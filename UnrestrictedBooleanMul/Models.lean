import UnrestrictedBooleanMul.Circuit
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Unrestricted, quadratic and bilinear models

Quadratic formulas multiply affine forms in the original inputs. Bilinear
formulas have disjoint left/right input blocks, homogeneous linear factors,
and a tensor-coefficient correctness condition. The conversion to the existing
Boolean ANF circuit model is proved, not built into that correctness condition.
All finite bilinear tensors have a schoolbook formula, so the comparison of
the three natural-number minima has no representability hypothesis.
-/

namespace UnrestrictedBooleanMul

noncomputable section

structure QuadraticFormula {m o : Nat} (target : Fin o → ANF m) (r : Nat) where
  left : Fin r → ANF m
  right : Fin r → ANF m
  left_affine : ∀ k, left k ∈ affine m
  right_affine : ∀ k, right k ∈ affine m
  computes : (Circuit.ofAffineProducts left right left_affine right_affine).Computes target

def QuadraticFormula.toCircuit {m o r : Nat} {target : Fin o → ANF m}
    (F : QuadraticFormula target r) : Circuit m r :=
  Circuit.ofAffineProducts F.left F.right F.left_affine F.right_affine

theorem QuadraticFormula.hasCircuit {m o r : Nat} {target : Fin o → ANF m}
    (F : QuadraticFormula target r) : HasCircuit target r :=
  ⟨⟨F.toCircuit, F.computes⟩⟩

def HasQuadraticFormula {m o : Nat} (target : Fin o → ANF m) (r : Nat) : Prop :=
  Nonempty (QuadraticFormula target r)

/-- Zero in the unrepresentable case, as for the existing `MC` definition.
Comparison theorems below explicitly establish representability first. -/
def quadraticComplexity {m o : Nat} (target : Fin o → ANF m) : Nat := by
  classical
  exact if h : ∃ r, HasQuadraticFormula target r then Nat.find h else 0

theorem mc_le_quadraticComplexity {m o : Nat} {target : Fin o → ANF m}
    (h : ∃ r, HasQuadraticFormula target r) :
    MC(target) ≤ quadraticComplexity target := by
  classical
  obtain ⟨F⟩ := Nat.find_spec h
  have hc : ∃ r, HasCircuit target r := ⟨Nat.find h, F.hasCircuit⟩
  rw [multiplicativeComplexity, dif_pos hc, quadraticComplexity, dif_pos h]
  exact Nat.find_min' hc F.hasCircuit

abbrev BilinearTensor (a b o : Nat) := Fin o → Fin a → Fin b → F₂

def tensorLeftVar (a b : Nat) (i : Fin a) : ANF (a + b) := X (Fin.castAdd b i)
def tensorRightVar (a b : Nat) (j : Fin b) : ANF (a + b) := X (Fin.natAdd a j)

def BilinearTensor.realize {a b o : Nat} (T : BilinearTensor a b o) :
    Fin o → ANF (a + b) :=
  fun s => ∑ i, ∑ j, T s i j • (tensorLeftVar a b i * tensorRightVar a b j)

structure BilinearFormula {a b o : Nat} (T : BilinearTensor a b o) (r : Nat) where
  left : Fin r → Fin a → F₂
  right : Fin r → Fin b → F₂
  output : Fin o → Fin r → F₂
  correct : ∀ s i j, T s i j = ∑ k, output s k * left k i * right k j

def BilinearFormula.leftANF {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (k : Fin r) : ANF (a + b) :=
  ∑ i, F.left k i • tensorLeftVar a b i

def BilinearFormula.rightANF {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (k : Fin r) : ANF (a + b) :=
  ∑ j, F.right k j • tensorRightVar a b j

theorem BilinearFormula.leftANF_affine {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (k : Fin r) : F.leftANF k ∈ affine (a + b) := by
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (X_mem_affine _)

theorem BilinearFormula.rightANF_affine {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (k : Fin r) : F.rightANF k ∈ affine (a + b) := by
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (X_mem_affine _)

theorem BilinearFormula.recombine {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (s : Fin o) :
    T.realize s = ∑ k, F.output s k • (F.leftANF k * F.rightANF k) := by
  simp only [BilinearTensor.realize, F.correct, Finset.sum_smul,
    leftANF, rightANF, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, mul_comm (F.left k i)]

def BilinearFormula.toQuadratic {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) : QuadraticFormula T.realize r where
  left := F.leftANF
  right := F.rightANF
  left_affine := F.leftANF_affine
  right_affine := F.rightANF_affine
  computes s := by
    rw [F.recombine s]
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (gate_mem_finalWire
      (Circuit.ofAffineProducts F.leftANF F.rightANF F.leftANF_affine F.rightANF_affine) k)

def HasBilinearFormula {a b o : Nat} (T : BilinearTensor a b o) (r : Nat) : Prop :=
  Nonempty (BilinearFormula T r)

/-- The ordinary schoolbook tensor decomposition, including empty input blocks. -/
def BilinearTensor.schoolbook {a b o : Nat} (T : BilinearTensor a b o) :
    BilinearFormula T (a * b) where
  left k i := if i = (finProdFinEquiv.symm k).1 then 1 else 0
  right k j := if j = (finProdFinEquiv.symm k).2 then 1 else 0
  output s k := T s (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  correct s i j := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [Fintype.sum_prod_type, mul_ite]

theorem BilinearTensor.hasFormula {a b o : Nat} (T : BilinearTensor a b o) :
    ∃ r, HasBilinearFormula T r := ⟨a * b, ⟨T.schoolbook⟩⟩

def bilinearRank {a b o : Nat} (T : BilinearTensor a b o) : Nat := by
  classical
  exact Nat.find T.hasFormula

theorem bilinearRank_le {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) : bilinearRank T ≤ r := by
  classical
  exact Nat.find_min' T.hasFormula ⟨F⟩

theorem quadraticComplexity_le_bilinearRank {a b o : Nat} (T : BilinearTensor a b o) :
    quadraticComplexity T.realize ≤ bilinearRank T := by
  classical
  obtain ⟨F⟩ := Nat.find_spec T.hasFormula
  have hq : ∃ r, HasQuadraticFormula T.realize r :=
    ⟨bilinearRank T, ⟨F.toQuadratic⟩⟩
  rw [quadraticComplexity, dif_pos hq]
  exact Nat.find_min' hq ⟨F.toQuadratic⟩

/-- Model separation for every finite binary bilinear tensor, without a
circuit-existence premise or any assumption about nonlinear feedback. -/
theorem model_complexity_chain {a b o : Nat} (T : BilinearTensor a b o) :
    MC(T.realize) ≤ quadraticComplexity T.realize ∧
      quadraticComplexity T.realize ≤ bilinearRank T := by
  exact ⟨mc_le_quadraticComplexity
    ⟨a * b, ⟨T.schoolbook.toQuadratic⟩⟩, quadraticComplexity_le_bilinearRank T⟩

/-- Coefficient tensor of rectangular polynomial multiplication. -/
def polynomialTensor (a b : Nat) : BilinearTensor a b (a + b - 1) :=
  fun s i j => if i.val + j.val = s.val then 1 else 0

end
end UnrestrictedBooleanMul
