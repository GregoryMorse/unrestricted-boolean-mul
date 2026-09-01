import UnrestrictedBooleanMul.N5.Target
import UnrestrictedBooleanMul.Quadratic
import Lean.Elab.Tactic.Omega

/-!
# Five-term quadratic quotient

This is the coordinate model used throughout the `n = 5` lower bound.  The
ambient space is the 45-dimensional space of squarefree quadratic
coefficients on the ten input variables.  The multiplication target embeds as
the nine-dimensional Hankel subspace, and the quadratic quotient is formed by
the standard `Submodule` quotient.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

abbrev LinearForm := Fin 10 → F₂
abbrev TwoForm := QuadraticForm 10
abbrev TargetCoeff := Fin 9 → F₂

/-- Coordinate of the `a_i` input in the ten-variable ambient space. -/
def aCoord (i : Fin 5) : Fin 10 := ⟨i.val, by omega⟩

/-- Coordinate of the `b_j` input in the ten-variable ambient space. -/
def bCoord (j : Fin 5) : Fin 10 := ⟨5 + j.val, by omega⟩

theorem aCoord_ne_bCoord (i j : Fin 5) : aCoord i ≠ bCoord j := by
  intro h
  have := congrArg Fin.val h
  simp [aCoord, bCoord] at this
  omega

theorem aCoord_injective : Function.Injective aCoord := by
  intro i j h
  apply Fin.ext
  simpa [aCoord] using congrArg Fin.val h

theorem bCoord_injective : Function.Injective bCoord := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [bCoord] at this
  omega

@[simp] theorem aCoord_inj (i j : Fin 5) : aCoord i = aCoord j ↔ i = j :=
  aCoord_injective.eq_iff

@[simp] theorem bCoord_inj (i j : Fin 5) : bCoord i = bCoord j ↔ i = j :=
  bCoord_injective.eq_iff

@[simp] theorem bCoord_ne_aCoord (i j : Fin 5) : bCoord i ≠ aCoord j :=
  Ne.symm (aCoord_ne_bCoord j i)

/-- Linear coordinate forms on the two input halves. -/
def aLinear (i : Fin 5) : LinearForm :=
  (Pi.basisFun F₂ (Fin 10)) (aCoord i)

def bLinear (j : Fin 5) : LinearForm :=
  (Pi.basisFun F₂ (Fin 10)) (bCoord j)

/-- The output coordinate containing the product `a_i b_j`. -/
def hankelIndex (i j : Fin 5) : Fin 9 :=
  ⟨i.val + j.val, by omega⟩

/-- The decomposable quadratic basis element `a_i ∧ b_j`. -/
def targetPairTwo (i j : Fin 5) : TwoForm :=
  squarefreeWedge (aLinear i) (bLinear j)

/-- The coefficient vector supported at one multiplication output. -/
def targetBasis (s : Fin 9) : TargetCoeff :=
  (Pi.basisFun F₂ (Fin 9)) s

/-- Interpret a coefficient word as an ANF in the multiplication target. -/
def targetANF (c : TargetCoeff) : ANF 10 :=
  ∑ s : Fin 9, c s • Mul 5 s

/-- Linear form of `targetANF`. -/
def targetANFLinear : TargetCoeff →ₗ[F₂] ANF 10 where
  toFun := targetANF
  map_add' c d := by
    simp [targetANF, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp [targetANF, Finset.smul_sum, smul_smul]

/-- Quadratic coefficient form of a target word. -/
def targetTwoLinear : TargetCoeff →ₗ[F₂] TwoForm :=
  (quadraticProjection 10).comp targetANFLinear

def targetTwo (c : TargetCoeff) : TwoForm := targetTwoLinear c

theorem aVar_five_eq_X_aCoord (i : Fin 5) : aVar 5 i = X (aCoord i) := by
  rfl

theorem bVar_five_eq_X_bCoord (j : Fin 5) : bVar 5 j = X (bCoord j) := by
  rfl

@[simp] theorem quadraticProjection_aVar_mul_bVar (i j : Fin 5) :
    quadraticProjection 10 (aVar 5 i * bVar 5 j) = targetPairTwo i j := by
  rw [aVar_five_eq_X_aCoord, bVar_five_eq_X_bCoord,
    quadraticProjection_X_mul_X']
  congr 1
  · ext k
    simp [aLinear, linearProjection_X, Pi.basisFun, Pi.single_apply]
  · ext k
    simp [bLinear, linearProjection_X, Pi.basisFun, Pi.single_apply]

theorem quadraticProjection_Mul (s : Fin 9) :
    quadraticProjection 10 (Mul 5 s) =
      ∑ i : Fin 5, ∑ j : Fin 5,
        if i.val + j.val = s.val then targetPairTwo i j else 0 := by
  simp only [Mul, mulCoefficient, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.val + j.val = s.val
  · simpa only [if_pos h] using quadraticProjection_aVar_mul_bVar i j
  · simpa only [if_neg h] using map_zero (quadraticProjection 10)

/-- Hankel expansion of the quadratic multiplication target. -/
theorem targetTwo_eq_double_sum (c : TargetCoeff) :
    targetTwo c = ∑ i : Fin 5, ∑ j : Fin 5,
      c (hankelIndex i j) • targetPairTwo i j := by
  classical
  calc
    targetTwo c = ∑ s : Fin 9,
        c s • quadraticProjection 10 (Mul 5 s) := by
      simp [targetTwo, targetTwoLinear, targetANFLinear, targetANF]
    _ = ∑ s : Fin 9, ∑ i : Fin 5, ∑ j : Fin 5,
        if i.val + j.val = s.val then c s • targetPairTwo i j else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [quadraticProjection_Mul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i.val + j.val = s.val <;> simp [h]
    _ = ∑ i : Fin 5, ∑ j : Fin 5, ∑ s : Fin 9,
        if i.val + j.val = s.val then c s • targetPairTwo i j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 5, ∑ j : Fin 5,
        c (hankelIndex i j) • targetPairTwo i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_eq_single (hankelIndex i j)]
      · simp [hankelIndex]
      · intro s hs
        have hne : i.val + j.val ≠ s.val := by
          intro h
          apply hs
          exact Fin.ext h.symm
        simp [hne]

@[simp] theorem targetPairTwo_cross (i j k l : Fin 5) :
    targetPairTwo i j
        (quadraticPair (aCoord k) (bCoord l) (aCoord_ne_bCoord k l)) =
      (if i = k ∧ j = l then 1 else 0) := by
  simp only [targetPairTwo, aLinear, bLinear, squarefreeWedge_pair,
    Pi.basisFun]
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simp_all

@[simp] theorem targetPairTwo_sameA (i j k l : Fin 5) (hkl : k ≠ l) :
    targetPairTwo i j (quadraticPair (aCoord k) (aCoord l)
      (fun h => hkl (aCoord_injective h))) = 0 := by
  simp [targetPairTwo, aLinear, bLinear, squarefreeWedge_pair,
    Pi.basisFun, bCoord_ne_aCoord]

@[simp] theorem targetPairTwo_sameB (i j k l : Fin 5) (hkl : k ≠ l) :
    targetPairTwo i j (quadraticPair (bCoord k) (bCoord l)
      (fun h => hkl (bCoord_injective h))) = 0 := by
  simp [targetPairTwo, aLinear, bLinear, squarefreeWedge_pair,
    Pi.basisFun]

/-- The target embedding is the `5 × 5` Hankel cross block. -/
@[simp] theorem targetTwo_cross (c : TargetCoeff) (i j : Fin 5) :
    targetTwo c
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)) =
      c (hankelIndex i j) := by
  rw [targetTwo_eq_double_sum]
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    targetPairTwo_cross, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp
    · intro l hlj
      simp [hlj]
  · intro k hki
    apply Finset.sum_eq_zero
    intro l _
    simp [hki]

@[simp] theorem targetTwo_sameA (c : TargetCoeff) (i j : Fin 5)
    (hij : i ≠ j) :
    targetTwo c (quadraticPair (aCoord i) (aCoord j)
      (fun h => hij (aCoord_injective h))) = 0 := by
  rw [targetTwo_eq_double_sum]
  simp

@[simp] theorem targetTwo_sameB (c : TargetCoeff) (i j : Fin 5)
    (hij : i ≠ j) :
    targetTwo c (quadraticPair (bCoord i) (bCoord j)
      (fun h => hij (bCoord_injective h))) = 0 := by
  rw [targetTwo_eq_double_sum]
  simp

/-- The nine target coordinates inside the 45-dimensional quadratic space. -/
def targetTwoSpace : Submodule F₂ TwoForm := LinearMap.range targetTwoLinear

/-- The quadratic quotient modulo the Hankel target. -/
abbrev QuadraticQuotient := TwoForm ⧸ targetTwoSpace

/-- Canonical projection to the quadratic quotient. -/
def quadraticQuotientProjection : TwoForm →ₗ[F₂] QuadraticQuotient :=
  Submodule.mkQ targetTwoSpace

/-- A quadratic form produced by one product of affine functions. -/
def IsDecomposableTwo (q : TwoForm) : Prop :=
  ∃ u v : LinearForm, q = squarefreeWedge u v

/-- Restriction to the nine private target anchors. -/
def anchorRestriction : TwoForm →ₗ[F₂] TargetCoeff where
  toFun q i := q ⟨(fiveTargetAnchor i).vars, fiveTargetAnchor_degree i⟩
  map_add' q r := by ext i; simp
  map_smul' a q := by ext i; simp

theorem anchorRestriction_quadraticProjection (p : ANF 10) :
    anchorRestriction (quadraticProjection 10 p) = fiveTargetProjection p := by
  rfl

/-- The private anchors form a left inverse to the target embedding. -/
theorem anchorRestriction_targetTwo (c : TargetCoeff) :
    anchorRestriction (targetTwo c) = c := by
  rw [targetTwo, targetTwoLinear, LinearMap.comp_apply,
    anchorRestriction_quadraticProjection]
  ext i
  classical
  simp [targetANFLinear, targetANF, fiveTargetProjection_Mul,
    Pi.basisFun, Pi.single_apply]

theorem targetTwo_injective : Function.Injective targetTwo := by
  intro c d h
  have := congrArg anchorRestriction h
  simpa [anchorRestriction_targetTwo] using this

theorem targetTwoLinear_injective : Function.Injective targetTwoLinear :=
  targetTwo_injective

/-- The squarefree quadratic ambient space has dimension `choose(10,2)=45`. -/
theorem twoForm_finrank : Module.finrank F₂ TwoForm = 45 := by
  rw [quadraticForm_finrank]
  norm_num [Nat.choose]

/-- The Hankel multiplication target has dimension nine. -/
theorem targetTwoSpace_finrank : Module.finrank F₂ targetTwoSpace = 9 := by
  have he := (LinearEquiv.ofInjective targetTwoLinear
    targetTwoLinear_injective).finrank_eq
  change Module.finrank F₂ targetTwoLinear.range = 9
  calc
    Module.finrank F₂ targetTwoLinear.range =
        Module.finrank F₂ TargetCoeff := he.symm
    _ = 9 := by simp [TargetCoeff]

/-- The quotient by the target has dimension 36. -/
theorem quadraticQuotient_finrank :
    Module.finrank F₂ QuadraticQuotient = 36 := by
  have h := targetTwoSpace.finrank_quotient_add_finrank
  rw [targetTwoSpace_finrank, twoForm_finrank] at h
  change Module.finrank F₂ (TwoForm ⧸ targetTwoSpace) = 36
  omega

/-- Every affine product has a decomposable quadratic projection. -/
theorem quadraticProjection_affineProduct {p q : ANF 10}
    (hp : p ∈ affine 10) (hq : q ∈ affine 10) :
    IsDecomposableTwo (quadraticProjection 10 (p * q)) := by
  rcases quadraticProjection_mul_of_affine hp hq with ⟨u, v, huv⟩
  exact ⟨u, v, huv⟩

end

end N5
end UnrestrictedBooleanMul
