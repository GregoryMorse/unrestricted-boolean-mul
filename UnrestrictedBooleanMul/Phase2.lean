import UnrestrictedBooleanMul.Phase2Certificate
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.ZMod
import Batteries.Data.BitVec.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace UnrestrictedBooleanMul

open Phase2Certificate

noncomputable section


@[simp] theorem anf_one_coeff {m : Nat} (s : Monomial m) :
    (1 : ANF m).coeff s = if s = 1 then 1 else 0 := by
  rw [MonoidAlgebra.one_def]
  change (Finsupp.single (1 : Monomial m) (1 : F₂)) s = if s = 1 then 1 else 0
  rw [Finsupp.single_apply]
  simp only [eq_comm]

theorem f2_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem prod_union_f2 {m : Nat} (x : Fin m → F₂) (s t : Finset (Fin m)) :
    (∏ i ∈ s ∪ t, x i) = (∏ i ∈ s, x i) * ∏ i ∈ t, x i := by
  have hz : ((∏ i ∈ s ∪ t, x i) = 0) ↔
      ((∏ i ∈ s, x i) * ∏ i ∈ t, x i) = 0 := by
    constructor
    · intro h
      rcases Finset.prod_eq_zero_iff.mp h with ⟨i, hi, hxi⟩
      rcases Finset.mem_union.mp hi with his | hit
      · rw [Finset.prod_eq_zero his hxi, zero_mul]
      · rw [Finset.prod_eq_zero hit hxi, mul_zero]
    · intro h
      rcases mul_eq_zero.mp h with hs | ht
      · rcases Finset.prod_eq_zero_iff.mp hs with ⟨i, hi, hxi⟩
        exact Finset.prod_eq_zero (Finset.mem_union_left t hi) hxi
      · rcases Finset.prod_eq_zero_iff.mp ht with ⟨i, hi, hxi⟩
        exact Finset.prod_eq_zero (Finset.mem_union_right s hi) hxi
  rcases f2_eq_zero_or_one (∏ i ∈ s ∪ t, x i) with h | h
  · rw [h, hz.mp h]
  · rcases f2_eq_zero_or_one ((∏ i ∈ s, x i) * ∏ i ∈ t, x i) with k | k
    · have bad : (1 : F₂) = 0 := h.symm.trans (hz.mpr k)
      exact (one_ne_zero bad).elim
    · rw [h, k]

def monomialEval {m : Nat} (x : Fin m → F₂) : Monomial m →* F₂ where
  toFun s := ∏ i ∈ s.vars, x i
  map_one' := by simp
  map_mul' s t := prod_union_f2 x s.vars t.vars

noncomputable def evalHom {m : Nat} (x : Fin m → F₂) : ANF m →ₐ[F₂] F₂ :=
  MonoidAlgebra.lift F₂ F₂ (Monomial m) (monomialEval x)

theorem eval_eq_evalHom {m : Nat} (p : ANF m) (x : Fin m → F₂) :
    eval p x = evalHom x p := by
  simp [eval, evalHom, monomialEval, MonoidAlgebra.lift_apply]

@[simp] theorem eval_zero' {m : Nat} (x : Fin m → F₂) : eval 0 x = 0 := by
  rw [eval_eq_evalHom]
  exact map_zero (evalHom x)

@[simp] theorem eval_one' {m : Nat} (x : Fin m → F₂) : eval 1 x = 1 := by
  rw [eval_eq_evalHom]
  exact map_one (evalHom x)

@[simp] theorem eval_add' {m : Nat} (p q : ANF m) (x : Fin m → F₂) :
    eval (p + q) x = eval p x + eval q x := by
  simp only [eval_eq_evalHom, map_add]

@[simp] theorem eval_mul' {m : Nat} (p q : ANF m) (x : Fin m → F₂) :
    eval (p * q) x = eval p x * eval q x := by
  simp only [eval_eq_evalHom, map_mul]

@[simp] theorem eval_smul' {m : Nat} (c : F₂) (p : ANF m) (x : Fin m → F₂) :
    eval (c • p) x = c * eval p x := by
  rw [eval_eq_evalHom, map_smul]
  rfl

def bitF2 (b : Bool) : F₂ := if b then 1 else 0
def f2Bit (x : F₂) : Bool := decide (x = 1)

@[simp] theorem f2Bit_zero : f2Bit 0 = false := by decide
@[simp] theorem f2Bit_one : f2Bit 1 = true := by decide

@[simp] theorem bitF2_f2Bit (x : F₂) : bitF2 (f2Bit x) = x := by
  fin_cases x <;> rfl

@[simp] theorem bitF2_xor (a b : Bool) : bitF2 (xor a b) = bitF2 a + bitF2 b := by
  cases a <;> cases b <;> decide

@[simp] theorem bitF2_and (a b : Bool) : bitF2 (a && b) = bitF2 a * bitF2 b := by
  cases a <;> cases b <;> decide

theorem bitF2_injective : Function.Injective bitF2 := by
  intro a b h
  cases a <;> cases b <;> simp [bitF2] at h ⊢

def coeffBits {n : Nat} (c : Fin n → F₂) : BitVec n :=
  BitVec.ofFnLE (fun i ↦ f2Bit (c i))

@[simp] theorem coeffBits_getLsb {n : Nat} (c : Fin n → F₂) (i : Fin n) :
    (coeffBits c).getLsb i = f2Bit (c i) := by
  simp [coeffBits]

def sel (b : Bool) (x : BitVec 64) : BitVec 64 := if b then x else 0

@[simp] theorem bitF2_sel_getLsb (c : F₂) (x : BitVec 64) (q : Fin 64) :
    bitF2 ((sel (f2Bit c) x).getLsb q) = c * bitF2 (x.getLsb q) := by
  cases h : f2Bit c
  · have hc : c = 0 := by rw [← bitF2_f2Bit c, h]; rfl
    simp [sel, hc, bitF2]
  · have hc : c = 1 := by rw [← bitF2_f2Bit c, h]; rfl
    simp [sel, hc]

@[simp] theorem bitF2_sel_getElem (c : F₂) (x : BitVec 64) (q : Fin 64) :
    bitF2 (sel (f2Bit c) x)[q] = c * bitF2 x[q] :=
  bitF2_sel_getLsb c x q

@[simp] theorem bitF2_sel_getElemNat (c : F₂) (x : BitVec 64) (i : Nat) (h : i < 64) :
    bitF2 (sel (f2Bit c) x)[i] = c * bitF2 x[i] :=
  bitF2_sel_getLsb c x ⟨i, h⟩

def v0 : BitVec 64 := 0xAAAAAAAAAAAAAAAA#64
def v1 : BitVec 64 := 0xCCCCCCCCCCCCCCCC#64
def v2 : BitVec 64 := 0xF0F0F0F0F0F0F0F0#64
def v3 : BitVec 64 := 0xFF00FF00FF00FF00#64
def v4 : BitVec 64 := 0xFFFF0000FFFF0000#64
def v5 : BitVec 64 := 0xFFFFFFFF00000000#64

@[simp] theorem bitF2_allOnes_getElem (q : Fin 64) :
    bitF2 (0xFFFFFFFFFFFFFFFF#64)[q] = 1 := by
  fin_cases q <;> decide

@[simp] theorem bitF2_allOnes_getElemNat (i : Nat) (h : i < 64) :
    bitF2 (0xFFFFFFFFFFFFFFFF#64)[i] = 1 :=
  bitF2_allOnes_getElem ⟨i, h⟩

def e0 := v0 &&& v3
def e1 := (v0 &&& v4) ^^^ (v1 &&& v3)
def e2 := (v0 &&& v5) ^^^ (v1 &&& v4) ^^^ (v2 &&& v3)
def e3 := (v1 &&& v5) ^^^ (v2 &&& v4)
def e4 := v2 &&& v5

def tableVar : Fin 6 → BitVec 64 := ![v0, v1, v2, v3, v4, v5]
def targetTable : Fin 5 → BitVec 64 := ![e0, e1, e2, e3, e4]

def assignment (q : Fin 64) : Fin 6 → F₂ :=
  fun i ↦ bitF2 ((tableVar i).getLsb q)

theorem eval_Mul_three (i : Fin 5) (q : Fin 64) :
    eval (UnrestrictedBooleanMul.Mul 3 i) (assignment q) =
      bitF2 ((targetTable i).getLsb q) := by
  fin_cases i <;>
    simp [UnrestrictedBooleanMul.Mul, mulCoefficient, aVar, bVar, assignment, tableVar, targetTable,
      e0, e1, e2, e3, e4, Fin.sum_univ_succ]

def targetSum : ANF 6 := ∑ i : Fin 5, UnrestrictedBooleanMul.Mul 3 i

def rationalBasis : Fin 10 → ANF 6 :=
  ![1, X 0, X 1, X 2, X 3, X 4, X 5,
    UnrestrictedBooleanMul.Mul 3 0, UnrestrictedBooleanMul.Mul 3 4, targetSum]

def ambientBasis : Fin 12 → ANF 6 :=
  ![1, X 0, X 1, X 2, X 3, X 4, X 5,
    UnrestrictedBooleanMul.Mul 3 0, UnrestrictedBooleanMul.Mul 3 1,
    UnrestrictedBooleanMul.Mul 3 2, UnrestrictedBooleanMul.Mul 3 3,
    UnrestrictedBooleanMul.Mul 3 4]

def rationalRep (c : Fin 10 → F₂) : ANF 6 := ∑ i, c i • rationalBasis i
def ambientRep (c : Fin 12 → F₂) : ANF 6 := ∑ i, c i • ambientBasis i

macro "solve_product_coeff" : tactic =>
  `(tactic|
    (simp [rationalRep, rationalBasis, targetSum, UnrestrictedBooleanMul.Mul,
      mulCoefficient, aVar, bVar, X, monomial_mul, Fin.sum_univ_succ,
      Phase2Certificate.c3, Phase2Certificate.c20, Phase2Certificate.c25,
      Phase2Certificate.c30, Phase2Certificate.c31, Phase2Certificate.c32,
      Phase2Certificate.c34, Phase2Certificate.g0, Phase2Certificate.g1,
      Phase2Certificate.ab]
     ring_nf
     simp +decide [monomial_mul, coeff_monomial]
     ring_nf
     all_goals simp only [Phase2Certificate.two_eq_zero_f2, mul_zero, add_zero, zero_add]))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_c3 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 1, 4}) = c3 a b := by
  solve_product_coeff

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_c20 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 4, 5}) = c20 a b := by
  solve_product_coeff

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_c25 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 1}) = c25 a b := by
  solve_product_coeff

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_c30 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {4, 5}) = c30 a b := by
  solve_product_coeff

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_c31 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 4}) +
      (rationalRep a * rationalRep b).coeff (Monomial.mk {1, 3}) = c31 a b := by
  solve_product_coeff

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_c32 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 5}) +
      (rationalRep a * rationalRep b).coeff (Monomial.mk {1, 4}) = c32 a b := by
  solve_product_coeff

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_c34 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {1, 5}) +
      (rationalRep a * rationalRep b).coeff (Monomial.mk {2, 4}) = c34 a b := by
  solve_product_coeff

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_g0 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 4}) +
      (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 5}) = g0 a b := by
  solve_product_coeff

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_g1 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 5}) +
      (rationalRep a * rationalRep b).coeff (Monomial.mk {1, 5}) = g1 a b := by
  solve_product_coeff

def rationalSpace : Submodule F₂ (ANF 6) :=
  Submodule.span F₂ (Set.range rationalBasis)

def ambientSpace : Submodule F₂ (ANF 6) :=
  Submodule.span F₂ (Set.range ambientBasis)

theorem mem_rationalSpace_iff {p : ANF 6} :
    p ∈ rationalSpace ↔ ∃ c : Fin 10 → F₂, rationalRep c = p := by
  simpa [rationalSpace, rationalRep] using
    (Submodule.mem_span_range_iff_exists_fun (R := F₂) (v := rationalBasis) (x := p))

theorem mem_ambientSpace_iff {p : ANF 6} :
    p ∈ ambientSpace ↔ ∃ c : Fin 12 → F₂, ambientRep c = p := by
  simpa [ambientSpace, ambientRep] using
    (Submodule.mem_span_range_iff_exists_fun (R := F₂) (v := ambientBasis) (x := p))

def ambientAnchor : Fin 12 → Monomial 6 :=
  ![⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{2}⟩, ⟨{3}⟩, ⟨{4}⟩, ⟨{5}⟩,
    ⟨{0, 3}⟩, ⟨{0, 4}⟩, ⟨{0, 5}⟩, ⟨{1, 5}⟩, ⟨{2, 5}⟩]

def ambientProjection : ANF 6 →ₗ[F₂] (Fin 12 → F₂) :=
  coefficientProjection ambientAnchor

set_option maxHeartbeats 1000000 in
theorem ambientProjection_basis (i : Fin 12) :
    ambientProjection (ambientBasis i) = (Pi.basisFun F₂ (Fin 12)) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [ambientProjection, coefficientProjection, ambientAnchor, ambientBasis,
      UnrestrictedBooleanMul.Mul, mulCoefficient, aVar, bVar, X, monomial_mul,
      Pi.basisFun, Fin.sum_univ_succ] <;> decide

@[simp] theorem ambientProjection_one :
    ambientProjection 1 = (Pi.basisFun F₂ (Fin 12)) 0 := by
  simpa [ambientBasis] using ambientProjection_basis 0

@[simp] theorem ambientProjection_X_zero :
    ambientProjection (X 0) = (Pi.basisFun F₂ (Fin 12)) 1 := by
  simpa [ambientBasis] using ambientProjection_basis 1

@[simp] theorem ambientProjection_X_one :
    ambientProjection (X 1) = (Pi.basisFun F₂ (Fin 12)) 2 := by
  simpa [ambientBasis] using ambientProjection_basis 2

@[simp] theorem ambientProjection_X_two :
    ambientProjection (X 2) = (Pi.basisFun F₂ (Fin 12)) 3 := by
  simpa [ambientBasis] using ambientProjection_basis 3

@[simp] theorem ambientProjection_X_three :
    ambientProjection (X 3) = (Pi.basisFun F₂ (Fin 12)) 4 := by
  simpa [ambientBasis] using ambientProjection_basis 4

@[simp] theorem ambientProjection_X_four :
    ambientProjection (X 4) = (Pi.basisFun F₂ (Fin 12)) 5 := by
  simpa [ambientBasis] using ambientProjection_basis 5

@[simp] theorem ambientProjection_X_five :
    ambientProjection (X 5) = (Pi.basisFun F₂ (Fin 12)) 6 := by
  simpa [ambientBasis] using ambientProjection_basis 6

@[simp] theorem ambientProjection_mul_zero :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 0) = (Pi.basisFun F₂ (Fin 12)) 7 := by
  simpa [ambientBasis] using ambientProjection_basis 7

@[simp] theorem ambientProjection_mul_one :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 1) = (Pi.basisFun F₂ (Fin 12)) 8 := by
  simpa [ambientBasis] using ambientProjection_basis 8

@[simp] theorem ambientProjection_mul_two :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 2) = (Pi.basisFun F₂ (Fin 12)) 9 := by
  simpa [ambientBasis] using ambientProjection_basis 9

@[simp] theorem ambientProjection_mul_three :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 3) = (Pi.basisFun F₂ (Fin 12)) 10 := by
  simpa [ambientBasis] using ambientProjection_basis 10

@[simp] theorem ambientProjection_mul_four :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 4) = (Pi.basisFun F₂ (Fin 12)) 11 := by
  simpa [ambientBasis] using ambientProjection_basis 11

theorem ambientBasis_linearIndependent : LinearIndependent F₂ ambientBasis := by
  apply LinearIndependent.of_comp ambientProjection
  have h : ambientProjection ∘ ambientBasis = (Pi.basisFun F₂ (Fin 12)) := by
    funext i
    exact ambientProjection_basis i
  rw [h]
  exact (Pi.basisFun F₂ (Fin 12)).linearIndependent

theorem ambientSpace_finrank : Module.finrank F₂ ambientSpace = 12 := by
  exact finrank_span_eq_card ambientBasis_linearIndependent

def freeBasis : Fin 7 → ANF 6 := ![1, X 0, X 1, X 2, X 3, X 4, X 5]

theorem affine_six_eq_span_freeBasis :
    affine 6 = Submodule.span F₂ (Set.range freeBasis) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p (rfl | ⟨i, rfl⟩)
    · apply Submodule.subset_span
      exact ⟨0, by simp [freeBasis]⟩
    · fin_cases i
      · apply Submodule.subset_span; exact ⟨1, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨2, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨3, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨4, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨5, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨6, by simp [freeBasis]⟩
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    fin_cases i
    · simpa [freeBasis] using one_mem_affine 6
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 0)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 1)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 2)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 3)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 4)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 5)

theorem affine_six_finrank_le : Module.finrank F₂ (affine 6) ≤ 7 := by
  rw [affine_six_eq_span_freeBasis]
  exact (finrank_span_le_card (Set.range freeBasis)).trans (by
    convert! Fintype.card_range_le freeBasis
    rw [Set.toFinset_card])

theorem rationalBasis_mem (i : Fin 10) : rationalBasis i ∈ rationalSpace :=
  Submodule.subset_span ⟨i, rfl⟩

theorem ambientBasis_mem (i : Fin 12) : ambientBasis i ∈ ambientSpace :=
  Submodule.subset_span ⟨i, rfl⟩

theorem affine_le_rationalSpace : affine 6 ≤ rationalSpace := by
  rw [affine_six_eq_span_freeBasis]
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  fin_cases i
  all_goals first | simpa [freeBasis, rationalBasis] using rationalBasis_mem 0 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 1 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 2 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 3 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 4 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 5 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 6

theorem ambientSpace_eq_mulAmbient : ambientSpace = mulAmbient 3 := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using one_mem_affine 6)
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 0))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 1))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 2))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 3))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 4))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 5))
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 0)
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 1)
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 2)
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 3)
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 4)
  · apply sup_le
    · rw [affine_six_eq_span_freeBasis]
      apply Submodule.span_le.mpr
      rintro p ⟨i, rfl⟩
      fin_cases i
      all_goals first | simpa [freeBasis, ambientBasis] using ambientBasis_mem 0 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 1 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 2 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 3 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 4 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 5 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 6
    · apply Submodule.span_le.mpr
      rintro p ⟨i, rfl⟩
      fin_cases i
      all_goals first | simpa [ambientBasis] using ambientBasis_mem 7 |
        simpa [ambientBasis] using ambientBasis_mem 8 |
        simpa [ambientBasis] using ambientBasis_mem 9 |
        simpa [ambientBasis] using ambientBasis_mem 10 |
        simpa [ambientBasis] using ambientBasis_mem 11

theorem targetSum_mem_ambientSpace : targetSum ∈ ambientSpace := by
  apply Submodule.sum_mem
  intro i _hi
  fin_cases i
  · simpa [ambientBasis] using ambientBasis_mem 7
  · simpa [ambientBasis] using ambientBasis_mem 8
  · simpa [ambientBasis] using ambientBasis_mem 9
  · simpa [ambientBasis] using ambientBasis_mem 10
  · simpa [ambientBasis] using ambientBasis_mem 11

theorem rationalSpace_le_ambientSpace : rationalSpace ≤ ambientSpace := by
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  fin_cases i
  all_goals first | simpa [rationalBasis, ambientBasis] using ambientBasis_mem 0 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 1 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 2 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 3 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 4 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 5 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 6 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 7 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 11 |
    simpa [rationalBasis] using targetSum_mem_ambientSpace

def truthR (x : BitVec 10) : BitVec 64 :=
  sel (x.getLsbD 0) (BitVec.allOnes 64) ^^^
  sel (x.getLsbD 1) v0 ^^^ sel (x.getLsbD 2) v1 ^^^
  sel (x.getLsbD 3) v2 ^^^ sel (x.getLsbD 4) v3 ^^^
  sel (x.getLsbD 5) v4 ^^^ sel (x.getLsbD 6) v5 ^^^
  sel (x.getLsbD 7) e0 ^^^ sel (x.getLsbD 8) e4 ^^^
  sel (x.getLsbD 9) (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4)

def truthW (x : BitVec 12) : BitVec 64 :=
  sel (x.getLsbD 0) (BitVec.allOnes 64) ^^^
  sel (x.getLsbD 1) v0 ^^^ sel (x.getLsbD 2) v1 ^^^
  sel (x.getLsbD 3) v2 ^^^ sel (x.getLsbD 4) v3 ^^^
  sel (x.getLsbD 5) v4 ^^^ sel (x.getLsbD 6) v5 ^^^
  sel (x.getLsbD 7) e0 ^^^ sel (x.getLsbD 8) e1 ^^^
  sel (x.getLsbD 9) e2 ^^^ sel (x.getLsbD 10) e3 ^^^
  sel (x.getLsbD 11) e4

theorem rationalRep_truth (c : Fin 10 → F₂) (q : Fin 64) :
    eval (rationalRep c) (assignment q) =
      bitF2 ((truthR (coeffBits c)).getLsb q) := by
  simp [rationalRep, rationalBasis, targetSum, truthR, eval_Mul_three,
    assignment, tableVar, targetTable, e0, e1, e2, e3, e4,
    Fin.sum_univ_succ, coeffBits]
  ring

theorem ambientRep_truth (c : Fin 12 → F₂) (q : Fin 64) :
    eval (ambientRep c) (assignment q) =
      bitF2 ((truthW (coeffBits c)).getLsb q) := by
  simp [ambientRep, ambientBasis, truthW, eval_Mul_three,
    assignment, tableVar, targetTable, e0, e1, e2, e3, e4,
    Fin.sum_univ_succ, coeffBits]

macro "solve_ambient_coeff" : tactic =>
  `(tactic|
    (simp +decide [ambientRep, ambientBasis, UnrestrictedBooleanMul.Mul,
      mulCoefficient, aVar, bVar, X, monomial_mul, coeff_monomial,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero]))

theorem algebraic_cert (a b : Fin 10 → F₂) (z : Fin 12 → F₂)
    (h : rationalRep a * rationalRep b = ambientRep z) :
    z 8 = z 9 ∧ z 9 = z 10 := by
  have h3 : c3 a b = 0 := by
    rw [← product_coeff_c3, h]
    solve_ambient_coeff
  have h20 : c20 a b = 0 := by
    rw [← product_coeff_c20, h]
    solve_ambient_coeff
  have h25 : c25 a b = 0 := by
    rw [← product_coeff_c25, h]
    solve_ambient_coeff
  have h30 : c30 a b = 0 := by
    rw [← product_coeff_c30, h]
    solve_ambient_coeff
  have h31 : c31 a b = 0 := by
    rw [← product_coeff_c31, h]
    solve_ambient_coeff
  have h32 : c32 a b = 0 := by
    rw [← product_coeff_c32, h]
    solve_ambient_coeff
  have h34 : c34 a b = 0 := by
    rw [← product_coeff_c34, h]
    solve_ambient_coeff
  have hg0 := Phase2Certificate.cert0 a b h3 h25 h31 h32
  have hg1 := Phase2Certificate.cert1 a b h20 h30 h32 h34
  rw [← product_coeff_g0, h] at hg0
  rw [← product_coeff_g1, h] at hg1
  have hz89 : z 8 + z 9 = 0 := by
    simpa +decide [ambientRep, ambientBasis, UnrestrictedBooleanMul.Mul,
      mulCoefficient, aVar, bVar, X, monomial_mul, coeff_monomial,
      Fin.sum_univ_succ] using hg0
  have hz910 : z 9 + z 10 = 0 := by
    simpa +decide [ambientRep, ambientBasis, UnrestrictedBooleanMul.Mul,
      mulCoefficient, aVar, bVar, X, monomial_mul, coeff_monomial,
      Fin.sum_univ_succ] using hg1
  constructor
  · rw [← CharTwo.sub_eq_add] at hz89
    exact sub_eq_zero.mp hz89
  · rw [← CharTwo.sub_eq_add] at hz910
    exact sub_eq_zero.mp hz910

def rationalOfAmbient (z : Fin 12 → F₂) : Fin 10 → F₂ :=
  ![z 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7 + z 8, z 11 + z 8, z 8]

theorem ambientRep_mem_rationalSpace (z : Fin 12 → F₂)
    (h₈₉ : z 8 = z 9) (h₉₁₀ : z 9 = z 10) : ambientRep z ∈ rationalSpace := by
  rw [mem_rationalSpace_iff]
  refine ⟨rationalOfAmbient z, ?_⟩
  simp [rationalOfAmbient, rationalRep, ambientRep, rationalBasis, ambientBasis,
    targetSum, Fin.sum_univ_succ]
  rw [← h₈₉, ← h₉₁₀, ← h₈₉]
  match_scalars <;> simp [add_assoc, CharTwo.add_self_eq_zero]

theorem rational_mul_mem_of_mem_ambient {f g : ANF 6}
    (hf : f ∈ rationalSpace) (hg : g ∈ rationalSpace)
    (hfg : f * g ∈ ambientSpace) : f * g ∈ rationalSpace := by
  rcases mem_rationalSpace_iff.mp hf with ⟨x, rfl⟩
  rcases mem_rationalSpace_iff.mp hg with ⟨y, rfl⟩
  rcases mem_ambientSpace_iff.mp hfg with ⟨z, hz⟩
  have hcoeff := algebraic_cert x y z hz.symm
  rw [← hz]
  exact ambientRep_mem_rationalSpace z hcoeff.1 hcoeff.2

theorem mul_three_one_not_mem_rationalSpace :
    UnrestrictedBooleanMul.Mul 3 1 ∉ rationalSpace := by
  intro h
  rcases mem_rationalSpace_iff.mp h with ⟨c, hc⟩
  have hp := congrArg ambientProjection hc
  have h₈ := congrFun hp 8
  have h₉ := congrFun hp 9
  simp [rationalRep, rationalBasis, targetSum, Fin.sum_univ_succ,
    Pi.basisFun] at h₈ h₉
  exact one_ne_zero (h₈.symm.trans h₉)

theorem finalWire_finrank_le_twelve (C : Circuit 6 5) :
    Module.finrank F₂ C.finalWire ≤ 12 := by
  rw [C.finalWire_eq]
  have hg : Module.finrank F₂ (Submodule.span F₂ (Set.range C.gate)) ≤ 5 := by
    exact (finrank_span_le_card (Set.range C.gate)).trans (by
      convert! Fintype.card_range_le C.gate
      rw [Set.toFinset_card])
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (affine 6) (Submodule.span F₂ (Set.range C.gate))
  have ha := affine_six_finrank_le
  omega

theorem ambientSpace_le_finalWire (C : Circuit 6 5)
    (computes : C.Computes (UnrestrictedBooleanMul.Mul 3)) :
    ambientSpace ≤ C.finalWire := by
  rw [ambientSpace_eq_mulAmbient]
  apply sup_le
  · simpa [Circuit.finalWire] using affine_le_wireSpace C.gate (j := 5)
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact computes i

theorem finalWire_eq_ambientSpace (C : Circuit 6 5)
    (computes : C.Computes (UnrestrictedBooleanMul.Mul 3)) :
    C.finalWire = ambientSpace := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (ambientSpace_le_finalWire C computes)
  rw [ambientSpace_finrank]
  exact finalWire_finrank_le_twelve C

theorem five_gate_impossible (C : Circuit 6 5) :
    ¬ C.Computes (UnrestrictedBooleanMul.Mul 3) := by
  intro computes
  have hfinal := finalWire_eq_ambientSpace C computes
  have gatesR : ∀ i : Fin 5, C.gate i ∈ rationalSpace := by
    intro i
    have all : ∀ k : Nat, ∀ hk : k < 5, C.gate ⟨k, hk⟩ ∈ rationalSpace := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk
          let j : Fin 5 := ⟨k, hk⟩
          have hw : wireSpace C.gate k ≤ rationalSpace := by
            apply sup_le affine_le_rationalSpace
            apply Submodule.span_le.mpr
            rintro p ⟨t, ht, rfl⟩
            exact ih t.val ht t.isLt
          have hl : C.left j ∈ rationalSpace := hw (by simpa [j] using C.left_mem j)
          have hr : C.right j ∈ rationalSpace := hw (by simpa [j] using C.right_mem j)
          have hg : C.left j * C.right j ∈ ambientSpace := by
            rw [← C.gate_eq j, ← hfinal]
            exact gate_mem_finalWire C j
          rw [C.gate_eq j]
          exact rational_mul_mem_of_mem_ambient hl hr hg
    exact all i.val i.isLt
  have hfinalR : C.finalWire ≤ rationalSpace := by
    rw [C.finalWire_eq]
    apply sup_le affine_le_rationalSpace
    apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact gatesR i
  exact mul_three_one_not_mem_rationalSpace (hfinalR (computes 1))

theorem mul_three_dimension_lower (r : Nat) (h : HasCircuit (Mul 3) r) : 5 ≤ r := by
  rcases h with ⟨⟨C, computes⟩⟩
  exact circuit_lower_bound_of_projection C (Mul 3) TargetCoordinates.threeProjection
    TargetCoordinates.threeProjection_kills_affine TargetCoordinates.threeProjection_Mul computes

theorem mul_three_lower (r : Nat) (h : HasCircuit (Mul 3) r) : 6 ≤ r := by
  have h₅ := mul_three_dimension_lower r h
  by_contra h₆
  have hr : r = 5 := by omega
  subst r
  rcases h with ⟨⟨C, computes⟩⟩
  exact five_gate_impossible C computes

theorem mc_mul_three : MC(Mul 3) = 6 :=
  mc_eq_of_lower_upper mul_three_upper mul_three_lower

end

end UnrestrictedBooleanMul
