import UnrestrictedBooleanMul.N3Certificate
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace UnrestrictedBooleanMul

open N3Certificate

noncomputable section

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
      N3Certificate.c3, N3Certificate.c20, N3Certificate.c25,
      N3Certificate.c30, N3Certificate.c31, N3Certificate.c32,
      N3Certificate.c34, N3Certificate.g0, N3Certificate.g1,
      N3Certificate.ab]
     ring_nf
     simp +decide [monomial_mul, coeff_monomial]
     ring_nf
     all_goals simp only [N3Certificate.two_eq_zero_f2, mul_zero, add_zero, zero_add]))

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
  have hg0 := N3Certificate.cert0 a b h3 h25 h31 h32
  have hg1 := N3Certificate.cert1 a b h20 h30 h32 h34
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
