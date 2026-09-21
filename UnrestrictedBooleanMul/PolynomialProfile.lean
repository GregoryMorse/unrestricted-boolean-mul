import UnrestrictedBooleanMul.BilinearRestriction
import UnrestrictedBooleanMul.BilinearCapacity
import Mathlib.Tactic.FinCases

/-! The output profile of every nonzero n=6 hyperplane restriction.
The algebraic minor argument follows N4.Hankel; it does not enumerate
circuits, factor families, quotient spaces, or hyperplane orbits. -/
namespace UnrestrictedBooleanMul.N6.Profile
noncomputable section
open Module Submodule

abbrev Coeff := Fin 11 → F₂
abbrev Normal := Fin 6 → F₂

def hankel (c : Coeff) (i j : Fin 6) : F₂ := c ⟨i.val + j.val, by omega⟩

def rankOne (c : Coeff) : Prop :=
  ∀ i k j l : Fin 6, hankel c i j * hankel c k l = hankel c i l * hankel c k j

/-- Zero, one, infinity, in that order. -/
def rationalNormal (k : Fin 3) : Normal := fun i =>
  if k = 0 then (if i = 0 then 1 else 0) else if k = 1 then 1 else if i = 5 then 1 else 0

def rationalCoeff (k : Fin 3) : Coeff := fun s =>
  if k = 0 then (if s = 0 then 1 else 0) else if k = 1 then 1 else if s = 10 then 1 else 0

private theorem square_f2 (x : F₂) : x * x = x := by
  rcases f2_eq_zero_or_one x with rfl | rfl <;> simp

/-- All zero minors force zero or a rational evaluation coefficient.
Only a fixed small list of minors is used, as in the n=4 proof. -/
theorem rankOne_classification {c : Coeff} (h : rankOne c) :
    c = 0 ∨ ∃ k : Fin 3, c = rationalCoeff k := by
  rcases f2_eq_zero_or_one (c 0) with hc0 | hc0
  · have hc1 : c 1 = 0 := by simpa [hankel, hc0, square_f2] using h 0 1 1 0
    have hc2 : c 2 = 0 := by simpa [hankel, hc0, square_f2] using h 0 2 2 0
    have hc3 : c 3 = 0 := by simpa [hankel, hc0, square_f2] using h 0 3 3 0
    have hc4 : c 4 = 0 := by simpa [hankel, hc0, square_f2] using h 0 4 4 0
    have hc5 : c 5 = 0 := by simpa [hankel, hc0, square_f2] using h 0 5 5 0
    have hc6 : c 6 = 0 := by simpa [hankel, hc2, square_f2] using h 1 5 5 1
    have hc7 : c 7 = 0 := by simpa [hankel, hc4, square_f2] using h 2 5 5 2
    have hc8 : c 8 = 0 := by simpa [hankel, hc6, square_f2] using h 3 5 5 3
    have hc9 : c 9 = 0 := by simpa [hankel, hc8, square_f2] using h 4 5 5 4
    rcases f2_eq_zero_or_one (c 10) with hc10 | hc10
    · left
      funext s
      fin_cases s <;> assumption
    · right
      refine ⟨2, ?_⟩
      funext s
      fin_cases s <;> simp [rationalCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10]
  · have hc2 : c 2 = c 1 := by simpa [hankel, hc0, square_f2] using h 0 1 0 1
    have hc3 : c 3 = c 1 := by simpa [hankel, hc0, hc2, square_f2] using h 0 1 0 2
    have hc4 : c 4 = c 1 := by simpa [hankel, hc0, hc2, square_f2] using h 0 2 0 2
    have hc5 : c 5 = c 1 := by simpa [hankel, hc0, hc2, hc3, square_f2] using h 0 2 0 3
    have hc6 : c 6 = c 1 := by simpa [hankel, hc0, hc3, square_f2] using h 0 3 0 3
    have hc7 : c 7 = c 1 := by simpa [hankel, hc0, hc3, hc4, square_f2] using h 0 3 0 4
    have hc8 : c 8 = c 1 := by simpa [hankel, hc0, hc4, square_f2] using h 0 4 0 4
    have hc9 : c 9 = c 1 := by simpa [hankel, hc0, hc4, hc5, square_f2] using h 0 4 0 5
    have hc10 : c 10 = c 1 := by simpa [hankel, hc0, hc5, square_f2] using h 0 5 0 5
    rcases f2_eq_zero_or_one (c 1) with hc1 | hc1
    · right
      refine ⟨0, ?_⟩
      funext s
      fin_cases s <;> simp [rationalCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10]
    · right
      refine ⟨1, ?_⟩
      funext s
      fin_cases s <;> simp [rationalCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10]

theorem rational_outer (k : Fin 3) (i j : Fin 6) :
    hankel (rationalCoeff k) i j = rationalNormal k i * rationalNormal k j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> decide

theorem rationalCoeff_ne_zero (k : Fin 3) : rationalCoeff k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h10 := congrFun h 10
  fin_cases k <;> simp [rationalCoeff] at h0 h10

theorem rationalNormal_injective : Function.Injective rationalNormal := by
  intro k l h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases k <;> fin_cases l <;> first | rfl | simp [rationalNormal] at h0 h1

def restrictedTensor (h : Normal) (p : Fin 6) : BilinearTensor 5 6 11 :=
  (polynomialTensor 6 6).restrictLeft (leftHyperplaneMatrix h p)

def coefficientMap (h : Normal) (p : Fin 6) : Coeff →ₗ[F₂] (Fin 5 → Fin 6 → F₂) :=
  Capacity.coefficientSum (restrictedTensor h p)

theorem coefficientMap_apply (h : Normal) (p : Fin 6) (c : Coeff) (u : Fin 5) (j : Fin 6) :
    coefficientMap h p c u j = hankel c (p.succAbove u) j +
      h (p.succAbove u) * hankel c p j := by
  have hc : ∀ i : Fin 6, (∑ s : Fin 11, c s * polynomialTensor 6 6 s i j) = hankel c i j := by
    intro i
    have heq : ∀ s : Fin 11, (i.val + j.val = s.val) ↔ (⟨i.val + j.val, by omega⟩ : Fin 11) = s :=
      fun s => ⟨fun hs => Fin.ext hs, fun hs => congrArg Fin.val hs⟩
    simp [polynomialTensor, heq, hankel]
  change (∑ s : Fin 11, c s • restrictedTensor h p s) u j = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, restrictedTensor,
    BilinearTensor.restrictLeft, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hi : ∀ i : Fin 6,
      (∑ s : Fin 11, c s * (leftHyperplaneMatrix h p i u * polynomialTensor 6 6 s i j)) =
        leftHyperplaneMatrix h p i u * hankel c i j := by
    intro i
    simp_rw [mul_left_comm (c _)]
    rw [← Finset.mul_sum, hc]
  simp_rw [hi]
  rw [Fin.sum_univ_succAbove _ p]
  simp [leftHyperplaneMatrix, add_comm]

/-- A vanishing output combination has the prescribed normal as its left factor. -/
theorem coefficientMap_zero_factor (h : Normal) (p : Fin 6) (hp : h p = 1)
    (c : Coeff) (hc : coefficientMap h p c = 0) (i j : Fin 6) :
    hankel c i j = h i * hankel c p j := by
  rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨u, rfl⟩
  · simp [hp]
  · have heq := congrFun (congrFun hc u) j
    rw [coefficientMap_apply] at heq
    exact CharTwo.add_eq_zero.mp heq

theorem coefficientMap_zero_iff (h : Normal) (p : Fin 6) (hp : h p = 1) (c : Coeff) :
    coefficientMap h p c = 0 ↔ c = 0 ∨ ∃ k : Fin 3, h = rationalNormal k ∧ c = rationalCoeff k := by
  constructor
  · intro hc
    have hf := coefficientMap_zero_factor h p hp c hc
    have hr : rankOne c := by
      intro i k j l
      rw [hf i j, hf k l, hf i l, hf k j]
      ac_rfl
    rcases rankOne_classification hr with hz | ⟨k, hk⟩
    · exact Or.inl hz
    · right
      refine ⟨k, ?_, hk⟩
      let s : Fin 6 := if k = 2 then 5 else 0
      have hs : rationalNormal k s = 1 := by
        fin_cases k <;> decide
      have hrp : rationalNormal k p = 1 := by
        rcases f2_eq_zero_or_one (rationalNormal k p) with hz | ho
        · have he := hf s s
          simp [hk, rational_outer, hs, hz] at he
        · exact ho
      funext i
      have he := hf i s
      simpa [hk, rational_outer, hs, hrp] using he.symm
  · rintro (rfl | ⟨k, rfl, rfl⟩)
    · exact map_zero _
    · ext u j
      simp [coefficientMap_apply, rational_outer, hp, CharTwo.add_self_eq_zero]

theorem rational_kernel (k : Fin 3) (p : Fin 6) (hp : rationalNormal k p = 1) :
    LinearMap.ker (coefficientMap (rationalNormal k) p) = F₂ ∙ rationalCoeff k := by
  apply le_antisymm
  · intro c hc
    rcases (coefficientMap_zero_iff _ p hp c).mp hc with rfl | ⟨l, hl, rfl⟩
    · exact Submodule.zero_mem _
    · have hkl := rationalNormal_injective hl
      subst l
      exact Submodule.subset_span (Set.mem_singleton _)
  · apply Submodule.span_le.mpr
    intro c hc
    have heq : c = rationalCoeff k := hc
    exact (coefficientMap_zero_iff _ p hp c).mpr (Or.inr ⟨k, rfl, heq⟩)

theorem nonrational_kernel (h : Normal) (p : Fin 6) (hp : h p = 1)
    (hn : ¬ ∃ k : Fin 3, h = rationalNormal k) : LinearMap.ker (coefficientMap h p) = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  rcases (coefficientMap_zero_iff h p hp c).mp hc with hz | ⟨k, hk, _⟩
  · exact hz
  · exact (hn ⟨k, hk⟩).elim

theorem coefficientMap_range (h : Normal) (p : Fin 6) :
    LinearMap.range (coefficientMap h p) = (restrictedTensor h p).targetSpace :=
  Capacity.coefficientSum_range _

/-- The manuscript output-profile lemma: every nonzero hyperplane has the asserted output dimension,
independently of pivot choice. This is not a tensor-rank lower bound. -/
theorem output_profile (h : Normal) (p : Fin 6) (hp : h p = 1) :
    finrank F₂ (restrictedTensor h p).targetSpace =
      if ∃ k : Fin 3, h = rationalNormal k then 10 else 11 := by
  classical
  have hr := (coefficientMap h p).finrank_range_add_finrank_ker
  rw [coefficientMap_range] at hr
  have hd : finrank F₂ Coeff = 11 := by simp [Coeff]
  rw [hd] at hr
  by_cases he : ∃ k : Fin 3, h = rationalNormal k
  · rw [if_pos he]
    obtain ⟨k, rfl⟩ := he
    rw [rational_kernel k p hp, finrank_span_singleton (rationalCoeff_ne_zero k)] at hr
    omega
  · rw [if_neg he]
    rw [nonrational_kernel h p hp he, finrank_bot] at hr
    omega

/-- Exact sector sizes needed to exclude fifteen products: five quotient
dimensions at a rational endpoint, four for every other normal. -/
theorem rank15_capacity_iff (h : Normal) (p : Fin 6) (hp : h p = 1) :
    bilinearRank (restrictedTensor h p) ≤ 15 ↔
    ∃ Q : Submodule F₂ ((Fin 5 → Fin 6 → F₂) ⧸ (restrictedTensor h p).targetSpace),
      finrank F₂ Q ≤ (if ∃ k : Fin 3, h = rationalNormal k then 5 else 4) ∧
        Capacity.value (restrictedTensor h p).targetSpace (bilinearRankOne 5 6 \ {0}) Q =
          (if ∃ k : Fin 3, h = rationalNormal k then 10 else 11) := by
  classical
  have hc := bilinearRank_capacity_criterion_nonzero (restrictedTensor h p)
    (if ∃ k : Fin 3, h = rationalNormal k then 5 else 4)
  have hd : finrank F₂ (restrictedTensor h p).targetSpace +
      (if ∃ k : Fin 3, h = rationalNormal k then 5 else 4) = 15 := by
    rw [output_profile h p hp]
    split <;> decide
  rw [hd] at hc
  simpa only [output_profile h p hp] using hc

#check rankOne_classification
#check rational_outer
#check rationalCoeff_ne_zero
#check rationalNormal_injective
#check coefficientMap_apply
#check coefficientMap_zero_factor
#check coefficientMap_zero_iff
#check rational_kernel
#check nonrational_kernel
#check coefficientMap_range
#check output_profile
#check rank15_capacity_iff
#print axioms rankOne_classification
#print axioms rational_outer
#print axioms rationalCoeff_ne_zero
#print axioms rationalNormal_injective
#print axioms coefficientMap_apply
#print axioms coefficientMap_zero_factor
#print axioms coefficientMap_zero_iff
#print axioms rational_kernel
#print axioms nonrational_kernel
#print axioms coefficientMap_range
#print axioms output_profile
#print axioms rank15_capacity_iff
end
end UnrestrictedBooleanMul.N6.Profile
