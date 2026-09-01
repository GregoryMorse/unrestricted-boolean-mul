import UnrestrictedBooleanMul.N5.TwoPlaceProfile

/-!
# Capacity of a defect line

This module proves the upper-bound half of manuscript Theorem 7.1 directly
from the exact capacity formula.  A two-dimensional defect has at most one
relation among its populated points.  If its represented-place weight reaches
three, it necessarily contains two distinct place types, and strong
mixed-place exclusion kills that last relation.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- In defect dimension at most two, the represented closed-place weight is
at most three.  Weight four would contain a degree-two place and two rational
places, whose three chosen effective points are linearly independent. -/
theorem representedPlaceWeight_le_three_of_finrank_le_two
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 2) :
    representedPlaceWeight Q ≤ 3 := by
  classical
  by_contra hbound
  have hweight : 4 ≤ representedPlaceWeight Q := by omega
  by_cases h0 : IsRepresentedPlace Q 0 <;>
    by_cases h1 : IsRepresentedPlace Q 1 <;>
      by_cases h2 : IsRepresentedPlace Q 2 <;>
        by_cases h3 : IsRepresentedPlace Q 3
  all_goals
    simp [representedPlaceWeight, representedRationalPlaceCount,
      representedDegreeTwoIndicator, h0, h1, h2, h3] at hweight
  all_goals
    first
    | exact not_three_distinct_represented_places_of_finrank_le_two
        Q hQ 0 1 3 h0 h1 h3 (by decide) (by decide) (by decide)
    | exact not_three_distinct_represented_places_of_finrank_le_two
        Q hQ 0 2 3 h0 h2 h3 (by decide) (by decide) (by decide)
    | exact not_three_distinct_represented_places_of_finrank_le_two
        Q hQ 1 2 3 h1 h2 h3 (by decide) (by decide) (by decide)

/-- Weight at least three guarantees two distinct represented place types.
This is only a four-boolean bookkeeping lemma; it does not enumerate quotient
points or decomposable forms. -/
theorem exists_two_distinct_represented_places_of_weight_ge_three
    (Q : Submodule F₂ QuadraticQuotient)
    (hweight : 3 ≤ representedPlaceWeight Q) :
    ∃ i j : Fin 4,
      IsRepresentedPlace Q i ∧ IsRepresentedPlace Q j ∧ i ≠ j := by
  classical
  by_cases h0 : IsRepresentedPlace Q 0 <;>
    by_cases h1 : IsRepresentedPlace Q 1 <;>
      by_cases h2 : IsRepresentedPlace Q 2 <;>
        by_cases h3 : IsRepresentedPlace Q 3
  all_goals
    simp [representedPlaceWeight, representedRationalPlaceCount,
      representedDegreeTwoIndicator, h0, h1, h2, h3] at hweight
  all_goals
    first
    | exact ⟨0, 3, h0, h3, by decide⟩
    | exact ⟨1, 3, h1, h3, by decide⟩
    | exact ⟨2, 3, h2, h3, by decide⟩
    | exact ⟨0, 1, h0, h1, by decide⟩

/-- A defect line has at most one relation gift before using any represented-
place information. -/
theorem relationGiftRank_le_one_of_finrank_le_two
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 2) :
    relationGiftRank Q ≤ 1 :=
  (relationGiftRank_le_relationKernel Q).trans
    (populatedRelationKernel_finrank_le_one_of_finrank_le_two Q hQ)

/-- Manuscript Theorem 7.1, upper-bound half: every quadratic defect of
dimension at most two has target capacity at most six. -/
theorem targetCapacity_le_six_of_finrank_le_two
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 2) :
    targetCapacity Q ≤ 6 := by
  rw [targetCapacity_eq_three_add_representedPlaceWeight_add_gifts]
  have hweight := representedPlaceWeight_le_three_of_finrank_le_two Q hQ
  by_cases hsmall : representedPlaceWeight Q ≤ 2
  · have hgift := relationGiftRank_le_one_of_finrank_le_two Q hQ
    omega
  · have hthree : 3 ≤ representedPlaceWeight Q := by omega
    rcases exists_two_distinct_represented_places_of_weight_ge_three
      Q hthree with ⟨i, j, hi, hj, hij⟩
    have hgift :=
      relationGiftRank_eq_zero_of_two_distinct_places_finrank_le_two
        Q hQ i j hi hj hij
    omega

/-! ## An algebraic equality witness -/

/-- A small effective parameter used at the rational place zero. -/
def defectTwoRationalParam : LocalKleinParam := ![0, 0, 1, 0]

theorem defectTwoRationalParam_effective :
    RationalLocalEffective defectTwoRationalParam := by
  simp [defectTwoRationalParam, RationalLocalEffective]

/-- The same four-bit word is effective in the degree-two local chart. -/
def defectTwoDegreeTwoParam : LocalKleinParam := ![0, 0, 1, 0]

theorem defectTwoDegreeTwoParam_effective :
    DegreeTwoLocalEffective defectTwoDegreeTwoParam := by
  simp only [defectTwoDegreeTwoParam, DegreeTwoLocalEffective,
    Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul]
  decide

def defectTwoRationalEffectiveParam : EffectiveParamAt 0 :=
  ⟨defectTwoRationalParam, by
    exact (mem_effectiveParamsAt_rational 0 (by decide)
      defectTwoRationalParam).2 defectTwoRationalParam_effective⟩

def defectTwoDegreeTwoEffectiveParam : EffectiveParamAt 3 :=
  ⟨defectTwoDegreeTwoParam, by
    exact (mem_effectiveParamsAt_degreeTwo defectTwoDegreeTwoParam).2
      defectTwoDegreeTwoParam_effective⟩

/-- The rational and degree-two effective quotient points generating the
sharp defect-line example. -/
def defectTwoCapacityBasis : Fin 2 → QuadraticQuotient :=
  ![closedPlaceQuotientPoint 0 defectTwoRationalEffectiveParam.1,
    closedPlaceQuotientPoint 3 defectTwoDegreeTwoEffectiveParam.1]

/-- A concrete defect line with local profile `J₀ ⊕ Dₓ`. -/
def defectTwoCapacitySpace : Submodule F₂ QuadraticQuotient :=
  Submodule.span F₂ (Set.range defectTwoCapacityBasis)

theorem defectTwoCapacitySpace_finrank_le_two :
    Module.finrank F₂ defectTwoCapacitySpace ≤ 2 := by
  letI : Fintype (Set.range defectTwoCapacityBasis) := Fintype.ofFinite _
  exact (finrank_span_le_card (Set.range defectTwoCapacityBasis)).trans (by
    convert! Fintype.card_range_le defectTwoCapacityBasis
    rw [Set.toFinset_card])

theorem defectTwoCapacitySpace_represents_rational :
    IsRepresentedPlace defectTwoCapacitySpace 0 := by
  refine ⟨defectTwoRationalEffectiveParam, ?_⟩
  exact Submodule.subset_span ⟨0, rfl⟩

theorem defectTwoCapacitySpace_represents_degreeTwo :
    IsRepresentedPlace defectTwoCapacitySpace 3 := by
  refine ⟨defectTwoDegreeTwoEffectiveParam, ?_⟩
  exact Submodule.subset_span ⟨1, rfl⟩

/-- The witness has exactly the intended represented-place weight three; a
third represented type would contradict its two-dimensionality. -/
theorem defectTwoCapacitySpace_representedPlaceWeight :
    representedPlaceWeight defectTwoCapacitySpace = 3 := by
  classical
  have h0 := defectTwoCapacitySpace_represents_rational
  have h3 := defectTwoCapacitySpace_represents_degreeTwo
  have h1 : ¬ IsRepresentedPlace defectTwoCapacitySpace 1 := by
    intro h1
    exact not_three_distinct_represented_places_of_finrank_le_two
      defectTwoCapacitySpace defectTwoCapacitySpace_finrank_le_two
      0 1 3 h0 h1 h3 (by decide) (by decide) (by decide)
  have h2 : ¬ IsRepresentedPlace defectTwoCapacitySpace 2 := by
    intro h2
    exact not_three_distinct_represented_places_of_finrank_le_two
      defectTwoCapacitySpace defectTwoCapacitySpace_finrank_le_two
      0 2 3 h0 h2 h3 (by decide) (by decide) (by decide)
  simp [representedPlaceWeight, representedRationalPlaceCount,
    representedDegreeTwoIndicator, h0, h1, h2, h3]

/-- The explicit rational-plus-degree-two defect line attains capacity six. -/
theorem defectTwoCapacitySpace_targetCapacity :
    targetCapacity defectTwoCapacitySpace = 6 := by
  rw [targetCapacity_eq_three_add_representedPlaceWeight_add_gifts,
    defectTwoCapacitySpace_representedPlaceWeight]
  have hgift :=
    relationGiftRank_eq_zero_of_two_distinct_places_finrank_le_two
      defectTwoCapacitySpace defectTwoCapacitySpace_finrank_le_two
      0 3 defectTwoCapacitySpace_represents_rational
      defectTwoCapacitySpace_represents_degreeTwo (by decide)
  omega

/-- Manuscript Theorem 7.1, equality witness: capacity six is attained by a
defect of dimension at most two. -/
theorem exists_finrank_le_two_targetCapacity_eq_six :
    ∃ Q : Submodule F₂ QuadraticQuotient,
      Module.finrank F₂ Q ≤ 2 ∧ targetCapacity Q = 6 :=
  ⟨defectTwoCapacitySpace, defectTwoCapacitySpace_finrank_le_two,
    defectTwoCapacitySpace_targetCapacity⟩

end

end N5
end UnrestrictedBooleanMul
