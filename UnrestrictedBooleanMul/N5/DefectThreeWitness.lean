import UnrestrictedBooleanMul.N5.DefectTwoCapacity
import UnrestrictedBooleanMul.N5.TwoRationalDegreeTwoProfile

/-!
# A sharp three-dimensional capacity witness

The span of effective points at `2P₀`, `2P₁`, and `Pₓ` is the local
equality mechanism in manuscript Theorem 7.2.  The three points are kept as
an explicit algebraic family; no quotient-point enumeration is used.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def defectThreeRationalOneEffectiveParam : EffectiveParamAt 1 :=
  ⟨defectTwoRationalParam, by
    exact (mem_effectiveParamsAt_rational 1 (by decide)
      defectTwoRationalParam).2 defectTwoRationalParam_effective⟩

def defectThreeCapacityBasis : Fin 3 → QuadraticQuotient :=
  ![closedPlaceQuotientPoint 0 defectTwoRationalEffectiveParam.1,
    closedPlaceQuotientPoint 1 defectThreeRationalOneEffectiveParam.1,
    closedPlaceQuotientPoint 3 defectTwoDegreeTwoEffectiveParam.1]

def defectThreeCapacitySpace : Submodule F₂ QuadraticQuotient :=
  Submodule.span F₂ (Set.range defectThreeCapacityBasis)

theorem defectThreeCapacitySpace_finrank_le_three :
    Module.finrank F₂ defectThreeCapacitySpace ≤ 3 := by
  letI : Fintype (Set.range defectThreeCapacityBasis) := Fintype.ofFinite _
  exact (finrank_span_le_card (Set.range defectThreeCapacityBasis)).trans (by
    convert! Fintype.card_range_le defectThreeCapacityBasis
    rw [Set.toFinset_card])

theorem defectThreeCapacitySpace_represents_zero :
    IsRepresentedPlace defectThreeCapacitySpace 0 := by
  refine ⟨defectTwoRationalEffectiveParam, ?_⟩
  exact Submodule.subset_span ⟨0, rfl⟩

theorem defectThreeCapacitySpace_represents_one :
    IsRepresentedPlace defectThreeCapacitySpace 1 := by
  refine ⟨defectThreeRationalOneEffectiveParam, ?_⟩
  exact Submodule.subset_span ⟨1, rfl⟩

theorem defectThreeCapacitySpace_represents_degreeTwo :
    IsRepresentedPlace defectThreeCapacitySpace 3 := by
  refine ⟨defectTwoDegreeTwoEffectiveParam, ?_⟩
  exact Submodule.subset_span ⟨2, rfl⟩

/-- The explicit three-place defect attains target capacity seven. -/
theorem defectThreeCapacitySpace_targetCapacity :
    targetCapacity defectThreeCapacitySpace = 7 :=
  targetCapacity_eq_seven_of_rational01_degreeTwo_places
    defectThreeCapacitySpace defectThreeCapacitySpace_finrank_le_three
    defectThreeCapacitySpace_represents_zero
    defectThreeCapacitySpace_represents_one
    defectThreeCapacitySpace_represents_degreeTwo

/-- Manuscript Theorem 7.2, equality witness: capacity seven is attained by a
defect of dimension at most three. -/
theorem exists_finrank_le_three_targetCapacity_eq_seven :
    ∃ Q : Submodule F₂ QuadraticQuotient,
      Module.finrank F₂ Q ≤ 3 ∧ targetCapacity Q = 7 :=
  ⟨defectThreeCapacitySpace, defectThreeCapacitySpace_finrank_le_three,
    defectThreeCapacitySpace_targetCapacity⟩

end

end N5
end UnrestrictedBooleanMul
