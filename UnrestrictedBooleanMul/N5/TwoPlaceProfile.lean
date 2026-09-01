import UnrestrictedBooleanMul.N5.ThreeRationalProfile

/-!
# Two distinct represented place types

Strong mixed-place exclusion says that the sum of chosen effective points at
two distinct closed places has empty decomposable fiber.  That sum nevertheless
lies in the span of the populated family.  Hence the populated span misses both
zero and this additional nonzero vector, sharpening the relation-kernel bound
from four to three without enumerating a Fano plane.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The sum of chosen witnesses for two distinct represented place types is a
nonzero vector in the populated span with empty decomposable fiber. -/
theorem representedPair_sum_missing
    (Q : Submodule F₂ QuadraticQuotient)
    (i j : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hij : i ≠ j) :
    let z :=
      populatedQuotientPoint (representedPopulatedPoint Q i hi) +
      populatedQuotientPoint (representedPopulatedPoint Q j hj)
    z ∈ Submodule.span F₂
        (Set.range (populatedQuotientPoint (Q := Q))) ∧
      z ≠ 0 ∧ ¬ IsPopulatedFiber z := by
  let x := representedPopulatedPoint Q i hi
  let y := representedPopulatedPoint Q j hj
  let z := populatedQuotientPoint x + populatedQuotientPoint y
  have hxy : x ≠ y := representedPopulatedPoint_ne Q i j hi hj hij
  have hzspan : z ∈ Submodule.span F₂
      (Set.range (populatedQuotientPoint (Q := Q))) := by
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨x, rfl⟩
    · exact Submodule.subset_span ⟨y, rfl⟩
  have hz0 : z ≠ 0 := by
    intro hz
    apply hxy
    apply populatedQuotientPoint_injective Q
    apply sub_eq_zero.mp
    rw [ZModModule.sub_eq_add]
    exact hz
  have hzmissing : ¬ IsPopulatedFiber z := by
    change ¬ IsPopulatedFiber
      (closedPlaceEffectivePoint (representedClosedPlaceParam Q i hi) +
       closedPlaceEffectivePoint (representedClosedPlaceParam Q j hj))
    exact not_populated_sum_of_distinct_effective_places
      (representedClosedPlaceParam Q i hi)
      (representedClosedPlaceParam Q j hj) (by simpa using hij)
  exact ⟨hzspan, hz0, hzmissing⟩

/-- Two distinct represented closed-place types reduce the additive relation
kernel to dimension at most three. -/
theorem populatedRelationKernel_finrank_le_three_of_two_distinct_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hij : i ≠ j) :
    Module.finrank F₂
      ↑(relationKernel (populatedQuotientPoint (Q := Q))) ≤ 3 := by
  let z :=
    populatedQuotientPoint (representedPopulatedPoint Q i hi) +
    populatedQuotientPoint (representedPopulatedPoint Q j hj)
  have hz := representedPair_sum_missing Q i j hi hj hij
  exact populatedRelationKernel_finrank_le_three_of_missing_span_point
    Q hQ z hz.1 hz.2.1 hz.2.2

/-- Incidence-only relation-gift bound for two distinct represented place
types.  The remaining sharp profile bounds use the local coefficient pivots
inside this three-dimensional relation kernel. -/
theorem relationGiftRank_le_three_of_two_distinct_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hij : i ≠ j) :
    relationGiftRank Q ≤ 3 :=
  (relationGiftRank_le_relationKernel Q).trans
    (populatedRelationKernel_finrank_le_three_of_two_distinct_places
      Q hQ i j hi hj hij)

end

end N5
end UnrestrictedBooleanMul
