import UnrestrictedBooleanMul.N5.ThreeRationalProfile

/-!
# The five-term displacement bound

This module assembles the closed rows of manuscript Theorem 6.2 while the
remaining local sparse-gift pivots are proved.  The zero-place row follows
from the profile-free four-dimensional relation-kernel bound.  The
three-rational row is imported from `ThreeRationalProfile`, where mixed-place
exclusion reduces the populated defect plane to four points.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- If no closed place is represented, the intrinsic displacement weight is
zero. -/
theorem representedPlaceWeight_eq_zero_of_no_represented_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hnone : ∀ i : Fin 4, ¬ IsRepresentedPlace Q i) :
    representedPlaceWeight Q = 0 := by
  classical
  have h₀ := hnone 0
  have h₁ := hnone 1
  have h₂ := hnone 2
  have h₃ := hnone 3
  simp [representedPlaceWeight, representedRationalPlaceCount,
    representedDegreeTwoIndicator, h₀, h₁, h₂, h₃]

/-- Manuscript Theorem 6.2, row `s = 0`: without a represented effective
place, all four available dimensions may be relation gifts. -/
theorem displacement_add_gifts_le_four_of_no_represented_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hnone : ∀ i : Fin 4, ¬ IsRepresentedPlace Q i) :
    displacementRank Q + relationGiftRank Q ≤ 4 := by
  rw [displacementRank_eq_representedPlaceWeight,
    representedPlaceWeight_eq_zero_of_no_represented_places Q hnone]
  simpa using relationGiftRank_le_four Q hQ

/-- Capacity form of the zero-place row of the displacement bound. -/
theorem targetCapacity_le_seven_of_no_represented_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hnone : ∀ i : Fin 4, ¬ IsRepresentedPlace Q i) :
    targetCapacity Q ≤ 7 := by
  rw [targetCapacity_eq_three_add_displacement_add_gifts]
  have hbound := displacement_add_gifts_le_four_of_no_represented_places
    Q hQ hnone
  omega

end

end N5
end UnrestrictedBooleanMul
