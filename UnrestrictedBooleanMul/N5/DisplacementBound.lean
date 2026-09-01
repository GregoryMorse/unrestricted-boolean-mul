import UnrestrictedBooleanMul.N5.ThreeRationalProfile
import UnrestrictedBooleanMul.N5.PointedFanoRelations

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

/-- The profile with only the zero rational place represented has weight
one. -/
theorem representedPlaceWeight_eq_one_of_only_rationalZero
    (Q : Submodule F₂ QuadraticQuotient)
    (h₀ : IsRepresentedPlace Q 0)
    (h₁ : ¬ IsRepresentedPlace Q 1)
    (h₂ : ¬ IsRepresentedPlace Q 2)
    (h₃ : ¬ IsRepresentedPlace Q 3) :
    representedPlaceWeight Q = 1 := by
  simp [representedPlaceWeight, representedRationalPlaceCount,
    representedDegreeTwoIndicator, h₀, h₁, h₂, h₃]

/-- The one-rational-place row of the displacement bound. -/
theorem displacement_add_gifts_le_four_of_only_rationalZero
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h₀ : IsRepresentedPlace Q 0)
    (h₁ : ¬ IsRepresentedPlace Q 1)
    (h₂ : ¬ IsRepresentedPlace Q 2)
    (h₃ : ¬ IsRepresentedPlace Q 3) :
    displacementRank Q + relationGiftRank Q ≤ 4 := by
  rw [displacementRank_eq_representedPlaceWeight,
    representedPlaceWeight_eq_one_of_only_rationalZero Q h₀ h₁ h₂ h₃]
  have hgift := relationGiftRank_le_three_of_represented_rationalZero Q hQ h₀
  omega

theorem targetCapacity_le_seven_of_only_rationalZero
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h₀ : IsRepresentedPlace Q 0)
    (h₁ : ¬ IsRepresentedPlace Q 1)
    (h₂ : ¬ IsRepresentedPlace Q 2)
    (h₃ : ¬ IsRepresentedPlace Q 3) :
    targetCapacity Q ≤ 7 := by
  rw [targetCapacity_eq_three_add_displacement_add_gifts]
  have hbound := displacement_add_gifts_le_four_of_only_rationalZero
    Q hQ h₀ h₁ h₂ h₃
  omega

/-- The profile with only the degree-two place represented has weight two. -/
theorem representedPlaceWeight_eq_two_of_only_degreeTwo
    (Q : Submodule F₂ QuadraticQuotient)
    (h₀ : ¬ IsRepresentedPlace Q 0)
    (h₁ : ¬ IsRepresentedPlace Q 1)
    (h₂ : ¬ IsRepresentedPlace Q 2)
    (h₃ : IsRepresentedPlace Q 3) :
    representedPlaceWeight Q = 2 := by
  simp [representedPlaceWeight, representedRationalPlaceCount,
    representedDegreeTwoIndicator, h₀, h₁, h₂, h₃]

/-- The degree-two-only row of the displacement bound. -/
theorem displacement_add_gifts_le_four_of_only_degreeTwo
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h₀ : ¬ IsRepresentedPlace Q 0)
    (h₁ : ¬ IsRepresentedPlace Q 1)
    (h₂ : ¬ IsRepresentedPlace Q 2)
    (h₃ : IsRepresentedPlace Q 3) :
    displacementRank Q + relationGiftRank Q ≤ 4 := by
  rw [displacementRank_eq_representedPlaceWeight,
    representedPlaceWeight_eq_two_of_only_degreeTwo Q h₀ h₁ h₂ h₃]
  have hgift := relationGiftRank_le_two_of_represented_degreeTwo Q hQ h₃
  omega

theorem targetCapacity_le_seven_of_only_degreeTwo
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h₀ : ¬ IsRepresentedPlace Q 0)
    (h₁ : ¬ IsRepresentedPlace Q 1)
    (h₂ : ¬ IsRepresentedPlace Q 2)
    (h₃ : IsRepresentedPlace Q 3) :
    targetCapacity Q ≤ 7 := by
  rw [targetCapacity_eq_three_add_displacement_add_gifts]
  have hbound := displacement_add_gifts_le_four_of_only_degreeTwo
    Q hQ h₀ h₁ h₂ h₃
  omega

end

end N5
end UnrestrictedBooleanMul
