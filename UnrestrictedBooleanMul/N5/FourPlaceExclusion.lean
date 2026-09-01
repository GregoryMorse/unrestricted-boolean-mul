import UnrestrictedBooleanMul.N5.FourPlaceRelation

/-!
# Algebraic exclusion of the four-place quadrilateral

The checked sixteen-direction Hermite atlas gives a direct-sum certificate for
the four closed-place quotient charts.  Consequently one nonzero effective
point from each chart cannot have zero sum.  Combined with
`four_represented_place_points_sum_eq_zero`, this excludes simultaneous
representation of all four place types in a defect space of dimension at most
three.

This direct-sum proof is the global coordinate form of the manuscript's
overlap/Klein obstruction.  It uses the displayed inverse matrix already
verified in `EffectiveFibers`, not a simultaneous degree-six interpolation or
a finite search.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- One nonzero effective parameter from each of the four direct atlas charts
cannot sum to zero in the quadratic quotient. -/
theorem four_closedPlaceEffectivePoint_sum_ne_zero
    (p : ∀ i : Fin 4, EffectiveParamAt i) :
    (∑ i : Fin 4,
      closedPlaceEffectivePoint ⟨i, p i⟩) ≠ 0 := by
  intro hsum
  let liftSum : TwoForm :=
    ∑ i : Fin 4, closedPlaceLift i (p i).1
  have hprojection : quadraticQuotientProjection liftSum = 0 := by
    change quadraticQuotientProjection
      (∑ i : Fin 4, closedPlaceLift i (p i).1) = 0
    rw [map_sum]
    simpa [closedPlaceEffectivePoint, closedPlaceQuotientPoint] using hsum
  have hliftTarget : liftSum ∈ targetTwoSpace :=
    (quadraticQuotientProjection_eq_zero_iff liftSum).1 hprojection
  have hremainder : quotientRemainder liftSum = 0 :=
    (quotientRemainder_eq_zero_iff liftSum).2 hliftTarget
  have hnested : ∑ i : Fin 4, ∑ k : Fin 4,
      (p i).1 k • closedPlaceAtlasDirection (i, k) = 0 := by
    change quotientRemainder
      (∑ i : Fin 4, closedPlaceLift i (p i).1) = 0 at hremainder
    rw [map_sum] at hremainder
    simpa only [quotientRemainder_closedPlaceLift] using hremainder
  let coefficient : Fin 4 × Fin 4 → F₂ :=
    fun ik ↦ (p ik.1).1 ik.2
  have hsingle : ∑ ik : Fin 4 × Fin 4,
      coefficient ik • closedPlaceAtlasDirection ik = 0 := by
    rw [Fintype.sum_prod_type]
    exact hnested
  have hcoefficient := Fintype.linearIndependent_iff.mp
    closedPlaceAtlasDirection_linearIndependent coefficient hsingle
  have hpzero : (p 0).1 = 0 := by
    funext k
    simpa [coefficient] using hcoefficient (0, k)
  exact effectiveParamsAt_ne_zero 0 (p 0).2 hpzero

/-- Manuscript Theorem 6.2, exceptional-profile clause: a defect space of
dimension at most three cannot represent the degree-two place and all three
rational places simultaneously. -/
theorem not_all_closedPlaces_represented
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    ¬ (∀ i : Fin 4, IsRepresentedPlace Q i) := by
  intro hplace
  let p : ∀ i : Fin 4, EffectiveParamAt i :=
    fun i ↦ Classical.choose (hplace i)
  have hpPoint (i : Fin 4) :
      closedPlaceEffectivePoint ⟨i, p i⟩ ∈ Q :=
    Classical.choose_spec (hplace i)
  have heq : ∑ i : Fin 4, closedPlaceEffectivePoint ⟨i, p i⟩ = 0 := by
    calc
      ∑ i : Fin 4, closedPlaceEffectivePoint ⟨i, p i⟩ =
          ∑ i : Fin 4, populatedQuotientPoint
            (closedPlacePopulatedPoint Q ⟨i, p i⟩ (hpPoint i)) := by
        rfl
      _ = 0 := by
        let hplace' : ∀ i : Fin 4, IsRepresentedPlace Q i := hplace
        have hsum := four_represented_place_points_sum_eq_zero Q hQ hplace'
        apply congrArg (fun z : QuadraticQuotient ↦ z) at hsum
        simpa [representedPopulatedPoint, representedClosedPlaceParam,
          p, hplace'] using hsum
  exact four_closedPlaceEffectivePoint_sum_ne_zero p heq

/-- Numerical form of the exceptional-profile exclusion: in defect dimension
at most three, the represented-place displacement weight is at most four. -/
theorem representedPlaceWeight_le_four_of_finrank_le_three
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    representedPlaceWeight Q ≤ 4 := by
  classical
  by_contra hbound
  have hweight : 5 ≤ representedPlaceWeight Q := by omega
  by_cases h₀ : IsRepresentedPlace Q 0 <;>
    by_cases h₁ : IsRepresentedPlace Q 1 <;>
      by_cases h₂ : IsRepresentedPlace Q 2 <;>
        by_cases h₃ : IsRepresentedPlace Q 3
  all_goals
    simp [representedPlaceWeight, representedRationalPlaceCount,
      representedDegreeTwoIndicator, h₀, h₁, h₂, h₃] at hweight
  apply not_all_closedPlaces_represented Q hQ
  intro i
  fin_cases i <;> assumption

end

end N5
end UnrestrictedBooleanMul
