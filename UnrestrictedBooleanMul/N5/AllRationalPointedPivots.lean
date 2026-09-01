import UnrestrictedBooleanMul.N5.PointedFanoRelations
import UnrestrictedBooleanMul.N5.RationalSecantSymmetry

/-!
# Pointed Fano pivots at every rational place

This module combines the algebraically transported local secant certificates
with the unconditional pointed-Fano codimension theorem.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The symmetry-complete four-pivot space improves every pointed rational
line-gift quotient to dimension one. -/
theorem relationGiftRank_le_two_of_strongRational_place
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q) (place : Fin 3) (q : LocalKleinParam)
    (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint (rationalPlaceLabel place) q)
    (hplace : IsRepresentedPlace Q (rationalPlaceLabel place)) :
    relationGiftRank Q ≤ 2 := by
  have hgift :=
    relationGiftRank_le_lineQuotientRank_add_one_of_finrank_le_three
      Q hQ x
  have hline :=
    fanoLineGiftCoeffSpaceThrough_strongRational_quotientRank_le_one
      Q x place q hq hxPoint hplace
  change Module.finrank F₂
      (fanoLineGiftQuotientSpaceThrough Q x) ≤ 1 at hline
  omega

/-- Any represented rational place forces relation-gift rank at most two. -/
theorem relationGiftRank_le_two_of_represented_rational
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) (place : Fin 3)
    (hplace : IsRepresentedPlace Q (rationalPlaceLabel place)) :
    relationGiftRank Q ≤ 2 := by
  let p := representedClosedPlaceParam Q (rationalPlaceLabel place) hplace
  let q : LocalKleinParam := p.2.1
  have hnotDegree : rationalPlaceLabel place ≠ 3 := by
    intro h
    have := congrArg Fin.val h
    simp [rationalPlaceLabel] at this
    omega
  have hq : RationalLocalEffective q := by
    have hm := p.2.2
    change q ∈ effectiveParamsAt (rationalPlaceLabel place) at hm
    rw [effectiveParamsAt, if_neg hnotDegree] at hm
    simpa [rationalEffectiveParams] using hm
  refine relationGiftRank_le_two_of_strongRational_place
    Q hQ (representedPopulatedPoint Q (rationalPlaceLabel place) hplace)
      place q hq ?_ hplace
  rfl

theorem relationGiftRank_le_two_of_represented_rationalZero
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hzero : IsRepresentedPlace Q 0) :
    relationGiftRank Q ≤ 2 := by
  simpa [rationalPlaceLabel] using
    relationGiftRank_le_two_of_represented_rational Q hQ 0 hzero

theorem relationGiftRank_le_two_of_represented_rationalOne
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hone : IsRepresentedPlace Q 1) :
    relationGiftRank Q ≤ 2 := by
  simpa [rationalPlaceLabel] using
    relationGiftRank_le_two_of_represented_rational Q hQ 1 hone

theorem relationGiftRank_le_two_of_represented_rationalInfinity
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hinfinity : IsRepresentedPlace Q 2) :
    relationGiftRank Q ≤ 2 := by
  simpa [rationalPlaceLabel] using
    relationGiftRank_le_two_of_represented_rational Q hQ 2 hinfinity

theorem relationGiftRank_le_three_of_transformedRational_place
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q) (θ : Fin 2) (q : LocalKleinParam)
    (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint (rationalPlacePerm θ 0) q)
    (hplace : IsRepresentedPlace Q (rationalPlacePerm θ 0)) :
    relationGiftRank Q ≤ 3 := by
  have hgift :=
    relationGiftRank_le_lineQuotientRank_add_one_of_finrank_le_three
      Q hQ x
  have hline :=
    fanoLineGiftCoeffSpaceThrough_transformedRational_quotientRank_le_two
      Q x θ q hq hxPoint hplace
  change Module.finrank F₂
      (fanoLineGiftQuotientSpaceThrough Q x) ≤ 2 at hline
  omega

/-- Representing rational place one or infinity forces relation-gift rank at
most three, exactly as at rational place zero. -/
theorem relationGiftRank_le_three_of_represented_transformedRational
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) (θ : Fin 2)
    (hplace : IsRepresentedPlace Q (rationalPlacePerm θ 0)) :
    relationGiftRank Q ≤ 3 := by
  let place := rationalPlacePerm θ 0
  let p := representedClosedPlaceParam Q place hplace
  let q : LocalKleinParam := p.2.1
  have hnotDegree : place ≠ 3 := by
    fin_cases θ <;> decide
  have hq : RationalLocalEffective q := by
    have hm := p.2.2
    change q ∈ effectiveParamsAt place at hm
    rw [effectiveParamsAt, if_neg hnotDegree] at hm
    simpa [rationalEffectiveParams] using hm
  refine relationGiftRank_le_three_of_transformedRational_place
    Q hQ (representedPopulatedPoint Q place hplace) θ q hq ?_ hplace
  rfl

theorem relationGiftRank_le_three_of_represented_rationalOne
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hone : IsRepresentedPlace Q 1) :
    relationGiftRank Q ≤ 3 := by
  simpa [rationalPlacePerm] using
    relationGiftRank_le_three_of_represented_transformedRational
      Q hQ 0 hone

theorem relationGiftRank_le_three_of_represented_rationalInfinity
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hinfinity : IsRepresentedPlace Q 2) :
    relationGiftRank Q ≤ 3 := by
  simpa [rationalPlacePerm] using
    relationGiftRank_le_three_of_represented_transformedRational
      Q hQ 1 hinfinity

end

end N5
end UnrestrictedBooleanMul
