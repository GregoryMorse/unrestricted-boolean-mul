import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryAlignedSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneR1Semantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneRInfSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneThreeR0Semantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneThreeR1Semantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneThreeRInfSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneTwoR0Semantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneTwoR1Semantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneTwoRInfSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfSemantic

/-!
# Complete normalized rational return-history chart

This module assembles the twelve algebraic leaves indexed by the four
simultaneous rational factor-pair types and the three rational feedback
directions.  The two aligned leaves carry exactly the normal-form hypotheses
consumed by their explicit affine-normalization certificates.  Every other
leaf is parameterized without a further coordinate restriction.

The statement is intentionally about the normalized history model.  The
circuit-facing factor-pair classification and the transport into these
coordinates are separate obligations; they are not hidden in this theorem.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The only chart-specific hypotheses left by the explicit certificates.
The aligned `(0,1)` and `(1,1)` leaves use their checked affine normal forms;
the ten direct leaves need no extra restriction. -/
def MixedReturnHistoryNormalForm
    (kind : MixedReturnFactorPair)
    (direction : RationalFeedbackDirection)
    (p : ZeroOneOffAxisHistoryParameters) : Prop :=
  match kind, direction with
  | .zeroOne, .zero => ZeroOneAlignedNormalForm p
  | .oneOneDifference, .zero => OneOneAlignedNormalForm p
  | _, _ => True

@[simp] theorem mixedReturnSection_zeroOne
    (p : ZeroOneOffAxisHistoryParameters) :
    mixedReturnSection .zeroOne p = p.returned := rfl

@[simp] theorem mixedReturnFeedbackProduct_zeroOne_one
    (p : ZeroOneOffAxisHistoryParameters) :
    mixedReturnFeedbackProduct .zeroOne .one p = p.feedbackProduct := rfl

/-- Every one of the twelve normalized rational history leaves excludes the
missing first-order target coordinate. -/
theorem firstOrderMissingFunctional_eq_zero_of_normalized_rational_history
    (kind : MixedReturnFactorPair)
    (direction : RationalFeedbackDirection)
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : MixedReturnHistoryNormalForm kind direction p)
    (hreturned : mixedReturnSection kind p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct kind direction p ∈
      N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget :
      quadraticProjection 10 (mixedReturnSection kind p) +
          quadraticProjection 10
            (mixedReturnFeedbackProduct kind direction p) =
        targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  have hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection kind p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct kind direction p)) :=
    quadraticQuotientProjection_eq_of_add_eq_target _ _ c htarget
  cases kind <;> cases direction
  · exact False.elim (zeroOneAligned_inconsistent_of_quadratic_history p
      (by simpa [MixedReturnHistoryNormalForm] using hnormal)
      hreturned hfeedback hprojection)
  · simpa only [mixedReturnSection_zeroOne,
      mixedReturnFeedbackProduct_zeroOne_one] using
      p.firstOrderMissingFunctional_eq_zero_of_history hreturned hfeedback c
        htarget
  · exact firstOrderMissingFunctional_eq_zero_of_zeroOneRInf_history p
      hreturned hfeedback c htarget
  · exact False.elim (oneOneAligned_inconsistent_of_quadratic_history p
      (by simpa [MixedReturnHistoryNormalForm] using hnormal)
      hreturned hfeedback hprojection)
  · exact firstOrderMissingFunctional_eq_zero_of_oneOneR1_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneOneRInf_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneTwoR0_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneTwoR1_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneTwoRInf_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneThreeR0_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneThreeR1_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneThreeRInf_history p
      hreturned hfeedback c htarget

end
end N5
end UnrestrictedBooleanMul
