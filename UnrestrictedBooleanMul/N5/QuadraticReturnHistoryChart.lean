import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedCorrectionZeroSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedCorrectionOneSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedBase
import UnrestrictedBooleanMul.N5.QuadraticReturnFactorShear
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneTwoR0Semantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneTwoR1Semantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneTwoRInfSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfSemantic

/-!
# Complete normalized rational return-history chart

Boolean factor shears reduce the four simultaneous factor-pair types to
`(0,1)` and `(1,2)`.  A projective involution identifies the two off-axis
`(0,1)` directions.  Three distinct rational places are excluded by a
nonzero sextic coefficient.  The proof does not need separate `(1,1)`,
`(1,3)`, `(0,1),RInf`, or `(1,2),RInf` certificates.
The aligned leaf still carries its explicit normal-form hypothesis.

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

private theorem zeroOne_history
    (direction : RationalFeedbackDirection)
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : MixedReturnHistoryNormalForm .zeroOne direction p)
    (hreturned : mixedReturnSection .zeroOne p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne direction p ∈
      N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget : quadraticProjection 10 (mixedReturnSection .zeroOne p) +
      quadraticProjection 10 (mixedReturnFeedbackProduct .zeroOne direction p) = targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  cases direction
  · have hprojection := quadraticQuotientProjection_eq_of_add_eq_target _ _ c htarget
    rcases f2_eq_zero_or_one p.correctionReturn with hzero | hone
    · exact False.elim (zeroOneAlignedCorrectionZero_inconsistent_of_quadratic_history
        p hnormal hzero hreturned hfeedback hprojection)
    · exact False.elim (zeroOneAlignedCorrectionOne_inconsistent_of_quadratic_history
        p hnormal hone hreturned hfeedback hprojection)
  · simpa only [mixedReturnSection_zeroOne,
      mixedReturnFeedbackProduct_zeroOne_one] using
      p.firstOrderMissingFunctional_eq_zero_of_history hreturned hfeedback c
        htarget
  · exact firstOrderMissingFunctional_eq_zero_of_zeroOneRInf_history p
      hreturned hfeedback c htarget

private theorem oneTwo_history
    (direction : RationalFeedbackDirection)
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo direction p ∈
      N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget : quadraticProjection 10 (mixedReturnSection .oneTwo p) +
      quadraticProjection 10 (mixedReturnFeedbackProduct .oneTwo direction p) = targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  cases direction
  · exact firstOrderMissingFunctional_eq_zero_of_oneTwoR0_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneTwoR1_history p
      hreturned hfeedback c htarget
  · exact firstOrderMissingFunctional_eq_zero_of_oneTwoRInf_history p
      hreturned hfeedback c htarget

private theorem equalShear_normalForm (p : ZeroOneOffAxisHistoryParameters)
    (h : OneOneAlignedNormalForm p) :
    ZeroOneAlignedNormalForm (ReturnFactorShear.equal.parameters p) :=
  ⟨h.m1, h.m2, h.m4, h.m6, h.m7, h.x1, h.x2, h.x4, h.x6, h.x7⟩

/-- All twelve named histories follow from the two basic factor types.
Factor shears preserve the feedback ANF exactly and the returned section
modulo affine wires, so neither the target equation nor its cost is weakened. -/
theorem firstOrderMissingFunctional_eq_zero_of_normalized_rational_history
    (kind : MixedReturnFactorPair)
    (direction : RationalFeedbackDirection)
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : MixedReturnHistoryNormalForm kind direction p)
    (hreturned : mixedReturnSection kind p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct kind direction p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget : quadraticProjection 10 (mixedReturnSection kind p) +
      quadraticProjection 10 (mixedReturnFeedbackProduct kind direction p) = targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  cases kind with
  | zeroOne => exact zeroOne_history direction p hnormal hreturned hfeedback c htarget
  | oneOneDifference =>
    obtain ⟨hr, hf, hc⟩ := ReturnFactorShear.equal.quadratic_history
      direction p hreturned hfeedback c htarget
    apply zeroOne_history direction (ReturnFactorShear.equal.parameters p) ?_ hr hf c hc
    cases direction
    · exact equalShear_normalForm p hnormal
    · trivial
    · trivial
  | oneTwo => exact oneTwo_history direction p hreturned hfeedback c htarget
  | oneThree =>
    obtain ⟨hr, hf, hc⟩ := ReturnFactorShear.incident.quadratic_history
      direction p hreturned hfeedback c htarget
    exact oneTwo_history direction (ReturnFactorShear.incident.parameters p) hr hf c hc

end
end N5
end UnrestrictedBooleanMul
