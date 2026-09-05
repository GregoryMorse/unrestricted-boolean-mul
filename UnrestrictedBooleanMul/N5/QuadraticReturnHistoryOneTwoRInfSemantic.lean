import UnrestrictedBooleanMul.N5.QuadraticReturnThreePlaces

/-!
# Three-place feedback: compatibility interface

The history is excluded by its nonzero sextic coefficient.  The former raw
polynomial certificate is unnecessary.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section

theorem oneTwoRInf_missingCoordinate_eq_zero_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo .infinity p ∈
      N4.quadraticANFSpace 10)
    (_hprojection : quadraticQuotientProjection
      (quadraticProjection 10 (mixedReturnSection .oneTwo p)) =
      quadraticQuotientProjection (quadraticProjection 10
        (mixedReturnFeedbackProduct .oneTwo .infinity p))) :
    returnHistoryMissingCoordinate (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
      returnHistoryMissingCoordinate (quadraticProjection 10
        (mixedReturnFeedbackProduct .oneTwo .infinity p)) = 0 :=
  (oneTwoRInf_quadratic_history_impossible p hreturned hfeedback).elim

end
end UnrestrictedBooleanMul.N5
