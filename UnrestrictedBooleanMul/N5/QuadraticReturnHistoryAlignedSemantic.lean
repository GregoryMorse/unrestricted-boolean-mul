import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedCorrectionZeroSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedCorrectionOneSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedCorrectionZeroSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedCorrectionOneSemantic

/-!
# Aligned exceptional return-history closure

The final Boolean bit split removes the four exceptional aligned leaves.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem zeroOneAligned_inconsistent_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : ZeroOneAlignedNormalForm p)
    (hreturned : mixedReturnSection .zeroOne p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne .zero p ∈
      N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p))) :
    False := by
  rcases f2_eq_zero_or_one p.correctionReturn with hzero | hone
  · exact zeroOneAlignedCorrectionZero_inconsistent_of_quadratic_history
      p hnormal hzero hreturned hfeedback hprojection
  · exact zeroOneAlignedCorrectionOne_inconsistent_of_quadratic_history
      p hnormal hone hreturned hfeedback hprojection

theorem oneOneAligned_inconsistent_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : OneOneAlignedNormalForm p)
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference .zero p ∈
      N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnSection .oneOneDifference p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .zero p))) :
    False := by
  rcases f2_eq_zero_or_one p.correctionReturn with hzero | hone
  · exact oneOneAlignedCorrectionZero_inconsistent_of_quadratic_history
      p hnormal hzero hreturned hfeedback hprojection
  · exact oneOneAlignedCorrectionOne_inconsistent_of_quadratic_history
      p hnormal hone hreturned hfeedback hprojection

end
end N5
end UnrestrictedBooleanMul
