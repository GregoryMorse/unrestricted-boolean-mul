import UnrestrictedBooleanMul.N5.QuadraticReturnOffAxisSymmetry

/-!
# Infinity feedback from projective symmetry

The full history theorem is proved in `QuadraticReturnOffAxisSymmetry` by
transporting the one-place theorem.  This compatibility module retains the
quadratic-quotient formulation without the withdrawn raw certificate.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section

theorem zeroOneRInf_missingCoordinate_eq_zero_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .zeroOne p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne .infinity p ∈
      N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection (quadraticProjection 10 (mixedReturnSection .zeroOne p)) =
        quadraticQuotientProjection (quadraticProjection 10
          (mixedReturnFeedbackProduct .zeroOne .infinity p))) :
    returnHistoryMissingCoordinate (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
      returnHistoryMissingCoordinate (quadraticProjection 10
        (mixedReturnFeedbackProduct .zeroOne .infinity p)) = 0 := by
  let q := quadraticProjection 10 (mixedReturnSection .zeroOne p)
  let r := quadraticProjection 10 (mixedReturnFeedbackProduct .zeroOne .infinity p)
  have hzero : quadraticQuotientProjection (q + r) = 0 := by
    rw [map_add, show quadraticQuotientProjection q = quadraticQuotientProjection r
      from hprojection]
    rw [← two_smul F₂, show (2 : F₂) = 0 by decide, zero_smul]
  obtain ⟨c, hc⟩ := (quadraticQuotientProjection_eq_zero_iff (q + r)).1 hzero
  have hc' : q + r = targetTwo c := hc.symm
  calc
    _ = returnHistoryMissingCoordinate (q + r) := (map_add _ q r).symm
    _ = firstOrderMissingFunctional c := by
      rw [hc', returnHistoryMissingCoordinate_targetTwo]
    _ = 0 := firstOrderMissingFunctional_eq_zero_of_zeroOneRInf_history
      p hreturned hfeedback c hc'

end
end UnrestrictedBooleanMul.N5
