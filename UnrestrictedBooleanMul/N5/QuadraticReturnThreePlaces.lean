import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic

/-!
# Three distinct rational places force a sextic term

For factor colours `r0,r1` and feedback colour `rInfinity`, the top term is
`r0*r1*rInfinity`.  Its coefficient on `{a0,a1,a4,b0,b1,b4}` is one.  All
affine-factor and quadratic-return corrections have degree at most five,
so this feedback product cannot be quadratic.  No certificate search is
needed for this chart.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section

private theorem targetANF_rInfinityCoeff :
    targetANF rInfinityCoeff = X (4 : Fin 10) * X 9 := by
  simp [targetANF, rInfinityCoeff, Mul, mulCoefficient,
    Fin.sum_univ_succ, aVar, bVar]

private theorem threeRationalPlaces_sextic_coeff :
    (targetANF rZeroCoeff * targetANF rOneCoeff * targetANF rInfinityCoeff).coeff
      ⟨{0, 1, 4, 5, 6, 9}⟩ = 1 := by
  rw [targetANF_rZeroCoeff, targetANF_rOneCoeff, targetANF_rInfinityCoeff]
  simp (config := { decide := true }) [aLinearSumTen, bLinearSumTen, mul_add, add_mul, X, monomial_mul,
    coeff_monomial]

private theorem firstProduct_add_quartic_degreeLE_three
    (p : ZeroOneOffAxisHistoryParameters) :
    N4.DegreeLE 3 (mixedReturnFirstProduct .oneTwo p +
      targetANF rZeroCoeff * targetANF rOneCoeff) := by
  have h := degreeLE_add
    (degreeLE_add
      (((linearANFTen_degreeLE_one p.ell).mul
        (linearANFTen_degreeLE_one p.m)).mono (by decide : 2 ≤ 3))
      ((linearANFTen_degreeLE_one p.ell).mul (targetANF_degreeLE_two rOneCoeff)))
    ((targetANF_degreeLE_two rZeroCoeff).mul (linearANFTen_degreeLE_one p.m))
  convert h using 1
  simp only [mixedReturnFirstProduct, MixedReturnFactorPair.leftTwo,
    MixedReturnFactorPair.rightTwo, MixedReturnFactorPair.rightLinear,
    quadraticCoordinateANF, quadraticANFOfForm_targetTwo, zero_smul, zero_add]
  ring_nf
  simp [anf_two_eq_zero]

private theorem correctedHigh_add_quartic_degreeLE_three
    (p : ZeroOneOffAxisHistoryParameters)
    (hr : mixedReturnSection .oneTwo p ∈ N4.quadraticANFSpace 10) :
    N4.DegreeLE 3 (mixedReturnCorrectedHigh .oneTwo p +
      targetANF rZeroCoeff * targetANF rOneCoeff) := by
  have hcorrection : N4.DegreeLE 3 (mixedReturnCorrection .oneTwo p) :=
    (degreeLE_add
      (quadraticCoordinateANF_mem_quadraticANFSpace
        p.correctionConstant p.correctionLinear p.correctionTwo)
      (degreeLE_smul hr p.correctionReturn)).mono (by decide)
  have h := degreeLE_add (firstProduct_add_quartic_degreeLE_three p) hcorrection
  convert h using 1
  unfold mixedReturnCorrectedHigh
  ac_rfl

private theorem feedbackFactor_add_quadratic_degreeLE_one
    (p : ZeroOneOffAxisHistoryParameters) :
    N4.DegreeLE 1 (quadraticCoordinateANF p.feedbackConstant p.feedbackLinear
      (targetTwo rInfinityCoeff) + targetANF rInfinityCoeff) := by
  have hAff : p.feedbackConstant • (1 : ANF 10) + linearANFTen p.feedbackLinear ∈
      affine 10 := (affine 10).add_mem
    ((affine 10).smul_mem _ (one_mem_affine 10)) (linearANFTen_mem_affine _)
  rw [quadraticCoordinateANF, quadraticANFOfForm_targetTwo,
    add_assoc, anf_add_self, add_zero]
  exact fun s hs => N4.affine_coeff_zero_of_two_le hAff s (by omega)

/-- The full feedback differs from the fixed sextic only in degrees ≤5. -/
theorem oneTwoRInf_feedback_add_sextic_degreeLE_five
    (p : ZeroOneOffAxisHistoryParameters)
    (hr : mixedReturnSection .oneTwo p ∈ N4.quadraticANFSpace 10) :
    N4.DegreeLE 5 (mixedReturnFeedbackProduct .oneTwo .infinity p +
      targetANF rZeroCoeff * targetANF rOneCoeff * targetANF rInfinityCoeff) := by
  have hfirst := (correctedHigh_add_quartic_degreeLE_three p hr).mul
    (quadraticCoordinateANF_mem_quadraticANFSpace p.feedbackConstant
      p.feedbackLinear (targetTwo rInfinityCoeff))
  have hsecond := ((targetANF_degreeLE_two rZeroCoeff).mul
    (targetANF_degreeLE_two rOneCoeff)).mul (feedbackFactor_add_quadratic_degreeLE_one p)
  have h := degreeLE_add hfirst hsecond
  convert h using 1
  simp only [mixedReturnFeedbackProduct, RationalFeedbackDirection.two]
  ring_nf
  simp [anf_two_eq_zero]

/-- Three distinct rational factor colours cannot produce a quadratic
feedback wire, regardless of its lower-order parameters. -/
theorem oneTwoRInf_quadratic_history_impossible
    (p : ZeroOneOffAxisHistoryParameters)
    (hr : mixedReturnSection .oneTwo p ∈ N4.quadraticANFSpace 10)
    (hf : mixedReturnFeedbackProduct .oneTwo .infinity p ∈ N4.quadraticANFSpace 10) :
    False := by
  have hlow := oneTwoRInf_feedback_add_sextic_degreeLE_five p hr
    ⟨{0, 1, 4, 5, 6, 9}⟩ (by decide)
  have hzero := hf ⟨{0, 1, 4, 5, 6, 9}⟩ (by decide)
  change (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
      ⟨{0, 1, 4, 5, 6, 9}⟩ +
    (targetANF rZeroCoeff * targetANF rOneCoeff * targetANF rInfinityCoeff).coeff
      ⟨{0, 1, 4, 5, 6, 9}⟩ = 0 at hlow
  rw [hzero, threeRationalPlaces_sextic_coeff, zero_add] at hlow
  exact one_ne_zero hlow

/-- Circuit-facing chart conclusion, now obtained from the sextic obstruction. -/
theorem firstOrderMissingFunctional_eq_zero_of_oneTwoRInf_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo .infinity p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (_htarget : quadraticProjection 10 (mixedReturnSection .oneTwo p) +
      quadraticProjection 10 (mixedReturnFeedbackProduct .oneTwo .infinity p) = targetTwo c) :
    firstOrderMissingFunctional c = 0 :=
  (oneTwoRInf_quadratic_history_impossible p hreturned hfeedback).elim

end
end UnrestrictedBooleanMul.N5
