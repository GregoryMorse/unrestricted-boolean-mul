import UnrestrictedBooleanMul.N5.ANFSubstitution
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic

/-!
# The off-axis rational return is one algebraic case

The projective substitution `t ↦ t/(t+1)` fixes the zero place and exchanges
one with infinity.  Its action on degree-four binary forms is an involution.
We apply it to the entire Boolean history, retaining the first high product,
the returned section, and every old-state correction.  Thus the infinity
feedback case follows from the already checked one-place case.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section

/-- Pullback of the ten input coordinates under `t ↦ t/(t+1)`. -/
def rationalOffAxisInput : Fin 10 → LinearForm :=
  ![![1,0,0,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0,0,0],
    ![0,1,1,0,0,0,0,0,0,0], ![0,1,0,1,0,0,0,0,0,0],
    ![1,1,1,1,1,0,0,0,0,0], ![0,0,0,0,0,1,0,0,0,0],
    ![0,0,0,0,0,0,1,0,0,0], ![0,0,0,0,0,0,1,1,0,0],
    ![0,0,0,0,0,0,1,0,1,0], ![0,0,0,0,0,1,1,1,1,1]]

def rationalOffAxisLinear (ell : LinearForm) : LinearForm :=
  ![ell 0 + ell 4, ell 1 + ell 2 + ell 3 + ell 4,
    ell 2 + ell 4, ell 3 + ell 4, ell 4,
    ell 5 + ell 9, ell 6 + ell 7 + ell 8 + ell 9,
    ell 7 + ell 9, ell 8 + ell 9, ell 9]

/-- The induced pullback on the nine Hankel coefficients. -/
def rationalOffAxisCoeff (c : TargetCoeff) : TargetCoeff :=
  ![c 0 + c 8, c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 + c 8,
    c 2 + c 4 + c 6 + c 8, c 3 + c 4 + c 7 + c 8, c 4 + c 8,
    c 5 + c 6 + c 7 + c 8, c 6 + c 8, c 7 + c 8, c 8]

def rationalOffAxisANF : ANF 10 →ₐ[F₂] ANF 10 :=
  anfSubstitution (fun i => linearANFTen (rationalOffAxisInput i))

@[simp] theorem rationalOffAxisANF_X (i : Fin 10) :
    rationalOffAxisANF (X i) = linearANFTen (rationalOffAxisInput i) :=
  anfSubstitution_X _ i

theorem rationalOffAxisLinear_add (ell m : LinearForm) :
    rationalOffAxisLinear (ell + m) =
      rationalOffAxisLinear ell + rationalOffAxisLinear m := by
  funext i
  fin_cases i <;> simp [rationalOffAxisLinear] <;> ring

theorem rationalOffAxisANF_linear (ell : LinearForm) :
    rationalOffAxisANF (linearANFTen ell) =
      linearANFTen (rationalOffAxisLinear ell) := by
  rw [linearANFTen, map_sum]
  simp only [map_smul, rationalOffAxisANF_X]
  simp [linearANFTen, rationalOffAxisInput, rationalOffAxisLinear,
    Fin.sum_univ_succ, add_smul]
  module

set_option maxHeartbeats 1000000 in
theorem rationalOffAxisANF_target (c : TargetCoeff) :
    rationalOffAxisANF (targetANF c) = targetANF (rationalOffAxisCoeff c) := by
  rw [targetANF_eq_double_sum, map_sum]
  simp_rw [map_sum, map_smul, map_mul, rationalOffAxisANF_X]
  rw [targetANF_eq_double_sum]
  apply eval_injective 10
  funext x
  simp [linearANFTen, rationalOffAxisInput, rationalOffAxisCoeff,
    hankelIndex, aCoord, bCoord, Fin.sum_univ_succ, eval_eq_evalHom]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

@[simp] theorem rationalOffAxisCoeff_zero :
    rationalOffAxisCoeff rZeroCoeff = rZeroCoeff := by
  decide

@[simp] theorem rationalOffAxisCoeff_infinity :
    rationalOffAxisCoeff rInfinityCoeff = rOneCoeff := by
  decide

@[simp] theorem rationalOffAxisCoeff_missing (c : TargetCoeff) :
    firstOrderMissingFunctional (rationalOffAxisCoeff c) =
      firstOrderMissingFunctional c := by
  simp [firstOrderMissingFunctional, rationalOffAxisCoeff]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

theorem rationalOffAxisANF_quadraticTarget
    (a : F₂) (ell : LinearForm) (c : TargetCoeff) :
    rationalOffAxisANF (quadraticCoordinateANF a ell (targetTwo c)) =
      quadraticCoordinateANF a (rationalOffAxisLinear ell)
        (targetTwo (rationalOffAxisCoeff c)) := by
  simp only [quadraticCoordinateANF, quadraticANFOfForm_targetTwo,
    map_add, map_smul, map_one, rationalOffAxisANF_linear,
    rationalOffAxisANF_target]

theorem rationalOffAxisANF_mem_affine {p : ANF 10}
    (hp : p ∈ affine 10) : rationalOffAxisANF p ∈ affine 10 :=
  anfSubstitution_mem_affine _ (fun _ => linearANFTen_mem_affine _) hp

theorem rationalOffAxisANF_mem_quadratic {p : ANF 10}
    (hp : p ∈ N4.quadraticANFSpace 10) :
    rationalOffAxisANF p ∈ N4.quadraticANFSpace 10 :=
  anfSubstitution_mem_quadratic _ (fun _ => linearANFTen_mem_affine _) hp

/-- Coordinates of a target word in the original eight correction directions.
The only compatibility equation is the first-order missing functional. -/
def returnHistoryCoordinates (c : TargetCoeff) : Fin 8 → F₂ :=
  ![c 0 + c 4, c 4, c 8 + c 4, c 1 + c 4 + c 3 + c 6,
    c 3 + c 6, c 7 + c 4 + c 3 + c 6, c 2 + c 4, c 6 + c 4]

theorem returnHistoryCoordinates_reconstruct (c : TargetCoeff)
    (hc : firstOrderMissingFunctional c = 0) :
    (∑ i : Fin 8, returnHistoryCoordinates c i •
      returnHistoryCorrectionDirections i) = c := by
  have h5 : c 5 = c 2 + c 3 + c 6 := by
    change c 2 + c 3 + c 5 + c 6 = 0 at hc
    calc
      c 5 = (c 2 + c 3 + c 5 + c 6) + (c 2 + c 3 + c 6) := by
        ring_nf
        simp [CharTwo.ofNat_eq_mod]
      _ = c 2 + c 3 + c 6 := by rw [hc, zero_add]
  funext i
  fin_cases i <;>
    simp [returnHistoryCoordinates, returnHistoryCorrectionDirections,
      rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
      historyJOneCoeff, historyJInfinityCoeff, dStarZeroCoeff,
      dStarOneCoeff, Fin.sum_univ_succ, h5] <;>
    ring_nf <;> simp [CharTwo.ofNat_eq_mod]

theorem ZeroOneOffAxisHistoryParameters.correctionCoeff_missing
    (p : ZeroOneOffAxisHistoryParameters) :
    firstOrderMissingFunctional p.correctionCoeff = 0 := by
  simp [ZeroOneOffAxisHistoryParameters.correctionCoeff,
    returnHistoryCorrectionDirections, firstOrderMissingFunctional,
    rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
    historyJOneCoeff, historyJInfinityCoeff, dStarZeroCoeff,
    dStarOneCoeff, Fin.sum_univ_succ]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- Transport all parameters together, keeping both the returned section and
its correction coefficient. -/
def ZeroOneOffAxisHistoryParameters.offAxis
    (p : ZeroOneOffAxisHistoryParameters) : ZeroOneOffAxisHistoryParameters where
  ell := rationalOffAxisLinear p.ell
  m := rationalOffAxisLinear p.m
  leftShift := rationalOffAxisLinear p.leftShift
  rightShift := rationalOffAxisLinear p.rightShift
  feedbackConstant := p.feedbackConstant
  feedbackLinear := rationalOffAxisLinear p.feedbackLinear
  correctionConstant := p.correctionConstant
  correctionLinear := rationalOffAxisLinear p.correctionLinear
  correctionTarget := returnHistoryCoordinates (rationalOffAxisCoeff p.correctionCoeff)
  correctionReturn := p.correctionReturn

theorem ZeroOneOffAxisHistoryParameters.offAxis_correctionCoeff
    (p : ZeroOneOffAxisHistoryParameters) :
    p.offAxis.correctionCoeff = rationalOffAxisCoeff p.correctionCoeff := by
  apply returnHistoryCoordinates_reconstruct
  rw [rationalOffAxisCoeff_missing, p.correctionCoeff_missing]

theorem ZeroOneOffAxisHistoryParameters.offAxis_firstProduct
    (p : ZeroOneOffAxisHistoryParameters) :
    rationalOffAxisANF (mixedReturnFirstProduct .zeroOne p) =
      p.offAxis.firstProduct := by
  simp [mixedReturnFirstProduct, MixedReturnFactorPair.leftTwo,
    MixedReturnFactorPair.rightTwo, MixedReturnFactorPair.rightLinear,
    ZeroOneOffAxisHistoryParameters.firstProduct,
    quadraticCoordinateANF, quadraticANFOfForm_targetTwo,
    rationalOffAxisANF_linear,
    ZeroOneOffAxisHistoryParameters.offAxis]
  simp [linearANFTen, rationalOffAxisInput, Fin.sum_univ_succ]

theorem ZeroOneOffAxisHistoryParameters.offAxis_returned
    (p : ZeroOneOffAxisHistoryParameters) :
    rationalOffAxisANF (mixedReturnSection .zeroOne p) = p.offAxis.returned := by
  simp [mixedReturnSection, mixedReturnFirstProduct, mixedReturnShiftedProduct,
    MixedReturnFactorPair.leftTwo, MixedReturnFactorPair.rightTwo,
    MixedReturnFactorPair.rightLinear, ZeroOneOffAxisHistoryParameters.returned,
    ZeroOneOffAxisHistoryParameters.firstProduct,
    ZeroOneOffAxisHistoryParameters.shiftedProduct,
    quadraticCoordinateANF, quadraticANFOfForm_targetTwo,
    rationalOffAxisANF_linear,
    ZeroOneOffAxisHistoryParameters.offAxis, rationalOffAxisLinear_add]
  simp [linearANFTen, rationalOffAxisInput, Fin.sum_univ_succ]

theorem ZeroOneOffAxisHistoryParameters.offAxis_feedback
    (p : ZeroOneOffAxisHistoryParameters) :
    rationalOffAxisANF (mixedReturnFeedbackProduct .zeroOne .infinity p) =
      p.offAxis.feedbackProduct := by
  simp only [mixedReturnFeedbackProduct, mixedReturnCorrectedHigh,
    mixedReturnCorrection, map_mul, map_add, map_smul,
    p.offAxis_firstProduct, p.offAxis_returned,
    ZeroOneOffAxisHistoryParameters.feedbackProduct,
    ZeroOneOffAxisHistoryParameters.correctedHighFactor,
    ZeroOneOffAxisHistoryParameters.correction,
    ZeroOneOffAxisHistoryParameters.feedbackFactor,
    RationalFeedbackDirection.two,
    ZeroOneOffAxisHistoryParameters.correctionTwo_eq_targetTwo,
    rationalOffAxisANF_quadraticTarget, rationalOffAxisCoeff_infinity,
    p.offAxis_correctionCoeff]
  rfl

/-- Infinity feedback is the one-place feedback theorem transported by a
single projective involution.  No additional polynomial certificate is used. -/
theorem firstOrderMissingFunctional_eq_zero_of_zeroOneRInf_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .zeroOne p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne .infinity p ∈
      N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget : quadraticProjection 10 (mixedReturnSection .zeroOne p) +
      quadraticProjection 10 (mixedReturnFeedbackProduct .zeroOne .infinity p) =
        targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  have hr := rationalOffAxisANF_mem_quadratic hreturned
  have hf := rationalOffAxisANF_mem_quadratic hfeedback
  rw [p.offAxis_returned] at hr
  rw [p.offAxis_feedback] at hf
  obtain ⟨a, ha, heq⟩ := exists_affine_add_target_of_quadraticProjection
    ((N4.quadraticANFSpace 10).add_mem hreturned hfeedback) c
    (by simpa only [map_add] using htarget)
  have hmap := congrArg (fun z => quadraticProjection 10 (rationalOffAxisANF z)) heq
  have ha0 := quadraticProjection_kills_affine 10
    (rationalOffAxisANF_mem_affine ha)
  change quadraticProjection 10 (rationalOffAxisANF a) = 0 at ha0
  simp only [map_add, p.offAxis_returned, p.offAxis_feedback,
    rationalOffAxisANF_target, quadraticProjection_targetANF, ha0, zero_add] at hmap
  have h := p.offAxis.firstOrderMissingFunctional_eq_zero_of_history
    hr hf (rationalOffAxisCoeff c) hmap
  simpa only [rationalOffAxisCoeff_missing] using h

end
end UnrestrictedBooleanMul.N5
