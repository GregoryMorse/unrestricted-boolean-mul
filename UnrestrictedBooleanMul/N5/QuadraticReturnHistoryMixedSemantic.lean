import UnrestrictedBooleanMul.N5.QuadraticReturnHistorySemantic

/-!
# Semantic bridge for mixed rational factor pairs

The `(1,2)` and `(1,3)` return histories use the same 71 named Boolean
parameters as the canonical `(0,1)` leaf.  This module keeps one semantic
construction and varies only the fixed quadratic parts of the two original
factors and of the later feedback factor.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The two mixed simultaneous factor-pair types. -/
inductive MixedReturnFactorPair where
  | oneTwo
  | oneThree
  deriving DecidableEq

/-- The three rational quadratic directions available to the feedback
factor. -/
inductive RationalFeedbackDirection where
  | zero
  | one
  | infinity
  deriving DecidableEq

def MixedReturnFactorPair.leftTwo : MixedReturnFactorPair → TwoForm
  | .oneTwo | .oneThree => targetTwo rZeroCoeff

def MixedReturnFactorPair.rightTwo : MixedReturnFactorPair → TwoForm
  | .oneTwo => targetTwo rOneCoeff
  | .oneThree => targetTwo (rZeroCoeff + rOneCoeff)

def RationalFeedbackDirection.two : RationalFeedbackDirection → TwoForm
  | .zero => targetTwo rZeroCoeff
  | .one => targetTwo rOneCoeff
  | .infinity => targetTwo rInfinityCoeff

/-- First high product for a mixed simultaneous factor pair. -/
def mixedReturnFirstProduct (kind : MixedReturnFactorPair)
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF 0 p.ell kind.leftTwo *
    quadraticCoordinateANF 0 p.m kind.rightTwo

/-- Equal-high comparison product after affine shifts of both factors. -/
def mixedReturnShiftedProduct (kind : MixedReturnFactorPair)
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF 0 (p.ell + p.leftShift) kind.leftTwo *
    quadraticCoordinateANF 0 (p.m + p.rightShift) kind.rightTwo

/-- Quadratic section returned by the equal-high comparison. -/
def mixedReturnSection (kind : MixedReturnFactorPair)
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  mixedReturnFirstProduct kind p + mixedReturnShiftedProduct kind p

/-- Admissible old-state correction, retaining the returned section. -/
def mixedReturnCorrection (kind : MixedReturnFactorPair)
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF p.correctionConstant p.correctionLinear
      p.correctionTwo +
    p.correctionReturn • mixedReturnSection kind p

/-- Corrected representative of the old high direction. -/
def mixedReturnCorrectedHigh (kind : MixedReturnFactorPair)
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  mixedReturnFirstProduct kind p + mixedReturnCorrection kind p

/-- The later normalized feedback product. -/
def mixedReturnFeedbackProduct (kind : MixedReturnFactorPair)
    (direction : RationalFeedbackDirection)
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  mixedReturnCorrectedHigh kind p *
    quadraticCoordinateANF p.feedbackConstant p.feedbackLinear direction.two

macro "simp_mixed_return_history" : tactic =>
  `(tactic|
    simp (config := { decide := true }) [
      ZeroOneOffAxisHistoryParameters.vector,
      mixedReturnFeedbackProduct, mixedReturnCorrectedHigh,
      mixedReturnCorrection, mixedReturnSection,
      mixedReturnFirstProduct, mixedReturnShiftedProduct,
      MixedReturnFactorPair.leftTwo, MixedReturnFactorPair.rightTwo,
      RationalFeedbackDirection.two,
      quadraticCoordinateANF,
      ZeroOneOffAxisHistoryParameters.quadraticANFOfForm_correctionTwo_eq_targetANF,
      ZeroOneOffAxisHistoryParameters.correctionCoeff,
      returnHistoryCorrectionDirections, historyJOneCoeff,
      historyJInfinityCoeff,
      rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
      dStarZeroCoeff, dStarOneCoeff,
      quadraticANFOfForm_targetTwo, quadraticANFOfForm_zero,
      linearANFTen, aCoord, bCoord, hankelIndex,
      eval_eq_evalHom, supportAssignmentTen, Fin.sum_univ_succ])

/-- First coordinate of each target-annihilating quadratic row used by the
mixed history certificates. -/
def mixedReturnQuotientFirstPair : Fin 11 → QuadraticIndex 10 :=
  ![
    quadraticPair (aCoord 0) (bCoord 2) (aCoord_ne_bCoord 0 2),
    quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3),
    quadraticPair (aCoord 1) (bCoord 1) (aCoord_ne_bCoord 1 1),
    quadraticPair (aCoord 1) (bCoord 2) (aCoord_ne_bCoord 1 2),
    quadraticPair (aCoord 1) (bCoord 4) (aCoord_ne_bCoord 1 4),
    quadraticPair (aCoord 2) (bCoord 1) (aCoord_ne_bCoord 2 1),
    quadraticPair (aCoord 2) (bCoord 2) (aCoord_ne_bCoord 2 2),
    quadraticPair (aCoord 2) (bCoord 3) (aCoord_ne_bCoord 2 3),
    quadraticPair (aCoord 2) (bCoord 4) (aCoord_ne_bCoord 2 4),
    quadraticPair (aCoord 3) (bCoord 1) (aCoord_ne_bCoord 3 1),
    quadraticPair (aCoord 3) (bCoord 3) (aCoord_ne_bCoord 3 3)
  ]

/-- Second coordinate on the same Hankel anti-diagonal. -/
def mixedReturnQuotientSecondPair : Fin 11 → QuadraticIndex 10 :=
  ![
    quadraticPair (aCoord 2) (bCoord 0) (aCoord_ne_bCoord 2 0),
    quadraticPair (aCoord 3) (bCoord 0) (aCoord_ne_bCoord 3 0),
    quadraticPair (aCoord 2) (bCoord 0) (aCoord_ne_bCoord 2 0),
    quadraticPair (aCoord 3) (bCoord 0) (aCoord_ne_bCoord 3 0),
    quadraticPair (aCoord 4) (bCoord 1) (aCoord_ne_bCoord 4 1),
    quadraticPair (aCoord 3) (bCoord 0) (aCoord_ne_bCoord 3 0),
    quadraticPair (aCoord 4) (bCoord 0) (aCoord_ne_bCoord 4 0),
    quadraticPair (aCoord 4) (bCoord 1) (aCoord_ne_bCoord 4 1),
    quadraticPair (aCoord 4) (bCoord 2) (aCoord_ne_bCoord 4 2),
    quadraticPair (aCoord 4) (bCoord 0) (aCoord_ne_bCoord 4 0),
    quadraticPair (aCoord 4) (bCoord 2) (aCoord_ne_bCoord 4 2)
  ]

/-- Eleven sparse quotient rows covering the union needed by the `R0`,
`R1`, and `RInf` mixed certificates. -/
def mixedReturnQuotientCoordinate (i : Fin 11) : TwoForm →ₗ[F₂] F₂ where
  toFun q := q (mixedReturnQuotientFirstPair i) +
    q (mixedReturnQuotientSecondPair i)
  map_add' q r := by simp only [Pi.add_apply]; ac_rfl
  map_smul' a q := by simp [mul_add]

@[simp] theorem mixedReturnQuotientCoordinate_targetTwo
    (i : Fin 11) (c : TargetCoeff) :
    mixedReturnQuotientCoordinate i (targetTwo c) = 0 := by
  fin_cases i <;>
    simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
      mixedReturnQuotientSecondPair, hankelIndex, CharTwo.add_self_eq_zero]

/-- Equal target quotients annihilate every sparse row used by the mixed
certificates. -/
theorem mixedReturnQuotientCoordinate_add_eq_zero_of_projection
    (q r : TwoForm)
    (hprojection : quadraticQuotientProjection q =
      quadraticQuotientProjection r)
    (i : Fin 11) :
    mixedReturnQuotientCoordinate i q +
        mixedReturnQuotientCoordinate i r = 0 := by
  have hquotientZero : quadraticQuotientProjection (q + r) = 0 := by
    rw [map_add, hprojection]
    rw [← two_smul F₂, show (2 : F₂) = 0 by decide, zero_smul]
  have htarget : q + r ∈ targetTwoSpace :=
    (quadraticQuotientProjection_eq_zero_iff _).1 hquotientZero
  rcases htarget with ⟨c, hc⟩
  calc
    _ = mixedReturnQuotientCoordinate i (q + r) :=
      ((mixedReturnQuotientCoordinate i).map_add q r).symm
    _ = mixedReturnQuotientCoordinate i (targetTwo c) := by
      apply congrArg (mixedReturnQuotientCoordinate i)
      exact hc.symm
    _ = 0 := mixedReturnQuotientCoordinate_targetTwo i c

/-- Convert an exact target return into equality of the genuine quadratic
quotient classes. -/
theorem quadraticQuotientProjection_eq_of_add_eq_target
    (q r : TwoForm) (c : TargetCoeff)
    (h : q + r = targetTwo c) :
    quadraticQuotientProjection q = quadraticQuotientProjection r := by
  have hsum : quadraticQuotientProjection q +
      quadraticQuotientProjection r = 0 := by
    calc
      _ = quadraticQuotientProjection (q + r) :=
        (quadraticQuotientProjection.map_add q r).symm
      _ = quadraticQuotientProjection (targetTwo c) :=
        congrArg quadraticQuotientProjection h
      _ = 0 := quadraticQuotientProjection_targetTwo c
  have hself : quadraticQuotientProjection r +
      quadraticQuotientProjection r = 0 := by
    rw [← two_smul F₂, show (2 : F₂) = 0 by decide, zero_smul]
  calc
    _ = quadraticQuotientProjection q + 0 := (add_zero _).symm
    _ = quadraticQuotientProjection q +
        (quadraticQuotientProjection r +
          quadraticQuotientProjection r) := by rw [hself]
    _ = (quadraticQuotientProjection q +
          quadraticQuotientProjection r) +
        quadraticQuotientProjection r := by ac_rfl
    _ = quadraticQuotientProjection r := by rw [hsum, zero_add]

/-- Once a history certificate annihilates the sparse missing row, an exact
target return cannot have the omitted first-order coordinate. -/
theorem firstOrderMissingFunctional_eq_zero_of_missingCoordinate
    (q r : TwoForm) (c : TargetCoeff)
    (hmissing : returnHistoryMissingCoordinate q +
      returnHistoryMissingCoordinate r = 0)
    (htarget : q + r = targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  calc
    firstOrderMissingFunctional c =
        returnHistoryMissingCoordinate (targetTwo c) :=
      (returnHistoryMissingCoordinate_targetTwo c).symm
    _ = returnHistoryMissingCoordinate (q + r) :=
      congrArg returnHistoryMissingCoordinate htarget.symm
    _ = returnHistoryMissingCoordinate q +
        returnHistoryMissingCoordinate r :=
      returnHistoryMissingCoordinate.map_add q r
    _ = 0 := hmissing

end
end N5
end UnrestrictedBooleanMul
