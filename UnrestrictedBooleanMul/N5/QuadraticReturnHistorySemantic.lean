import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryModel
import UnrestrictedBooleanMul.N5.CubicSemantic

/-!
# Semantic bridge for the rational-return history certificate

This module identifies the named polynomial history parameters with the
literal ANF products used by the circuit proof.  It is intentionally built
one projection layer at a time so every generated constraint has an auditable
algebraic source.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The first high product in the canonical `(0,1)` factor-pair model. -/
def ZeroOneOffAxisHistoryParameters.firstProduct
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF 0 p.ell 0 *
    quadraticCoordinateANF 0 p.m (targetTwo rZeroCoeff)

/-- The equal-high comparison product, obtained by shifting both linear
parts without changing their quadratic parts. -/
def ZeroOneOffAxisHistoryParameters.shiftedProduct
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF 0 (p.ell + p.leftShift) 0 *
    quadraticCoordinateANF 0 (p.m + p.rightShift)
      (targetTwo rZeroCoeff)

/-- The quadratic return candidate is the sum of the two equal-high
products. -/
def ZeroOneOffAxisHistoryParameters.returned
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  p.firstProduct + p.shiftedProduct

/-- The complete cubic projection of the returned product depends only on
the left linear shift: the original linear part occurs twice and cancels. -/
theorem ZeroOneOffAxisHistoryParameters.returned_cubic_eq
    (p : ZeroOneOffAxisHistoryParameters) :
    anfThreeProjectionTen p.returned =
      ambientVectorWedgeTwo p.leftShift (targetTwo rZeroCoeff) := by
  have hzero (i j : Fin 10) :
      ambientTwoCoeff (0 : TwoForm) i j = 0 := by
    simp [ambientTwoCoeff]
  rw [ZeroOneOffAxisHistoryParameters.returned, map_add,
    ZeroOneOffAxisHistoryParameters.firstProduct,
    ZeroOneOffAxisHistoryParameters.shiftedProduct,
    anfThreeProjectionTen_quadraticCoordinateANF_mul,
    anfThreeProjectionTen_quadraticCoordinateANF_mul]
  funext i j k
  simp [exactLowProductCubic, quadraticOverlapCubic, factorPlaneCubic,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN, quadraticANFOfForm, hzero]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The first selected return-high polynomial is exactly the `0x023` cubic
coefficient of the literal returned product. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_zero_eq_returned_cubic
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 0 =
      anfThreeProjectionTen p.returned 0 1 5 := by
  have h15 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (1 : Fin 10) 5 = 0 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 1) (bCoord 0) = 0
    simp [rZeroCoeff, hankelIndex]
  have h05 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 5 = 1 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 0) = 1
    simp [rZeroCoeff, hankelIndex]
  have h01 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 1 = 0 := by
    rw [ambientTwoCoeff,
      dif_neg (show (0 : Fin 10) ≠ 1 by decide)]
    change targetTwo rZeroCoeff
      (quadraticPair (aCoord 0) (aCoord 1) (by decide)) = 0
    exact targetTwo_sameA rZeroCoeff 0 1 (by decide)
  rw [p.returned_cubic_eq]
  simp [zeroOneRawConstraint, ZeroOneOffAxisHistoryParameters.vector,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    h15, h05, h01]

/-- The second selected return-high polynomial is the `0x031` cubic
coefficient of the literal returned product. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_one_eq_returned_cubic
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 1 =
      anfThreeProjectionTen p.returned 0 4 5 := by
  have h45 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (4 : Fin 10) 5 = 0 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 4) (bCoord 0) = 0
    simp [rZeroCoeff, hankelIndex]
  have h05 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 5 = 1 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 0) = 1
    simp [rZeroCoeff, hankelIndex]
  have h04 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 4 = 0 := by
    rw [ambientTwoCoeff,
      dif_neg (show (0 : Fin 10) ≠ 4 by decide)]
    change targetTwo rZeroCoeff
      (quadraticPair (aCoord 0) (aCoord 4) (by decide)) = 0
    exact targetTwo_sameA rZeroCoeff 0 4 (by decide)
  rw [p.returned_cubic_eq]
  simp [zeroOneRawConstraint, ZeroOneOffAxisHistoryParameters.vector,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    h45, h05, h04]

/-- The third selected return-high polynomial is the `0x061` cubic
coefficient of the literal returned product. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_two_eq_returned_cubic
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 2 =
      anfThreeProjectionTen p.returned 0 5 6 := by
  have h56 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (5 : Fin 10) 6 = 0 := by
    rw [ambientTwoCoeff,
      dif_neg (show (5 : Fin 10) ≠ 6 by decide)]
    change targetTwo rZeroCoeff
      (quadraticPair (bCoord 0) (bCoord 1) (by decide)) = 0
    exact targetTwo_sameB rZeroCoeff 0 1 (by decide)
  have h06 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 6 = 0 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 1) = 0
    simp [rZeroCoeff, hankelIndex]
  have h05 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 5 = 1 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 0) = 1
    simp [rZeroCoeff, hankelIndex]
  rw [p.returned_cubic_eq]
  simp [zeroOneRawConstraint, ZeroOneOffAxisHistoryParameters.vector,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    h56, h06, h05]

/-- The fourth selected return-high polynomial is the `0x0a1` cubic
coefficient of the literal returned product. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_three_eq_returned_cubic
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 3 =
      anfThreeProjectionTen p.returned 0 5 7 := by
  have h57 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (5 : Fin 10) 7 = 0 := by
    rw [ambientTwoCoeff,
      dif_neg (show (5 : Fin 10) ≠ 7 by decide)]
    change targetTwo rZeroCoeff
      (quadraticPair (bCoord 0) (bCoord 2) (by decide)) = 0
    exact targetTwo_sameB rZeroCoeff 0 2 (by decide)
  have h07 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 7 = 0 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 2) = 0
    simp [rZeroCoeff, hankelIndex]
  have h05 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 5 = 1 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 0) = 1
    simp [rZeroCoeff, hankelIndex]
  rw [p.returned_cubic_eq]
  simp [zeroOneRawConstraint, ZeroOneOffAxisHistoryParameters.vector,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    h57, h07, h05]

/-- A literal quadratic return supplies the first four equations consumed by
the raw history certificate. -/
theorem ZeroOneOffAxisHistoryParameters.returnHighConstraints_eq_zero
    (p : ZeroOneOffAxisHistoryParameters)
    (hquadratic : p.returned ∈ N4.quadraticANFSpace 10) :
    zeroOneRawConstraint p.vector 0 = 0 ∧
    zeroOneRawConstraint p.vector 1 = 0 ∧
    zeroOneRawConstraint p.vector 2 = 0 ∧
    zeroOneRawConstraint p.vector 3 = 0 := by
  have hcubic := anfThreeProjectionTen_eq_zero_of_quadratic hquadratic
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p.constraint_zero_eq_returned_cubic]
    exact congrFun (congrFun (congrFun hcubic 0) 1) 5
  · rw [p.constraint_one_eq_returned_cubic]
    exact congrFun (congrFun (congrFun hcubic 0) 4) 5
  · rw [p.constraint_two_eq_returned_cubic]
    exact congrFun (congrFun (congrFun hcubic 0) 5) 6
  · rw [p.constraint_three_eq_returned_cubic]
    exact congrFun (congrFun (congrFun hcubic 0) 5) 7

end
end N5
end UnrestrictedBooleanMul
