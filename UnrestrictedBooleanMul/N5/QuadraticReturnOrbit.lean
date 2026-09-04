import UnrestrictedBooleanMul.N5.QuadraticReturnSecant

/-!
# Sparse quartic pivots for quadratic-return orbits

An unpopulated equal-high return cannot be treated as a new decomposable
quadratic direction.  The feedback problem is instead a restricted exterior
kernel calculation: exterior multiplication by the returned affine missing
form must be injective on the old first-order Hankel envelope.

This file begins that calculation with the canonical rational `(0,1)` return
orbit.  The proof uses twelve displayed quartic coordinates and the single
linear equation defining the missing Hankel coset.  It does not enumerate
quadratic forms, Boolean assignments, or circuits.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Quadratic shadow of the canonical `(0,1)` equal-high return.  In input
coordinates it is the three-edge path
`a_2--a_0--b_2` together with `a_2--b_0`. -/
def rationalZeroOneReturnSection : TwoForm :=
  squarefreeWedge (aLinear 0) (aLinear 2) +
    squarefreeWedge (aLinear 0) (bLinear 2) +
      squarefreeWedge (aLinear 2) (bLinear 0)

/-- The canonical `(0,1)` returned affine form has trivial exterior kernel
on the old first-order target envelope. -/
theorem rationalZeroOneReturn_wedge_firstOrder_injective
    (u c : TargetCoeff)
    (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hzero : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + u) +
        rationalZeroOneReturnSection)
      (targetTwo c) = 0) :
    c = 0 := by
  have hcrossReverse (d : TargetCoeff) (i j : Fin 5) :
      ambientTwoCoeff (targetTwo d) (bCoord j) (aCoord i) =
        d (hankelIndex i j) := by
    rw [ambientTwoCoeff_comm]
    exact ambientTwoCoeff_targetTwo_cross d i j
  have hsameA (d : TargetCoeff) (i j : Fin 5) :
      ambientTwoCoeff (targetTwo d) (aCoord i) (aCoord j) = 0 := by
    by_cases hij : i = j
    · subst j
      exact ambientTwoCoeff_same _ _
    · simp [ambientTwoCoeff, hij]
  have hsameB (d : TargetCoeff) (i j : Fin 5) :
      ambientTwoCoeff (targetTwo d) (bCoord i) (bCoord j) = 0 := by
    by_cases hij : i = j
    · subst j
      exact ambientTwoCoeff_same _ _
    · simp [ambientTwoCoeff, hij]
  have hcoord (i j k l : Fin 10) :
      ambientWedgeTwo
          (targetTwo (firstOrderMissingCoeff + u) +
            rationalZeroOneReturnSection)
          (targetTwo c) i j k l = 0 :=
    congrFun (congrFun (congrFun (congrFun hzero i) j) k) l
  have hc1 := hcoord (aCoord 0) (aCoord 2) (aCoord 1) (bCoord 0)
  have hc2 := hcoord (aCoord 0) (aCoord 2) (aCoord 1) (bCoord 1)
  have hc3 := hcoord (aCoord 0) (aCoord 2) (aCoord 1) (bCoord 2)
  have hc4 := hcoord (aCoord 0) (aCoord 2) (aCoord 1) (bCoord 3)
  have hc5 := hcoord (aCoord 0) (aCoord 2) (aCoord 1) (bCoord 4)
  have hc6 := hcoord (aCoord 0) (aCoord 2) (aCoord 3) (bCoord 3)
  have hc7 := hcoord (aCoord 0) (aCoord 2) (aCoord 3) (bCoord 4)
  have hc8 := hcoord (aCoord 0) (aCoord 2) (aCoord 4) (bCoord 4)
  simp [ambientWedgeTwo, rationalZeroOneReturnSection,
    ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
    ambientTwoCoeff_targetTwo_cross,
    aLinear, bLinear, Pi.basisFun, hankelIndex,
    aCoord_ne_bCoord, bCoord_ne_aCoord, hcrossReverse,
    hsameA, hsameB] at hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8
  have hd2 := hcoord (aCoord 0) (bCoord 0) (aCoord 1) (bCoord 1)
  have hd3 := hcoord (aCoord 0) (bCoord 0) (aCoord 1) (bCoord 2)
  have hd5 := hcoord (aCoord 0) (bCoord 0) (aCoord 1) (bCoord 4)
  have hd6 := hcoord (aCoord 0) (bCoord 0) (aCoord 2) (bCoord 4)
  simp [ambientWedgeTwo, rationalZeroOneReturnSection,
    ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
    ambientTwoCoeff_targetTwo_cross,
    aLinear, bLinear, Pi.basisFun, hankelIndex,
    aCoord_ne_bCoord, bCoord_ne_aCoord, hcrossReverse,
    hsameA, hsameB,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8] at hd2 hd3 hd5 hd6
  have hu0 : firstOrderMissingFunctional u = 0 :=
    (mem_firstOrderEnvelopeCoeffSpace u).1 hu
  have hmissing :
      (firstOrderMissingCoeff + u) 2 +
          (firstOrderMissingCoeff + u) 3 +
          (firstOrderMissingCoeff + u) 5 +
          (firstOrderMissingCoeff + u) 6 = 1 := by
    have hfunctional : firstOrderMissingFunctional
        (firstOrderMissingCoeff + u) = 1 := by
      rw [map_add, firstOrderMissingFunctional_missing, hu0, add_zero]
    exact hfunctional
  have hc0 : c 0 = 0 := by
    by_contra hc0ne
    have h2 := hd2.resolve_left hc0ne
    have h3 := hd3.resolve_left hc0ne
    have h5 := hd5.resolve_left hc0ne
    have h6 := hd6.resolve_left hc0ne
    have hz2 : (firstOrderMissingCoeff + u) 2 = 0 := by simp [h2]
    have hz3 : (firstOrderMissingCoeff + u) 3 = 0 := by simp [h3]
    have hz5 : (firstOrderMissingCoeff + u) 5 = 0 := by simp [h5]
    have hz6 : (firstOrderMissingCoeff + u) 6 = 0 := by simp [h6]
    rw [hz2, hz3, hz5, hz6] at hmissing
    simp at hmissing
  funext i
  fin_cases i <;> assumption

/-- Quadratic shadow of the canonical `(1,1)` equal-high return.  It differs
from the `(0,1)` shadow only by the old rational target at zero. -/
def rationalOneOneReturnSection : TwoForm :=
  rationalZeroOneReturnSection + targetTwo rZeroCoeff

/-- The `(1,1)` orbit inherits the `(0,1)` target-kernel certificate by
absorbing its rational target translate into the first-order envelope. -/
theorem rationalOneOneReturn_wedge_firstOrder_injective
    (u c : TargetCoeff)
    (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hzero : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + u) +
        rationalOneOneReturnSection)
      (targetTwo c) = 0) :
    c = 0 := by
  have hrZero : rZeroCoeff ∈ firstOrderEnvelopeCoeffSpace := by
    rw [mem_firstOrderEnvelopeCoeffSpace]
    simp [firstOrderMissingFunctional, rZeroCoeff]
  have hu' : u + rZeroCoeff ∈ firstOrderEnvelopeCoeffSpace :=
    firstOrderEnvelopeCoeffSpace.add_mem hu hrZero
  apply rationalZeroOneReturn_wedge_firstOrder_injective
      (u + rZeroCoeff) c hu'
  have hfirst :
      targetTwo (firstOrderMissingCoeff + (u + rZeroCoeff)) +
          rationalZeroOneReturnSection =
        targetTwo (firstOrderMissingCoeff + u) +
          rationalOneOneReturnSection := by
    rw [rationalOneOneReturnSection]
    change targetTwoLinear
          (firstOrderMissingCoeff + (u + rZeroCoeff)) +
          rationalZeroOneReturnSection =
        targetTwoLinear (firstOrderMissingCoeff + u) +
          (rationalZeroOneReturnSection + targetTwoLinear rZeroCoeff)
    rw [show targetTwoLinear
          (firstOrderMissingCoeff + (u + rZeroCoeff)) =
        targetTwoLinear (firstOrderMissingCoeff + u) +
          targetTwoLinear rZeroCoeff by
      rw [← targetTwoLinear.map_add]
      apply congrArg targetTwoLinear
      ac_rfl]
    abel
  rw [hfirst]
  exact hzero

/-- Quadratic shadow of the canonical `(1,2)` equal-high return.  Its
same-side part has alternating rank four; the remaining summand is an old
rational target translate. -/
def rationalOneTwoReturnSection : TwoForm :=
  squarefreeWedge (aLinear 0) (aLinear 1 + aLinear 3 + aLinear 4) +
    squarefreeWedge (aLinear 1) (aLinear 2 + aLinear 3 + aLinear 4) +
      targetTwo (rZeroCoeff + rOneCoeff)

/-- Exterior multiplication by the `(1,2)` return is injective on the full
Hankel target.  Nine `AAA B` coordinates see only its rank-four same-side
part and kill all nine Hankel coefficients. -/
theorem rationalOneTwoReturn_wedge_target_injective
    (d c : TargetCoeff)
    (hzero : ambientWedgeTwo
      (targetTwo d + rationalOneTwoReturnSection)
      (targetTwo c) = 0) :
    c = 0 := by
  have hcrossReverse (e : TargetCoeff) (i j : Fin 5) :
      ambientTwoCoeff (targetTwo e) (bCoord j) (aCoord i) =
        e (hankelIndex i j) := by
    rw [ambientTwoCoeff_comm]
    exact ambientTwoCoeff_targetTwo_cross e i j
  have hsameA (e : TargetCoeff) (i j : Fin 5) :
      ambientTwoCoeff (targetTwo e) (aCoord i) (aCoord j) = 0 := by
    by_cases hij : i = j
    · subst j
      exact ambientTwoCoeff_same _ _
    · simp [ambientTwoCoeff, hij]
  have hcoord (i j k l : Fin 10) :
      ambientWedgeTwo
          (targetTwo d + rationalOneTwoReturnSection)
          (targetTwo c) i j k l = 0 :=
    congrFun (congrFun (congrFun (congrFun hzero i) j) k) l
  have h2 := hcoord (aCoord 0) (aCoord 2) (aCoord 3) (bCoord 0)
  have h0 := hcoord (aCoord 0) (aCoord 1) (aCoord 2) (bCoord 0)
  have h3 := hcoord (aCoord 1) (aCoord 2) (aCoord 3) (bCoord 0)
  have h1 := hcoord (aCoord 0) (aCoord 1) (aCoord 3) (bCoord 0)
  have h4 := hcoord (aCoord 0) (aCoord 1) (aCoord 4) (bCoord 0)
  have h6 := hcoord (aCoord 0) (aCoord 2) (aCoord 3) (bCoord 4)
  have h7 := hcoord (aCoord 1) (aCoord 2) (aCoord 3) (bCoord 4)
  have h5 := hcoord (aCoord 0) (aCoord 1) (aCoord 3) (bCoord 4)
  have h8 := hcoord (aCoord 0) (aCoord 1) (aCoord 4) (bCoord 4)
  simp [ambientWedgeTwo, rationalOneTwoReturnSection,
    ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
    ambientTwoCoeff_targetTwo_cross,
    aLinear, Pi.basisFun, hankelIndex,
    aCoord_ne_bCoord, bCoord_ne_aCoord, hcrossReverse,
    hsameA] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  funext i
  fin_cases i <;> simp_all

/-- Quadratic shadow of the canonical `(1,3)` equal-high return.  Again the
same-side part has alternating rank four. -/
def rationalOneThreeReturnSection : TwoForm :=
  squarefreeWedge (aLinear 0 + aLinear 1) (aLinear 2) +
    squarefreeWedge (aLinear 0 + aLinear 2) (aLinear 3 + aLinear 4) +
      targetTwo (rZeroCoeff + rOneCoeff)

/-- Exterior multiplication by the `(1,3)` return is injective on the full
Hankel target, by a second nine-coordinate rank-four pivot. -/
theorem rationalOneThreeReturn_wedge_target_injective
    (d c : TargetCoeff)
    (hzero : ambientWedgeTwo
      (targetTwo d + rationalOneThreeReturnSection)
      (targetTwo c) = 0) :
    c = 0 := by
  have hcrossReverse (e : TargetCoeff) (i j : Fin 5) :
      ambientTwoCoeff (targetTwo e) (bCoord j) (aCoord i) =
        e (hankelIndex i j) := by
    rw [ambientTwoCoeff_comm]
    exact ambientTwoCoeff_targetTwo_cross e i j
  have hsameA (e : TargetCoeff) (i j : Fin 5) :
      ambientTwoCoeff (targetTwo e) (aCoord i) (aCoord j) = 0 := by
    by_cases hij : i = j
    · subst j
      exact ambientTwoCoeff_same _ _
    · simp [ambientTwoCoeff, hij]
  have hcoord (i j k l : Fin 10) :
      ambientWedgeTwo
          (targetTwo d + rationalOneThreeReturnSection)
          (targetTwo c) i j k l = 0 :=
    congrFun (congrFun (congrFun (congrFun hzero i) j) k) l
  have h1 := hcoord (aCoord 0) (aCoord 1) (aCoord 3) (bCoord 0)
  have h0 := hcoord (aCoord 0) (aCoord 1) (aCoord 2) (bCoord 0)
  have h3 := hcoord (aCoord 1) (aCoord 2) (aCoord 3) (bCoord 0)
  have h4 := hcoord (aCoord 0) (aCoord 3) (aCoord 4) (bCoord 0)
  have h2 := hcoord (aCoord 0) (aCoord 2) (aCoord 3) (bCoord 0)
  have h5 := hcoord (aCoord 0) (aCoord 1) (aCoord 3) (bCoord 4)
  have h7 := hcoord (aCoord 1) (aCoord 2) (aCoord 3) (bCoord 4)
  have h8 := hcoord (aCoord 0) (aCoord 3) (aCoord 4) (bCoord 4)
  have h6 := hcoord (aCoord 0) (aCoord 2) (aCoord 3) (bCoord 4)
  simp [ambientWedgeTwo, rationalOneThreeReturnSection,
    ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
    ambientTwoCoeff_targetTwo_cross,
    aLinear, Pi.basisFun, hankelIndex,
    aCoord_ne_bCoord, bCoord_ne_aCoord, hcrossReverse,
    hsameA] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  funext i
  fin_cases i <;> simp_all

/-- The four simultaneous rational-plane orbit types for unpopulated
equal-high quadratic returns. -/
inductive RationalReturnOrbit where
  | zeroOne
  | oneOne
  | oneTwo
  | oneThree
  deriving DecidableEq, Fintype

/-- Canonical returned section attached to a rational-plane orbit type. -/
def rationalReturnOrbitSection : RationalReturnOrbit → TwoForm
  | .zeroOne => rationalZeroOneReturnSection
  | .oneOne => rationalOneOneReturnSection
  | .oneTwo => rationalOneTwoReturnSection
  | .oneThree => rationalOneThreeReturnSection

/-- Every canonical rational return orbit has trivial exterior kernel on the
old Hankel target. -/
theorem rationalReturnOrbit_wedge_firstOrder_injective
    (orbit : RationalReturnOrbit) (u c : TargetCoeff)
    (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hzero : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + u) +
        rationalReturnOrbitSection orbit)
      (targetTwo c) = 0) :
    c = 0 := by
  cases orbit with
  | zeroOne =>
      exact rationalZeroOneReturn_wedge_firstOrder_injective u c hu hzero
  | oneOne =>
      exact rationalOneOneReturn_wedge_firstOrder_injective u c hu hzero
  | oneTwo =>
      exact rationalOneTwoReturn_wedge_target_injective
        (firstOrderMissingCoeff + u) c hzero
  | oneThree =>
      exact rationalOneThreeReturn_wedge_target_injective
        (firstOrderMissingCoeff + u) c hzero

end
end N5
end UnrestrictedBooleanMul
