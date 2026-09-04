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
    aLinear, bLinear, Pi.basisFun, hankelIndex, ambientTwoCoeff] at hc1 hc2
      hc3 hc4 hc5 hc6 hc7 hc8
  have hd2 := hcoord (aCoord 0) (bCoord 0) (aCoord 1) (bCoord 1)
  have hd3 := hcoord (aCoord 0) (bCoord 0) (aCoord 1) (bCoord 2)
  have hd5 := hcoord (aCoord 0) (bCoord 0) (aCoord 1) (bCoord 4)
  have hd6 := hcoord (aCoord 0) (bCoord 0) (aCoord 2) (bCoord 4)
  simp [ambientWedgeTwo, rationalZeroOneReturnSection,
    ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
    aLinear, bLinear, Pi.basisFun, hankelIndex, ambientTwoCoeff,
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
    calc
      c 0 = c 0 * 1 := by ring
      _ = c 0 * ((firstOrderMissingCoeff + u) 2 +
          (firstOrderMissingCoeff + u) 3 +
          (firstOrderMissingCoeff + u) 5 +
          (firstOrderMissingCoeff + u) 6) := by rw [hmissing]
      _ = 0 := by
        rw [mul_add, mul_add, mul_add, hd2, hd3, hd5, hd6]
        simp
  funext i
  fin_cases i <;> assumption

end
end N5
end UnrestrictedBooleanMul
