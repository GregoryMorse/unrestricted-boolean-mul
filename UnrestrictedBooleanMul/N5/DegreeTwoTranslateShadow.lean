import UnrestrictedBooleanMul.N5.IndependentShadow

/-!
# The non-rational cubic kernel in the first-order envelope

The exact first-order envelope contains one non-rigid independent plane that
does not contain a rational value direction.  It is a rationally adjusted
translate of the degree-two place.  This module solves its four-dimensional
cubic kernel by sparse exterior-coordinate pivots and derives its Boolean
quadratic-shadow correction algebraically.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- First direction of the unique non-rational non-rigid plane, in target
coefficients. -/
def degreeTwoTranslateLeftCoeff : TargetCoeff :=
  rOneCoeff + rInfinityCoeff + dStarZeroCoeff

/-- Second direction of the unique non-rational non-rigid plane. -/
def degreeTwoTranslateRightCoeff : TargetCoeff :=
  rZeroCoeff + rOneCoeff + dStarOneCoeff

def degreeTwoTranslateLeftTwo : TwoForm :=
  targetTwo degreeTwoTranslateLeftCoeff

def degreeTwoTranslateRightTwo : TwoForm :=
  targetTwo degreeTwoTranslateRightCoeff

private def translateXA₀ : LinearForm :=
  aLinear 0 + aLinear 1 + aLinear 3 + aLinear 4

private def translateXA₁ : LinearForm :=
  aLinear 0 + aLinear 2 + aLinear 3

private def translateYA₀ : LinearForm :=
  aLinear 0 + aLinear 2 + aLinear 3

private def translateYA₁ : LinearForm :=
  aLinear 1 + aLinear 2 + aLinear 4

private def translateXB₀ : LinearForm :=
  bLinear 0 + bLinear 1 + bLinear 3 + bLinear 4

private def translateXB₁ : LinearForm :=
  bLinear 0 + bLinear 2 + bLinear 3

private def translateYB₀ : LinearForm :=
  bLinear 0 + bLinear 2 + bLinear 3

private def translateYB₁ : LinearForm :=
  bLinear 1 + bLinear 2 + bLinear 4

/-- Sparse solution of the four-dimensional cubic kernel on the adjusted
degree-two plane.  The `a` and `b` blocks each leave exactly two scalar
parameters; no assignments of the ten ambient variables are enumerated. -/
theorem degreeTwoTranslate_cubic_syzygy (x y : LinearForm)
    (h : factorPlaneCubic x y degreeTwoTranslateLeftTwo
      degreeTwoTranslateRightTwo = 0) :
    ∃ p q r s : F₂,
      x = p • translateXA₀ + q • translateXA₁ +
          r • translateXB₀ + s • translateXB₁ ∧
      y = p • translateYA₀ + q • translateYA₁ +
          r • translateYB₀ + s • translateYB₁ := by
  have hc (i j k : Fin 10) := congrFun (congrFun (congrFun h i) j) k
  have h015 := hc (aCoord 0) (aCoord 1) (bCoord 0)
  have h016 := hc (aCoord 0) (aCoord 1) (bCoord 1)
  have h025 := hc (aCoord 0) (aCoord 2) (bCoord 0)
  have h026 := hc (aCoord 0) (aCoord 2) (bCoord 1)
  have h035 := hc (aCoord 0) (aCoord 3) (bCoord 0)
  have h036 := hc (aCoord 0) (aCoord 3) (bCoord 1)
  have h045 := hc (aCoord 0) (aCoord 4) (bCoord 0)
  have h046 := hc (aCoord 0) (aCoord 4) (bCoord 1)
  have h056 := hc (aCoord 0) (bCoord 0) (bCoord 1)
  have h057 := hc (aCoord 0) (bCoord 0) (bCoord 2)
  have h058 := hc (aCoord 0) (bCoord 0) (bCoord 3)
  have h059 := hc (aCoord 0) (bCoord 0) (bCoord 4)
  have h067 := hc (aCoord 0) (bCoord 1) (bCoord 2)
  have h068 := hc (aCoord 0) (bCoord 1) (bCoord 3)
  have h069 := hc (aCoord 0) (bCoord 1) (bCoord 4)
  have h156 := hc (aCoord 1) (bCoord 0) (bCoord 1)
  simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    degreeTwoTranslateLeftTwo, degreeTwoTranslateRightTwo,
    degreeTwoTranslateLeftCoeff, degreeTwoTranslateRightCoeff,
    ambientTwoCoeff, rZeroCoeff, rOneCoeff, rInfinityCoeff,
    dStarZeroCoeff, dStarOneCoeff, hankelIndex, aCoord_ne_bCoord] at h015 h016 h025 h026 h035 h036 h045 h046 h056 h057 h058 h059 h067 h068 h069 h156
  ring_nf at h015 h016 h025 h026 h035 h036 h045 h046 h056 h057 h058 h059 h067 h068 h069 h156
  have htwo : (2 : F₂) = 0 := by decide
  simp [htwo] at h015 h016 h025 h026 h035 h036 h045 h046 h056 h057 h058 h059 h067 h068 h069 h156
  have hxA0 : x (aCoord 0) = x (aCoord 1) + x (aCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h015 + h016 + h025 + h026
  have hxA3 : x (aCoord 3) = x (aCoord 1) + x (aCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h015 + h016 + h025 + h026 + h035 + h036
  have hxA4 : x (aCoord 4) = x (aCoord 1) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h015 + h016 + h045 + h046
  have hyA0 : y (aCoord 0) = x (aCoord 1) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h015 + h016
  have hyA1 : y (aCoord 1) = x (aCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h015 + h025 + h026
  have hyA2 : y (aCoord 2) = x (aCoord 1) + x (aCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h015 + h016 + h026
  have hyA3 : y (aCoord 3) = x (aCoord 1) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h015 + h016 + h035
  have hyA4 : y (aCoord 4) = x (aCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h025 + h026 + h045
  have hxB0 : x (bCoord 0) = x (bCoord 1) + x (bCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h057 + h067
  have hxB3 : x (bCoord 3) = x (bCoord 1) + x (bCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h056 + h057 + h058 + h067 + h068
  have hxB4 : x (bCoord 4) = x (bCoord 1) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h056 + h059 + h069
  have hyB0 : y (bCoord 0) = x (bCoord 1) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h056 + h156
  have hyB1 : y (bCoord 1) = x (bCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h057 + h067 + h156
  have hyB2 : y (bCoord 2) = x (bCoord 1) + x (bCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h067
  have hyB3 : y (bCoord 3) = x (bCoord 1) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h056 + h058 + h156
  have hyB4 : y (bCoord 4) = x (bCoord 2) := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2]))
      h056 + h057 + h059 + h067 + h156
  have hx0 : x 0 = x 1 + x 2 := by simpa [aCoord] using hxA0
  have hx3 : x 3 = x 1 + x 2 := by simpa [aCoord] using hxA3
  have hx4 : x 4 = x 1 := by simpa [aCoord] using hxA4
  have hx5 : x 5 = x 6 + x 7 := by simpa [bCoord] using hxB0
  have hx8 : x 8 = x 6 + x 7 := by simpa [bCoord] using hxB3
  have hx9 : x 9 = x 6 := by simpa [bCoord] using hxB4
  have hy0 : y 0 = x 1 := by simpa [aCoord] using hyA0
  have hy1 : y 1 = x 2 := by simpa [aCoord] using hyA1
  have hy2 : y 2 = x 1 + x 2 := by simpa [aCoord] using hyA2
  have hy3 : y 3 = x 1 := by simpa [aCoord] using hyA3
  have hy4 : y 4 = x 2 := by simpa [aCoord] using hyA4
  have hy5 : y 5 = x 6 := by simpa [bCoord] using hyB0
  have hy6 : y 6 = x 7 := by simpa [bCoord] using hyB1
  have hy7 : y 7 = x 6 + x 7 := by simpa [bCoord] using hyB2
  have hy8 : y 8 = x 6 := by simpa [bCoord] using hyB3
  have hy9 : y 9 = x 7 := by simpa [bCoord] using hyB4
  refine ⟨x (aCoord 1), x (aCoord 2),
    x (bCoord 1), x (bCoord 2), ?_, ?_⟩
  · funext i
    fin_cases i <;>
      simp [translateXA₀, translateXA₁, translateXB₀, translateXB₁,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        hx0, hx3, hx4, hx5, hx8, hx9]
  · funext i
    fin_cases i <;>
      simp [translateYA₀, translateYA₁, translateYB₀, translateYB₁,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9]

end

end N5
end UnrestrictedBooleanMul
