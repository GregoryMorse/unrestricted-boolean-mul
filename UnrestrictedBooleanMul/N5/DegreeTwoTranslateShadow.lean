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

set_option linter.unusedSimpArgs false

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
  ![1, 1, 0, 1, 1, 0, 0, 0, 0, 0]

private def translateXA₁ : LinearForm :=
  ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0]

private def translateYA₀ : LinearForm :=
  ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0]

private def translateYA₁ : LinearForm :=
  ![0, 1, 1, 0, 1, 0, 0, 0, 0, 0]

private def translateXB₀ : LinearForm :=
  ![0, 0, 0, 0, 0, 1, 1, 0, 1, 1]

private def translateXB₁ : LinearForm :=
  ![0, 0, 0, 0, 0, 1, 0, 1, 1, 0]

private def translateYB₀ : LinearForm :=
  ![0, 0, 0, 0, 0, 1, 0, 1, 1, 0]

private def translateYB₁ : LinearForm :=
  ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1]

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

private def translateEnvelope64 : TwoForm :=
  targetTwo ![1, 1, 0, 1, 1, 0, 1, 1, 0]

private def translateEnvelopeF7 : TwoForm :=
  targetTwo ![1, 0, 1, 1, 0, 1, 1, 0, 1]

private def translateEnvelope93 : TwoForm :=
  targetTwo ![0, 1, 1, 0, 1, 1, 0, 1, 1]

private theorem translateEnvelope64_mem :
    translateEnvelope64 ∈ firstOrderEnvelopeTwoSpace := by
  refine ⟨![1, 1, 0, 1, 1, 0, 1, 1, 0], ?_, rfl⟩
  apply (mem_firstOrderEnvelopeCoeffSpace _).2
  decide

private theorem translateEnvelopeF7_mem :
    translateEnvelopeF7 ∈ firstOrderEnvelopeTwoSpace := by
  refine ⟨![1, 0, 1, 1, 0, 1, 1, 0, 1], ?_, rfl⟩
  apply (mem_firstOrderEnvelopeCoeffSpace _).2
  decide

private theorem translateEnvelope93_mem :
    translateEnvelope93 ∈ firstOrderEnvelopeTwoSpace := by
  refine ⟨![0, 1, 1, 0, 1, 1, 0, 1, 1], ?_, rfl⟩
  apply (mem_firstOrderEnvelopeCoeffSpace _).2
  decide

private def translateZ1 : LinearForm :=
  ![1, 0, 1, 1, 0, 0, 1, 1, 0, 1]

private def translateZ2 : LinearForm :=
  ![0, 1, 1, 0, 1, 1, 0, 1, 1, 0]

private def translateZ3 : LinearForm :=
  ![1, 0, 1, 1, 0, 1, 1, 0, 1, 1]

private def translateZ4 : LinearForm :=
  ![1, 1, 0, 1, 1, 1, 0, 1, 1, 0]

private def translateZ5 : LinearForm :=
  ![0, 1, 1, 0, 1, 0, 1, 1, 0, 1]

private def translateBlockP : Fin 5 → F₂ := ![1, 1, 0, 1, 1]
private def translateBlockQ : Fin 5 → F₂ := ![1, 0, 1, 1, 0]
private def translateBlockR : Fin 5 → F₂ := ![0, 1, 1, 0, 1]

private theorem degreeTwoTranslateLeftCoeff_eq_vector :
    degreeTwoTranslateLeftCoeff = ![1, 1, 0, 1, 1, 0, 1, 1, 0] := by
  funext i
  fin_cases i <;>
    simp [degreeTwoTranslateLeftCoeff, rOneCoeff, rInfinityCoeff,
      dStarZeroCoeff]

private theorem degreeTwoTranslateRightCoeff_eq_vector :
    degreeTwoTranslateRightCoeff = ![0, 1, 1, 0, 1, 1, 0, 1, 1] := by
  funext i
  fin_cases i <;>
    simp [degreeTwoTranslateRightCoeff, rZeroCoeff, rOneCoeff, dStarOneCoeff]

@[simp] private theorem translateXA₀_a (i : Fin 5) :
    translateXA₀ (aCoord i) = translateBlockP i := by
  fin_cases i <;> rfl

@[simp] private theorem translateXA₀_b (i : Fin 5) :
    translateXA₀ (bCoord i) = 0 := by
  fin_cases i <;> rfl

@[simp] private theorem translateXA₁_a (i : Fin 5) :
    translateXA₁ (aCoord i) = translateBlockQ i := by
  fin_cases i <;> rfl

@[simp] private theorem translateXA₁_b (i : Fin 5) :
    translateXA₁ (bCoord i) = 0 := by
  fin_cases i <;> rfl

@[simp] private theorem translateYA₀_a (i : Fin 5) :
    translateYA₀ (aCoord i) = translateBlockQ i := by
  fin_cases i <;> rfl

@[simp] private theorem translateYA₀_b (i : Fin 5) :
    translateYA₀ (bCoord i) = 0 := by
  fin_cases i <;> rfl

@[simp] private theorem translateYA₁_a (i : Fin 5) :
    translateYA₁ (aCoord i) = translateBlockR i := by
  fin_cases i <;> rfl

@[simp] private theorem translateYA₁_b (i : Fin 5) :
    translateYA₁ (bCoord i) = 0 := by
  fin_cases i <;> rfl

@[simp] private theorem translateXB₀_a (i : Fin 5) :
    translateXB₀ (aCoord i) = 0 := by
  fin_cases i <;> rfl

@[simp] private theorem translateXB₀_b (i : Fin 5) :
    translateXB₀ (bCoord i) = translateBlockP i := by
  fin_cases i <;> rfl

@[simp] private theorem translateXB₁_a (i : Fin 5) :
    translateXB₁ (aCoord i) = 0 := by
  fin_cases i <;> rfl

@[simp] private theorem translateXB₁_b (i : Fin 5) :
    translateXB₁ (bCoord i) = translateBlockQ i := by
  fin_cases i <;> rfl

@[simp] private theorem translateYB₀_a (i : Fin 5) :
    translateYB₀ (aCoord i) = 0 := by
  fin_cases i <;> rfl

@[simp] private theorem translateYB₀_b (i : Fin 5) :
    translateYB₀ (bCoord i) = translateBlockQ i := by
  fin_cases i <;> rfl

@[simp] private theorem translateYB₁_a (i : Fin 5) :
    translateYB₁ (aCoord i) = 0 := by
  fin_cases i <;> rfl

@[simp] private theorem translateYB₁_b (i : Fin 5) :
    translateYB₁ (bCoord i) = translateBlockR i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ1_a (i : Fin 5) :
    translateZ1 (aCoord i) = translateBlockQ i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ1_b (i : Fin 5) :
    translateZ1 (bCoord i) = translateBlockR i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ2_a (i : Fin 5) :
    translateZ2 (aCoord i) = translateBlockR i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ2_b (i : Fin 5) :
    translateZ2 (bCoord i) = translateBlockQ i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ3_a (i : Fin 5) :
    translateZ3 (aCoord i) = translateBlockQ i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ3_b (i : Fin 5) :
    translateZ3 (bCoord i) = translateBlockP i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ4_a (i : Fin 5) :
    translateZ4 (aCoord i) = translateBlockP i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ4_b (i : Fin 5) :
    translateZ4 (bCoord i) = translateBlockQ i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ5_a (i : Fin 5) :
    translateZ5 (aCoord i) = translateBlockR i := by
  fin_cases i <;> rfl

@[simp] private theorem translateZ5_b (i : Fin 5) :
    translateZ5 (bCoord i) = translateBlockR i := by
  fin_cases i <;> rfl

/-- The sixteen scalar points of the cubic kernel use only three old-envelope
corrections and five auxiliary linear forms.  This is a table of algebraic
kernel parameters, not an enumeration of the ten Boolean inputs. -/
private def degreeTwoTranslateCorrectionWitness
    (p q r s : F₂) : TwoForm × LinearForm :=
  if p = 0 then
    if q = 0 then
      if r = 0 then
        if s = 0 then (0, 0) else (translateEnvelope64, translateZ1)
      else
        if s = 0 then (translateEnvelope64, translateZ2)
        else (translateEnvelope64, translateZ4)
    else
      if r = 0 then
        if s = 0 then (translateEnvelope64, translateZ2)
        else (0, translateZ5)
      else
        if s = 0 then (translateEnvelope93, translateZ4)
        else (translateEnvelopeF7, translateZ2)
  else
    if q = 0 then
      if r = 0 then
        if s = 0 then (translateEnvelope64, translateZ1)
        else (translateEnvelope93, translateZ5)
      else
        if s = 0 then (translateEnvelopeF7, translateZ2)
        else (0, translateZ2)
    else
      if r = 0 then
        if s = 0 then (translateEnvelope64, translateZ3)
        else (translateEnvelopeF7, translateZ1)
      else
        if s = 0 then (0, translateZ4)
        else (translateEnvelope93, translateZ4)

private theorem f2_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem one_add_one_eq_zero_f2 : (1 : F₂) + 1 = 0 := by decide
private theorem ten_eq_zero_f2 : (10 : F₂) = 0 := by decide
private theorem five_ones_eq_one_f2 :
    (1 : F₂) + (1 + 1) + (1 + 1) = 1 := by decide

private theorem degreeTwoTranslateCorrectionWitness_mem
    (p q r s : F₂) :
    (degreeTwoTranslateCorrectionWitness p q r s).1 ∈
      firstOrderEnvelopeTwoSpace := by
  rcases f2_eq_zero_or_one p with rfl | rfl <;>
    rcases f2_eq_zero_or_one q with rfl | rfl <;>
      rcases f2_eq_zero_or_one r with rfl | rfl <;>
        rcases f2_eq_zero_or_one s with rfl | rfl <;>
          simp [degreeTwoTranslateCorrectionWitness,
            translateEnvelope64_mem, translateEnvelopeF7_mem,
            translateEnvelope93_mem]

private def translateKernelX (p q r s : F₂) : LinearForm :=
  p • translateXA₀ + q • translateXA₁ +
    r • translateXB₀ + s • translateXB₁

private def translateKernelY (p q r s : F₂) : LinearForm :=
  p • translateYA₀ + q • translateYA₁ +
    r • translateYB₀ + s • translateYB₁

@[simp] private theorem ambientBooleanContraction_targetTwo_sameA
    (ell : LinearForm) (c : TargetCoeff) (i j : Fin 5) (hij : i ≠ j) :
    ambientBooleanContraction ell (targetTwo c)
        (quadraticPair (aCoord i) (aCoord j)
          (fun h => hij (aCoord_injective h))) = 0 := by
  simp [ambientBooleanContraction]

@[simp] private theorem ambientBooleanContraction_targetTwo_sameB
    (ell : LinearForm) (c : TargetCoeff) (i j : Fin 5) (hij : i ≠ j) :
    ambientBooleanContraction ell (targetTwo c)
        (quadraticPair (bCoord i) (bCoord j)
          (fun h => hij (bCoord_injective h))) = 0 := by
  simp [ambientBooleanContraction]

@[simp] private theorem ambientBooleanContraction_targetTwo_cross
    (ell : LinearForm) (c : TargetCoeff) (i j : Fin 5) :
    ambientBooleanContraction ell (targetTwo c)
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)) =
      (ell (aCoord i) + ell (bCoord j)) * c (hankelIndex i j) := by
  unfold ambientBooleanContraction
  rw [targetTwo_cross]
  simp [quadraticPair, aCoord_ne_bCoord]

private def translateCorrectionLeft (p q r s : F₂) : TwoForm :=
  squarefreeWedge (translateKernelX p q r s) (translateKernelY p q r s) +
      ambientBooleanContraction (translateKernelX p q r s)
        degreeTwoTranslateRightTwo +
      ambientBooleanContraction (translateKernelY p q r s)
        degreeTwoTranslateLeftTwo

private def translateCorrectionRight
    (p q r s : F₂) (old : TwoForm) (z : LinearForm) : TwoForm :=
  old + squarefreeWedge (translateKernelX p q r s) z

private def TranslateCorrectionCase
    (p q r s : F₂) (old : TwoForm) (z : LinearForm) : Prop :=
  translateCorrectionLeft p q r s =
    translateCorrectionRight p q r s old z

private def TranslateCorrectionSameA
    (p q r s : F₂) (old : TwoForm) (z : LinearForm) : Prop :=
  ∀ i j : Fin 5, ∀ hij : i ≠ j,
    translateCorrectionLeft p q r s
        (quadraticPair (aCoord i) (aCoord j)
          (fun h => hij (aCoord_injective h))) =
      translateCorrectionRight p q r s old z
        (quadraticPair (aCoord i) (aCoord j)
          (fun h => hij (aCoord_injective h)))

private def TranslateCorrectionSameB
    (p q r s : F₂) (old : TwoForm) (z : LinearForm) : Prop :=
  ∀ i j : Fin 5, ∀ hij : i ≠ j,
    translateCorrectionLeft p q r s
        (quadraticPair (bCoord i) (bCoord j)
          (fun h => hij (bCoord_injective h))) =
      translateCorrectionRight p q r s old z
        (quadraticPair (bCoord i) (bCoord j)
          (fun h => hij (bCoord_injective h)))

private def TranslateCorrectionCross
    (p q r s : F₂) (old : TwoForm) (z : LinearForm) : Prop :=
  ∀ i j : Fin 5,
    translateCorrectionLeft p q r s
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)) =
      translateCorrectionRight p q r s old z
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j))

private def TranslateCorrectionSameARow
    (p q r s : F₂) (old : TwoForm) (z : LinearForm) (i : Fin 5) : Prop :=
  ∀ j : Fin 5, ∀ hij : i ≠ j,
    translateCorrectionLeft p q r s
        (quadraticPair (aCoord i) (aCoord j)
          (fun h => hij (aCoord_injective h))) =
      translateCorrectionRight p q r s old z
        (quadraticPair (aCoord i) (aCoord j)
          (fun h => hij (aCoord_injective h)))

private def TranslateCorrectionSameBRow
    (p q r s : F₂) (old : TwoForm) (z : LinearForm) (i : Fin 5) : Prop :=
  ∀ j : Fin 5, ∀ hij : i ≠ j,
    translateCorrectionLeft p q r s
        (quadraticPair (bCoord i) (bCoord j)
          (fun h => hij (bCoord_injective h))) =
      translateCorrectionRight p q r s old z
        (quadraticPair (bCoord i) (bCoord j)
          (fun h => hij (bCoord_injective h)))

private def TranslateCorrectionCrossRow
    (p q r s : F₂) (old : TwoForm) (z : LinearForm) (i : Fin 5) : Prop :=
  ∀ j : Fin 5,
    translateCorrectionLeft p q r s
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)) =
      translateCorrectionRight p q r s old z
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j))

set_option linter.unusedSimpArgs false

local macro "solve_degreeTwoTranslateCorrection" : tactic =>
  `(tactic|
    (unfold TranslateCorrectionCase translateCorrectionLeft
       translateCorrectionRight
     apply twoForm_ext_blocks
     · intros i j hij
       simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
         degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
         translateEnvelope93]
       rw [ambientBooleanContraction_targetTwo_sameA _ _ _ _ hij,
         ambientBooleanContraction_targetTwo_sameA _ _ _ _ hij]
       simp only [targetTwo_sameA _ _ _ hij, Pi.zero_apply,
         add_zero, zero_add, squarefreeWedge_pair]
       fin_cases i <;> fin_cases j <;>
         try simp at hij <;>
         simp [translateKernelX, translateKernelY,
           translateBlockP, translateBlockQ, translateBlockR] <;>
         try ring_nf <;> simp [N3Certificate.pow_two_f2,
           N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
           N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
           ten_eq_zero_f2, one_add_one_eq_zero_f2,
           five_ones_eq_one_f2,
           CharTwo.add_self_eq_zero, one_add_one_eq_two, add_assoc]
       all_goals decide
     · intros i j hij
       simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
         degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
         translateEnvelope93]
       rw [ambientBooleanContraction_targetTwo_sameB _ _ _ _ hij,
         ambientBooleanContraction_targetTwo_sameB _ _ _ _ hij]
       simp only [targetTwo_sameB _ _ _ hij, Pi.zero_apply,
         add_zero, zero_add, squarefreeWedge_pair]
       fin_cases i <;> fin_cases j <;>
         try simp at hij <;>
         simp [translateKernelX, translateKernelY,
           translateBlockP, translateBlockQ, translateBlockR] <;>
         try ring_nf <;> simp [N3Certificate.pow_two_f2,
           N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
           N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
           ten_eq_zero_f2, one_add_one_eq_zero_f2,
           five_ones_eq_one_f2,
           CharTwo.add_self_eq_zero, one_add_one_eq_two, add_assoc]
       all_goals decide
     · intros i j
       simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
         degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
         translateEnvelope93, ambientBooleanContraction_targetTwo_cross,
         targetTwo_cross, squarefreeWedge_pair]
       fin_cases i <;> fin_cases j <;>
         simp [translateKernelX, translateKernelY,
           degreeTwoTranslateLeftCoeff_eq_vector,
           degreeTwoTranslateRightCoeff_eq_vector, hankelIndex,
           translateBlockP, translateBlockQ, translateBlockR] <;>
         try ring_nf <;> simp [N3Certificate.pow_two_f2,
           N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
           N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
           ten_eq_zero_f2, one_add_one_eq_zero_f2,
           five_ones_eq_one_f2,
           CharTwo.add_self_eq_zero, one_add_one_eq_two, add_assoc]
       all_goals decide))

local macro "solve_degreeTwoTranslateSameA" : tactic =>
  `(tactic|
    (unfold TranslateCorrectionSameA translateCorrectionLeft
       translateCorrectionRight
     intros i j hij
     simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
       degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
       translateEnvelope93, ambientBooleanContraction_targetTwo_sameA,
       targetTwo_sameA, add_zero, zero_add]
     simp only [squarefreeWedge_pair]
     fin_cases i <;> fin_cases j <;>
       try simp at hij <;>
       simp [translateKernelX, translateKernelY,
         translateBlockP, translateBlockQ, translateBlockR] <;>
       ring_nf <;> simp [N3Certificate.pow_two_f2,
         N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]))

local macro "solve_degreeTwoTranslateSameB" : tactic =>
  `(tactic|
    (unfold TranslateCorrectionSameB translateCorrectionLeft
       translateCorrectionRight
     intros i j hij
     simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
       degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
       translateEnvelope93, ambientBooleanContraction_targetTwo_sameB,
       targetTwo_sameB, add_zero, zero_add]
     simp only [squarefreeWedge_pair]
     fin_cases i <;> fin_cases j <;>
       try simp at hij <;>
       simp [translateKernelX, translateKernelY,
         translateBlockP, translateBlockQ, translateBlockR] <;>
       ring_nf <;> simp [N3Certificate.pow_two_f2,
         N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]))

local macro "solve_degreeTwoTranslateCross" : tactic =>
  `(tactic|
    (unfold TranslateCorrectionCross translateCorrectionLeft
       translateCorrectionRight
     intros i j
     simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
       degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
       translateEnvelope93, ambientBooleanContraction_targetTwo_cross,
       targetTwo_cross]
     simp only [squarefreeWedge_pair]
     fin_cases i <;> fin_cases j <;>
       simp [translateKernelX, translateKernelY,
         translateZ1, translateZ2, translateZ3, translateZ4, translateZ5,
         translateXA₀, translateXA₁, translateYA₀, translateYA₁,
         translateXB₀, translateXB₁, translateYB₀, translateYB₁,
         degreeTwoTranslateLeftCoeff, degreeTwoTranslateRightCoeff,
         rZeroCoeff, rOneCoeff, rInfinityCoeff,
         dStarZeroCoeff, dStarOneCoeff, hankelIndex] <;>
       ring_nf <;> simp [N3Certificate.pow_two_f2,
         N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]))

local macro "solve_degreeTwoTranslateSameARow" : tactic =>
  `(tactic|
    (unfold TranslateCorrectionSameARow translateCorrectionLeft
       translateCorrectionRight
     intros j hij
     simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
       degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
       translateEnvelope93]
     rw [ambientBooleanContraction_targetTwo_sameA _ _ _ _ hij,
       ambientBooleanContraction_targetTwo_sameA _ _ _ _ hij]
     simp only [targetTwo_sameA _ _ _ hij, Pi.zero_apply,
       add_zero, zero_add, squarefreeWedge_pair]
     fin_cases j <;>
       try simp at hij <;>
       simp [translateKernelX, translateKernelY,
         translateZ1, translateZ2, translateZ3, translateZ4, translateZ5,
         translateXA₀, translateXA₁, translateYA₀, translateYA₁,
         translateXB₀, translateXB₁, translateYB₀, translateYB₁,
         aCoord, bCoord] <;>
       try ring_nf <;> simp [N3Certificate.pow_two_f2,
         N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]))

local macro "solve_degreeTwoTranslateSameBRow" : tactic =>
  `(tactic|
    (unfold TranslateCorrectionSameBRow translateCorrectionLeft
       translateCorrectionRight
     intros j hij
     simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
       degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
       translateEnvelope93]
     rw [ambientBooleanContraction_targetTwo_sameB _ _ _ _ hij,
       ambientBooleanContraction_targetTwo_sameB _ _ _ _ hij]
     simp only [targetTwo_sameB _ _ _ hij, Pi.zero_apply,
       add_zero, zero_add, squarefreeWedge_pair]
     fin_cases j <;>
       try simp at hij <;>
       simp [translateKernelX, translateKernelY,
         translateZ1, translateZ2, translateZ3, translateZ4, translateZ5,
         translateXA₀, translateXA₁, translateYA₀, translateYA₁,
         translateXB₀, translateXB₁, translateYB₀, translateYB₁,
         aCoord, bCoord] <;>
       try ring_nf <;> simp [N3Certificate.pow_two_f2,
         N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]))

local macro "solve_degreeTwoTranslateCrossRow" : tactic =>
  `(tactic|
    (unfold TranslateCorrectionCrossRow translateCorrectionLeft
       translateCorrectionRight
     intros j
     simp only [Pi.add_apply, degreeTwoTranslateLeftTwo,
       degreeTwoTranslateRightTwo, translateEnvelope64, translateEnvelopeF7,
       translateEnvelope93, ambientBooleanContraction_targetTwo_cross,
       targetTwo_cross, squarefreeWedge_pair]
     fin_cases j <;>
       simp [translateKernelX, translateKernelY,
         degreeTwoTranslateLeftCoeff_eq_vector,
         degreeTwoTranslateRightCoeff_eq_vector, hankelIndex,
         translateBlockP, translateBlockQ, translateBlockR] <;>
       try ring_nf <;> simp [N3Certificate.pow_two_f2,
         N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]))

private theorem translateCorrection0000 :
    TranslateCorrectionCase 0 0 0 0 0 0 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection0001 :
    TranslateCorrectionCase 0 0 0 1 translateEnvelope64 translateZ1 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection0010 :
    TranslateCorrectionCase 0 0 1 0 translateEnvelope64 translateZ2 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection0011 :
    TranslateCorrectionCase 0 0 1 1 translateEnvelope64 translateZ4 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection0100 :
    TranslateCorrectionCase 0 1 0 0 translateEnvelope64 translateZ2 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection0101 :
    TranslateCorrectionCase 0 1 0 1 0 translateZ5 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection0110 :
    TranslateCorrectionCase 0 1 1 0 translateEnvelope93 translateZ4 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection0111 :
    TranslateCorrectionCase 0 1 1 1 translateEnvelopeF7 translateZ2 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection1000 :
    TranslateCorrectionCase 1 0 0 0 translateEnvelope64 translateZ1 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection1001 :
    TranslateCorrectionCase 1 0 0 1 translateEnvelope93 translateZ5 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection1010 :
    TranslateCorrectionCase 1 0 1 0 translateEnvelopeF7 translateZ2 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection1011 :
    TranslateCorrectionCase 1 0 1 1 0 translateZ2 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection1100 :
    TranslateCorrectionCase 1 1 0 0 translateEnvelope64 translateZ3 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection1101 :
    TranslateCorrectionCase 1 1 0 1 translateEnvelopeF7 translateZ1 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection1110 :
    TranslateCorrectionCase 1 1 1 0 0 translateZ4 := by
  solve_degreeTwoTranslateCorrection

private theorem translateCorrection1111 :
    TranslateCorrectionCase 1 1 1 1 translateEnvelope93 translateZ4 := by
  solve_degreeTwoTranslateCorrection

private def TranslateCorrectionWitnessIdentity
    (p q r s : F₂) : Prop :=
  TranslateCorrectionCase p q r s
    (degreeTwoTranslateCorrectionWitness p q r s).1
    (degreeTwoTranslateCorrectionWitness p q r s).2

private theorem translateCorrectionWitness0000 :
    TranslateCorrectionWitnessIdentity 0 0 0 0 := by
  exact translateCorrection0000

private theorem translateCorrectionWitness0001 :
    TranslateCorrectionWitnessIdentity 0 0 0 1 := by
  exact translateCorrection0001

private theorem translateCorrectionWitness0010 :
    TranslateCorrectionWitnessIdentity 0 0 1 0 := by
  exact translateCorrection0010

private theorem translateCorrectionWitness0011 :
    TranslateCorrectionWitnessIdentity 0 0 1 1 := by
  exact translateCorrection0011

private theorem translateCorrectionWitness0100 :
    TranslateCorrectionWitnessIdentity 0 1 0 0 := by
  exact translateCorrection0100

private theorem translateCorrectionWitness0101 :
    TranslateCorrectionWitnessIdentity 0 1 0 1 := by
  exact translateCorrection0101

private theorem translateCorrectionWitness0110 :
    TranslateCorrectionWitnessIdentity 0 1 1 0 := by
  exact translateCorrection0110

private theorem translateCorrectionWitness0111 :
    TranslateCorrectionWitnessIdentity 0 1 1 1 := by
  exact translateCorrection0111

private theorem translateCorrectionWitness1000 :
    TranslateCorrectionWitnessIdentity 1 0 0 0 := by
  exact translateCorrection1000

private theorem translateCorrectionWitness1001 :
    TranslateCorrectionWitnessIdentity 1 0 0 1 := by
  exact translateCorrection1001

private theorem translateCorrectionWitness1010 :
    TranslateCorrectionWitnessIdentity 1 0 1 0 := by
  exact translateCorrection1010

private theorem translateCorrectionWitness1011 :
    TranslateCorrectionWitnessIdentity 1 0 1 1 := by
  exact translateCorrection1011

private theorem translateCorrectionWitness1100 :
    TranslateCorrectionWitnessIdentity 1 1 0 0 := by
  exact translateCorrection1100

private theorem translateCorrectionWitness1101 :
    TranslateCorrectionWitnessIdentity 1 1 0 1 := by
  exact translateCorrection1101

private theorem translateCorrectionWitness1110 :
    TranslateCorrectionWitnessIdentity 1 1 1 0 := by
  exact translateCorrection1110

private theorem translateCorrectionWitness1111 :
    TranslateCorrectionWitnessIdentity 1 1 1 1 := by
  exact translateCorrection1111

private theorem translateCorrectionWitness000
    (s : F₂) : TranslateCorrectionWitnessIdentity 0 0 0 s := by
  rcases f2_eq_zero_or_one s with rfl | rfl
  · exact translateCorrectionWitness0000
  · exact translateCorrectionWitness0001

private theorem translateCorrectionWitness001
    (s : F₂) : TranslateCorrectionWitnessIdentity 0 0 1 s := by
  rcases f2_eq_zero_or_one s with rfl | rfl
  · exact translateCorrectionWitness0010
  · exact translateCorrectionWitness0011

private theorem translateCorrectionWitness010
    (s : F₂) : TranslateCorrectionWitnessIdentity 0 1 0 s := by
  rcases f2_eq_zero_or_one s with rfl | rfl
  · exact translateCorrectionWitness0100
  · exact translateCorrectionWitness0101

private theorem translateCorrectionWitness011
    (s : F₂) : TranslateCorrectionWitnessIdentity 0 1 1 s := by
  rcases f2_eq_zero_or_one s with rfl | rfl
  · exact translateCorrectionWitness0110
  · exact translateCorrectionWitness0111

private theorem translateCorrectionWitness100
    (s : F₂) : TranslateCorrectionWitnessIdentity 1 0 0 s := by
  rcases f2_eq_zero_or_one s with rfl | rfl
  · exact translateCorrectionWitness1000
  · exact translateCorrectionWitness1001

private theorem translateCorrectionWitness101
    (s : F₂) : TranslateCorrectionWitnessIdentity 1 0 1 s := by
  rcases f2_eq_zero_or_one s with rfl | rfl
  · exact translateCorrectionWitness1010
  · exact translateCorrectionWitness1011

private theorem translateCorrectionWitness110
    (s : F₂) : TranslateCorrectionWitnessIdentity 1 1 0 s := by
  rcases f2_eq_zero_or_one s with rfl | rfl
  · exact translateCorrectionWitness1100
  · exact translateCorrectionWitness1101

private theorem translateCorrectionWitness111
    (s : F₂) : TranslateCorrectionWitnessIdentity 1 1 1 s := by
  rcases f2_eq_zero_or_one s with rfl | rfl
  · exact translateCorrectionWitness1110
  · exact translateCorrectionWitness1111

private theorem translateCorrectionWitness00
    (r s : F₂) : TranslateCorrectionWitnessIdentity 0 0 r s := by
  rcases f2_eq_zero_or_one r with rfl | rfl
  · exact translateCorrectionWitness000 s
  · exact translateCorrectionWitness001 s

private theorem translateCorrectionWitness01
    (r s : F₂) : TranslateCorrectionWitnessIdentity 0 1 r s := by
  rcases f2_eq_zero_or_one r with rfl | rfl
  · exact translateCorrectionWitness010 s
  · exact translateCorrectionWitness011 s

private theorem translateCorrectionWitness10
    (r s : F₂) : TranslateCorrectionWitnessIdentity 1 0 r s := by
  rcases f2_eq_zero_or_one r with rfl | rfl
  · exact translateCorrectionWitness100 s
  · exact translateCorrectionWitness101 s

private theorem translateCorrectionWitness11
    (r s : F₂) : TranslateCorrectionWitnessIdentity 1 1 r s := by
  rcases f2_eq_zero_or_one r with rfl | rfl
  · exact translateCorrectionWitness110 s
  · exact translateCorrectionWitness111 s

private theorem translateCorrectionWitness0
    (q r s : F₂) : TranslateCorrectionWitnessIdentity 0 q r s := by
  rcases f2_eq_zero_or_one q with rfl | rfl
  · exact translateCorrectionWitness00 r s
  · exact translateCorrectionWitness01 r s

private theorem translateCorrectionWitness1
    (q r s : F₂) : TranslateCorrectionWitnessIdentity 1 q r s := by
  rcases f2_eq_zero_or_one q with rfl | rfl
  · exact translateCorrectionWitness10 r s
  · exact translateCorrectionWitness11 r s

private theorem translateCorrectionWitnessAll
    (p q r s : F₂) : TranslateCorrectionWitnessIdentity p q r s := by
  rcases f2_eq_zero_or_one p with rfl | rfl
  · exact translateCorrectionWitness0 q r s
  · exact translateCorrectionWitness1 q r s

private theorem degreeTwoTranslateCorrectionWitness_identity
    (p q r s : F₂) :
    let x := translateKernelX p q r s
    let y := translateKernelY p q r s
    squarefreeWedge x y +
        ambientBooleanContraction x degreeTwoTranslateRightTwo +
        ambientBooleanContraction y degreeTwoTranslateLeftTwo =
      (degreeTwoTranslateCorrectionWitness p q r s).1 +
        squarefreeWedge x (degreeTwoTranslateCorrectionWitness p q r s).2 := by
  change TranslateCorrectionWitnessIdentity p q r s
  exact translateCorrectionWitnessAll p q r s

/-- Both directions of the adjusted degree-two plane lie in the exact
first-order envelope. -/
theorem degreeTwoTranslateLeftTwo_mem_firstOrderEnvelope :
    degreeTwoTranslateLeftTwo ∈ firstOrderEnvelopeTwoSpace := by
  rw [degreeTwoTranslateLeftTwo, degreeTwoTranslateLeftCoeff_eq_vector]
  exact translateEnvelope64_mem

theorem degreeTwoTranslateRightTwo_mem_firstOrderEnvelope :
    degreeTwoTranslateRightTwo ∈ firstOrderEnvelopeTwoSpace := by
  rw [degreeTwoTranslateRightTwo, degreeTwoTranslateRightCoeff_eq_vector]
  exact translateEnvelope93_mem

/-- On the adjusted degree-two plane, every cubic syzygy has Boolean
quadratic correction equal to one decomposable form modulo the first-order
envelope. -/
theorem degreeTwoTranslate_booleanCorrection_decomposition
    (x y : LinearForm)
    (hcubic : factorPlaneCubic x y degreeTwoTranslateLeftTwo
      degreeTwoTranslateRightTwo = 0) :
    ∃ old ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x degreeTwoTranslateRightTwo +
          ambientBooleanContraction y degreeTwoTranslateLeftTwo =
        old + squarefreeWedge x z := by
  rcases degreeTwoTranslate_cubic_syzygy x y hcubic with
    ⟨p, q, r, s, hx, hy⟩
  have hx' : x = translateKernelX p q r s := by
    simpa [translateKernelX] using hx
  have hy' : y = translateKernelY p q r s := by
    simpa [translateKernelY] using hy
  refine ⟨(degreeTwoTranslateCorrectionWitness p q r s).1,
    degreeTwoTranslateCorrectionWitness_mem p q r s,
    (degreeTwoTranslateCorrectionWitness p q r s).2, ?_⟩
  rw [hx', hy']
  exact degreeTwoTranslateCorrectionWitness_identity p q r s

/-- Equal cubic parts on the adjusted degree-two plane leave only two
decomposable quadratic forms modulo the first-order envelope. -/
theorem degreeTwoTranslate_shadow_decomposition
    (a b a' b' : F₂) (ell m x y : LinearForm)
    (hcubic : factorPlaneCubic x y degreeTwoTranslateLeftTwo
      degreeTwoTranslateRightTwo = 0) :
    ∃ old ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m degreeTwoTranslateLeftTwo
          degreeTwoTranslateRightTwo +
        lowProductQuadraticShadow a' b' (ell + x) (m + y)
          degreeTwoTranslateLeftTwo degreeTwoTranslateRightTwo =
        old + squarefreeWedge u v + squarefreeWedge s t := by
  rcases degreeTwoTranslate_booleanCorrection_decomposition x y hcubic with
    ⟨old, hold, z, hcorrection⟩
  exact lowProductShadow_decomposition_of_correction
    firstOrderEnvelopeTwoSpace a b a' b' ell m x y
    degreeTwoTranslateLeftTwo degreeTwoTranslateRightTwo
    degreeTwoTranslateLeftTwo_mem_firstOrderEnvelope
    degreeTwoTranslateRightTwo_mem_firstOrderEnvelope
    old hold z hcorrection

/-- The adjusted degree-two exceptional plane cannot produce the unique
target coset missing from the first-order envelope. -/
theorem degreeTwoTranslate_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic :
      factorPlaneCubic ell m degreeTwoTranslateLeftTwo
          degreeTwoTranslateRightTwo =
        factorPlaneCubic ell' m' degreeTwoTranslateLeftTwo
          degreeTwoTranslateRightTwo)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m degreeTwoTranslateLeftTwo
          degreeTwoTranslateRightTwo +
        lowProductQuadraticShadow a' b' ell' m' degreeTwoTranslateLeftTwo
          degreeTwoTranslateRightTwo ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  let x : LinearForm := ell + ell'
  let y : LinearForm := m + m'
  have hx : ell + x = ell' := by
    change ell + (ell + ell') = ell'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hy : m + y = m' := by
    change m + (m + m') = m'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hcubicZero :
      factorPlaneCubic x y degreeTwoTranslateLeftTwo
        degreeTwoTranslateRightTwo = 0 :=
    factorPlaneCubic_difference_eq_zero ell m ell' m'
      degreeTwoTranslateLeftTwo degreeTwoTranslateRightTwo hcubic
  rcases degreeTwoTranslate_shadow_decomposition
      a b a' b' ell m x y hcubicZero with
    ⟨old, hold, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    old hold p q s t u hu
  have hdecomp' :
      lowProductQuadraticShadow a b ell m degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo +
          lowProductQuadraticShadow a' b' ell' m'
            degreeTwoTranslateLeftTwo degreeTwoTranslateRightTwo =
        old + squarefreeWedge p q + squarefreeWedge s t := by
    simpa only [hx, hy] using hdecomp
  exact hdecomp'.symm.trans hmissing

end

end N5
end UnrestrictedBooleanMul
