import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryRaw

/-!
# Typed interface to the rational-return history certificate

The generated certificate uses 71 Boolean coordinates.  This module assigns
those coordinates their mathematical roles so the circuit-facing
normalization layer does not depend on positional conventions.

For the canonical `(0,1)` factor-pair and off-axis `r1` feedback branch,
the 28 equations are four vanishing high coefficients of the returned
quadratic section, eighteen vanishing high coefficients of the feedback
product, and six equal-quotient coefficients.  The checked certificate says
that these equations force the missing first-order target coefficient to
vanish.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Parameters retained by the history-sensitive equal-high return model. -/
structure ZeroOneOffAxisHistoryParameters where
  ell : Fin 10 → F₂
  m : Fin 10 → F₂
  leftShift : Fin 10 → F₂
  rightShift : Fin 10 → F₂
  feedbackConstant : F₂
  feedbackLinear : Fin 10 → F₂
  correctionConstant : F₂
  correctionLinear : Fin 10 → F₂
  correctionTarget : Fin 8 → F₂
  correctionReturn : F₂

/-- Pack the named history parameters in the coordinate order used by the
explicit polynomial certificate. -/
def ZeroOneOffAxisHistoryParameters.vector
    (p : ZeroOneOffAxisHistoryParameters) : Fin 71 → F₂ :=
  ![
    p.ell 0, p.ell 1, p.ell 2, p.ell 3, p.ell 4,
    p.ell 5, p.ell 6, p.ell 7, p.ell 8, p.ell 9,
    p.m 0, p.m 1, p.m 2, p.m 3, p.m 4,
    p.m 5, p.m 6, p.m 7, p.m 8, p.m 9,
    p.leftShift 0, p.leftShift 1, p.leftShift 2, p.leftShift 3, p.leftShift 4,
    p.leftShift 5, p.leftShift 6, p.leftShift 7, p.leftShift 8, p.leftShift 9,
    p.rightShift 0, p.rightShift 1, p.rightShift 2, p.rightShift 3, p.rightShift 4,
    p.rightShift 5, p.rightShift 6, p.rightShift 7, p.rightShift 8, p.rightShift 9,
    p.feedbackConstant, p.feedbackLinear 0, p.feedbackLinear 1, p.feedbackLinear 2, p.feedbackLinear 3,
    p.feedbackLinear 4, p.feedbackLinear 5, p.feedbackLinear 6, p.feedbackLinear 7, p.feedbackLinear 8,
    p.feedbackLinear 9, p.correctionConstant, p.correctionLinear 0, p.correctionLinear 1, p.correctionLinear 2,
    p.correctionLinear 3, p.correctionLinear 4, p.correctionLinear 5, p.correctionLinear 6, p.correctionLinear 7,
    p.correctionLinear 8, p.correctionLinear 9, p.correctionTarget 0, p.correctionTarget 1, p.correctionTarget 2,
    p.correctionTarget 3, p.correctionTarget 4, p.correctionTarget 5, p.correctionTarget 6, p.correctionTarget 7,
    p.correctionReturn
  ]

/-- All high-vanishing and equal-quotient equations used by the certificate. -/
def ZeroOneOffAxisHistoryParameters.Equations
    (p : ZeroOneOffAxisHistoryParameters) : Prop :=
  ∀ i : Fin 28, zeroOneRawConstraint p.vector i = 0

/-- The coefficient of the unique missing first-order target direction. -/
def ZeroOneOffAxisHistoryParameters.missingCoefficient
    (p : ZeroOneOffAxisHistoryParameters) : F₂ :=
  zeroOneRawTarget p.vector

/-- The canonical off-axis history equations rule out a missing-target
escape. -/
theorem ZeroOneOffAxisHistoryParameters.missingCoefficient_eq_zero
    (p : ZeroOneOffAxisHistoryParameters) (h : p.Equations) :
    p.missingCoefficient = 0 :=
  zeroOne_offAxis_raw_history_missing_eq_zero p.vector h

/-- Equivalently, no parameter tuple satisfies the history equations while
having missing coefficient one. -/
theorem not_zeroOneOffAxisHistoryEscape
    (p : ZeroOneOffAxisHistoryParameters) :
    ¬(p.Equations ∧ p.missingCoefficient = 1) := by
  rintro ⟨hequations, hmissing⟩
  rw [p.missingCoefficient_eq_zero hequations] at hmissing
  exact zero_ne_one hmissing

end
end N5
end UnrestrictedBooleanMul
