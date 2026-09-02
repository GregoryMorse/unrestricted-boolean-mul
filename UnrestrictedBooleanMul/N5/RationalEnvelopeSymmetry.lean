import UnrestrictedBooleanMul.N5.RationalPlaceSymmetry
import UnrestrictedBooleanMul.N5.FirstOrderEnvelope

/-!
# Rational-place symmetry of the first-order envelope

Translation and reversal already act on linear forms, two-forms, and the
nine Hankel coefficients.  Here we record that both generators preserve the
missing functional.  Consequently they preserve the first-order envelope
and transport its unique missing affine coset to itself.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Translation and reversal preserve the defining functional of the
codimension-one first-order coefficient envelope. -/
theorem firstOrderMissingFunctional_rationalTargetCoeffChange
    (theta : Fin 2) (c : TargetCoeff) :
    firstOrderMissingFunctional (rationalTargetCoeffChange theta c) =
      firstOrderMissingFunctional c := by
  fin_cases theta <;>
    simp [rationalTargetCoeffChange, firstOrderMissingFunctional] <;>
    ring_nf;
    simp [N3Certificate.two_eq_zero_f2,
      show (3 : F₂) = 1 by decide, show (4 : F₂) = 0 by decide]

/-- Coefficient-space form of envelope invariance. -/
theorem rationalTargetCoeffChange_mem_firstOrderEnvelope_iff
    (theta : Fin 2) (c : TargetCoeff) :
    rationalTargetCoeffChange theta c ∈ firstOrderEnvelopeCoeffSpace ↔
      c ∈ firstOrderEnvelopeCoeffSpace := by
  rw [mem_firstOrderEnvelopeCoeffSpace,
    mem_firstOrderEnvelopeCoeffSpace,
    firstOrderMissingFunctional_rationalTargetCoeffChange]

/-- Each rational-place generator maps the embedded first-order two-form
envelope into itself. -/
theorem rationalPlaceTwoFormLinear_mem_firstOrderEnvelope
    (theta : Fin 2) {q : TwoForm}
    (hq : q ∈ firstOrderEnvelopeTwoSpace) :
    rationalPlaceTwoFormLinear theta q ∈ firstOrderEnvelopeTwoSpace := by
  rcases hq with ⟨c, hc, rfl⟩
  change rationalPlaceTwoFormLinear theta (targetTwo c) ∈
    firstOrderEnvelopeTwoSpace
  rw [rationalPlaceTwoFormLinear_targetTwo]
  exact ⟨rationalTargetCoeffChange theta c,
    (rationalTargetCoeffChange_mem_firstOrderEnvelope_iff theta c).2 hc,
    rfl⟩

/-- The correction which returns the transformed missing representative to
the chosen representative is an old first-order coefficient. -/
def rationalMissingCorrection (theta : Fin 2) : TargetCoeff :=
  rationalTargetCoeffChange theta firstOrderMissingCoeff +
    firstOrderMissingCoeff

theorem rationalMissingCorrection_mem
    (theta : Fin 2) :
    rationalMissingCorrection theta ∈ firstOrderEnvelopeCoeffSpace := by
  rw [mem_firstOrderEnvelopeCoeffSpace]
  simp only [rationalMissingCorrection, map_add,
    firstOrderMissingFunctional_rationalTargetCoeffChange,
    firstOrderMissingFunctional_missing,
    CharTwo.add_self_eq_zero]

/-- The displayed coefficient substitutions are additive.  Keeping this as
a lemma avoids repeatedly expanding all nine coordinates. -/
theorem rationalTargetCoeffChange_add
    (theta : Fin 2) (c d : TargetCoeff) :
    rationalTargetCoeffChange theta (c + d) =
      rationalTargetCoeffChange theta c + rationalTargetCoeffChange theta d := by
  fin_cases theta <;>
    funext i <;> fin_cases i <;>
    simp [rationalTargetCoeffChange] <;> abel

/-- Exact coefficient identity for transport of the missing affine coset. -/
theorem rationalTargetCoeffChange_missing_add
    (theta : Fin 2) (u : TargetCoeff) :
    rationalTargetCoeffChange theta (firstOrderMissingCoeff + u) =
      firstOrderMissingCoeff +
        (rationalMissingCorrection theta +
          rationalTargetCoeffChange theta u) := by
  have hadd : rationalTargetCoeffChange theta
      (firstOrderMissingCoeff + u) =
      rationalTargetCoeffChange theta firstOrderMissingCoeff +
        rationalTargetCoeffChange theta u :=
    rationalTargetCoeffChange_add theta firstOrderMissingCoeff u
  have hmissingSelf : firstOrderMissingCoeff + firstOrderMissingCoeff = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (firstOrderMissingCoeff i)
  rw [hadd, rationalMissingCorrection]
  calc
    rationalTargetCoeffChange theta firstOrderMissingCoeff +
        rationalTargetCoeffChange theta u =
      (firstOrderMissingCoeff + firstOrderMissingCoeff) +
        (rationalTargetCoeffChange theta firstOrderMissingCoeff +
          rationalTargetCoeffChange theta u) := by
      rw [hmissingSelf, zero_add]
    _ = firstOrderMissingCoeff +
        (rationalTargetCoeffChange theta firstOrderMissingCoeff +
          firstOrderMissingCoeff + rationalTargetCoeffChange theta u) := by
      ac_rfl

/-- Two-form form: rational-place symmetry preserves the missing affine
target coset, with an explicit old-envelope correction. -/
theorem rationalPlaceTwoFormLinear_missingCoset
    (theta : Fin 2) (u : TargetCoeff) :
    rationalPlaceTwoFormLinear theta
        (targetTwo (firstOrderMissingCoeff + u)) =
      targetTwo (firstOrderMissingCoeff +
        (rationalMissingCorrection theta +
          rationalTargetCoeffChange theta u)) := by
  rw [rationalPlaceTwoFormLinear_targetTwo,
    rationalTargetCoeffChange_missing_add]

end
end N5
end UnrestrictedBooleanMul
