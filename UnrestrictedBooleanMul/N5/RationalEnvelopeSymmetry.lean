import UnrestrictedBooleanMul.N5.EnvelopeLocalSymmetry

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

/-! ## Transported target-clean second jets -/

/-- The target-clean second-jet space transported from the rational-zero
normalization by one rational-place generator. -/
def rationalTargetCleanSecondJetSpace (theta : Fin 2) :
    Submodule F₂ TwoForm :=
  targetCleanSecondJetSpace.map (rationalPlaceTwoFormLinear theta)

/-- Membership in a transported clean space is tested by applying the same
involutive generator once more. -/
theorem mem_rationalTargetCleanSecondJetSpace_iff
    (theta : Fin 2) (q : TwoForm) :
    q ∈ rationalTargetCleanSecondJetSpace theta ↔
      rationalPlaceTwoFormLinear theta q ∈ targetCleanSecondJetSpace := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ targetCleanSecondJetSpace at hz
    simpa only [rationalPlaceTwoFormLinear_involutive] using hz
  · intro hq
    exact ⟨rationalPlaceTwoFormLinear theta q, hq,
      rationalPlaceTwoFormLinear_involutive theta q⟩

/-- The multiplication target meets every rational transport of the clean
second jet in precisely the old first-order envelope. -/
theorem targetTwoSpace_inf_rationalTargetCleanSecondJetSpace
    (theta : Fin 2) :
    targetTwoSpace ⊓ rationalTargetCleanSecondJetSpace theta =
      firstOrderEnvelopeTwoSpace := by
  apply le_antisymm
  · rintro p ⟨hpTarget, hpClean⟩
    have htransTarget : rationalPlaceTwoFormLinear theta p ∈
        targetTwoSpace := by
      rcases hpTarget with ⟨c, rfl⟩
      change rationalPlaceTwoFormLinear theta (targetTwo c) ∈ targetTwoSpace
      rw [rationalPlaceTwoFormLinear_targetTwo]
      exact ⟨rationalTargetCoeffChange theta c, rfl⟩
    have htransClean : rationalPlaceTwoFormLinear theta p ∈
        targetCleanSecondJetSpace :=
      (mem_rationalTargetCleanSecondJetSpace_iff theta p).1 hpClean
    have htransFirst : rationalPlaceTwoFormLinear theta p ∈
        firstOrderEnvelopeTwoSpace :=
      (target_mem_targetCleanSecondJetSpace_iff_firstOrder
        (rationalPlaceTwoFormLinear theta p) htransTarget).1 htransClean
    have hback := rationalPlaceTwoFormLinear_mem_firstOrderEnvelope
      theta (rationalPlaceTwoFormLinear theta p) htransFirst
    simpa only [rationalPlaceTwoFormLinear_involutive] using hback
  · intro p hpFirst
    have hpTarget : p ∈ targetTwoSpace :=
      firstOrderEnvelopeTwoSpace_le_targetTwoSpace hpFirst
    have htransFirst : rationalPlaceTwoFormLinear theta p ∈
        firstOrderEnvelopeTwoSpace :=
      rationalPlaceTwoFormLinear_mem_firstOrderEnvelope theta p hpFirst
    have htransTarget : rationalPlaceTwoFormLinear theta p ∈
        targetTwoSpace :=
      firstOrderEnvelopeTwoSpace_le_targetTwoSpace htransFirst
    have htransClean : rationalPlaceTwoFormLinear theta p ∈
        targetCleanSecondJetSpace :=
      (target_mem_targetCleanSecondJetSpace_iff_firstOrder
        (rationalPlaceTwoFormLinear theta p) htransTarget).2 htransFirst
    exact ⟨hpTarget,
      (mem_rationalTargetCleanSecondJetSpace_iff theta p).2 htransClean⟩

theorem rationalTargetCoeffChange_missing
    (theta : Fin 2) :
    rationalTargetCoeffChange theta firstOrderMissingCoeff =
      firstOrderMissingCoeff + rationalMissingCorrection theta := by
  fin_cases theta <;>
    funext i <;> fin_cases i <;>
    simp [rationalTargetCoeffChange, firstOrderMissingCoeff,
      rationalMissingCorrection, CharTwo.add_self_eq_zero]

/-- The affine nondecomposability part of the target-clean certificate is
also invariant under rational-place transport. -/
theorem firstOrderMissing_add_rationalTargetClean_not_decomposable
    (theta : Fin 2) (z : TwoForm)
    (hz : z ∈ rationalTargetCleanSecondJetSpace theta) :
    ¬ IsDecomposableTwo (targetTwo firstOrderMissingCoeff + z) := by
  intro hdec
  have htransZ : rationalPlaceTwoFormLinear theta z ∈
      targetCleanSecondJetSpace :=
    (mem_rationalTargetCleanSecondJetSpace_iff theta z).1 hz
  have hcorrectionFirst : targetTwo (rationalMissingCorrection theta) ∈
      firstOrderEnvelopeTwoSpace :=
    ⟨rationalMissingCorrection theta,
      rationalMissingCorrection_mem theta, rfl⟩
  have hcorrectionClean : targetTwo (rationalMissingCorrection theta) ∈
      targetCleanSecondJetSpace := by
    have htarget : targetTwo (rationalMissingCorrection theta) ∈
        targetTwoSpace :=
      firstOrderEnvelopeTwoSpace_le_targetTwoSpace hcorrectionFirst
    exact (target_mem_targetCleanSecondJetSpace_iff_firstOrder
      (targetTwo (rationalMissingCorrection theta)) htarget).2
        hcorrectionFirst
  let z' := targetTwo (rationalMissingCorrection theta) +
    rationalPlaceTwoFormLinear theta z
  have hz' : z' ∈ targetCleanSecondJetSpace :=
    targetCleanSecondJetSpace.add_mem hcorrectionClean htransZ
  have htransEq :
      rationalPlaceTwoFormLinear theta
          (targetTwo firstOrderMissingCoeff + z) =
        targetTwo firstOrderMissingCoeff + z' := by
    rw [map_add, rationalPlaceTwoFormLinear_targetTwo,
      rationalTargetCoeffChange_missing]
    have htargetAdd :
        targetTwo
            (firstOrderMissingCoeff + rationalMissingCorrection theta) =
          targetTwo firstOrderMissingCoeff +
            targetTwo (rationalMissingCorrection theta) := by
      exact targetTwoLinear.map_add _ _
    rw [htargetAdd]
    change
      (targetTwo firstOrderMissingCoeff +
          targetTwo (rationalMissingCorrection theta)) +
          rationalPlaceTwoFormLinear theta z =
        targetTwo firstOrderMissingCoeff +
          (targetTwo (rationalMissingCorrection theta) +
            rationalPlaceTwoFormLinear theta z)
    exact add_assoc _ _ _
  have htransDec : IsDecomposableTwo
      (targetTwo firstOrderMissingCoeff + z') := by
    rw [← htransEq]
    exact rationalPlaceTwoFormLinear_decomposable theta hdec
  exact firstOrderMissing_add_targetClean_not_decomposable z' hz' htransDec

end
end N5
end UnrestrictedBooleanMul
