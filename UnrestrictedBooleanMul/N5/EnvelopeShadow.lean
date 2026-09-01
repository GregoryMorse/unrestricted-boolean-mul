import UnrestrictedBooleanMul.N5.IndependentShadow

/-!
# First-order envelope shadow bridge

This module isolates the decomposable-defect step in manuscript Lemma 11.2.
Once a quadratic shadow comparison has been localized to the target-clean
second-jet module, adjoining one decomposable defect direction still cannot
create the missing target class.  The proof is the submodule intersection
identity (11.7), not a finite circuit or coordinate-state enumeration.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The seven independent exceptional planes in the first-order envelope:
three rational value--jet planes, three rational-value pairs, and `D_*`. -/
inductive ExceptionalIndependentPlane where
  | rationalJet (place : Fin 3)
  | rationalPair (pair : Fin 3)
  | degreeTwo
  deriving DecidableEq

def ExceptionalIndependentPlane.left :
    ExceptionalIndependentPlane → TwoForm
  | .rationalJet 0 => rationalZeroValueTwo
  | .rationalJet 1 => rationalOneValueTwo
  | .rationalJet 2 => rationalInfinityValueTwo
  | .rationalPair pair => rationalPairLeftValueTwo pair
  | .degreeTwo => dStarZeroTwo

def ExceptionalIndependentPlane.right :
    ExceptionalIndependentPlane → TwoForm
  | .rationalJet 0 => rationalZeroJetTwo
  | .rationalJet 1 => rationalOneJetTwo
  | .rationalJet 2 => rationalInfinityJetTwo
  | .rationalPair pair => rationalPairRightValueTwo pair
  | .degreeTwo => dStarOneTwo

theorem ExceptionalIndependentPlane.left_mem_firstOrderEnvelope
    (P : ExceptionalIndependentPlane) :
    P.left ∈ firstOrderEnvelopeTwoSpace := by
  cases P with
  | rationalJet place =>
      fin_cases place
      · change rationalZeroValueTwo ∈ firstOrderEnvelopeTwoSpace
        rw [rationalZeroValueTwo_eq_target]
        simpa [exactFirstOrderDirections] using
          targetTwo_exactFirstOrderDirection_mem 0
      · change rationalOneValueTwo ∈ firstOrderEnvelopeTwoSpace
        rw [rationalOneValueTwo_eq_target]
        simpa [exactFirstOrderDirections] using
          targetTwo_exactFirstOrderDirection_mem 1
      · change rationalInfinityValueTwo ∈ firstOrderEnvelopeTwoSpace
        rw [rationalInfinityValueTwo_eq_target]
        simpa [exactFirstOrderDirections] using
          targetTwo_exactFirstOrderDirection_mem 2
  | rationalPair pair =>
      exact rationalValueTwo_mem_firstOrderEnvelope
        (rationalPairLeft pair)
  | degreeTwo =>
      exact dStarZeroTwo_mem_firstOrderEnvelope

theorem ExceptionalIndependentPlane.right_mem_firstOrderEnvelope
    (P : ExceptionalIndependentPlane) :
    P.right ∈ firstOrderEnvelopeTwoSpace := by
  cases P with
  | rationalJet place =>
      fin_cases place
      · change rationalZeroJetTwo ∈ firstOrderEnvelopeTwoSpace
        rw [rationalZeroJetTwo_eq_target]
        simpa [exactFirstOrderDirections] using
          targetTwo_exactFirstOrderDirection_mem 3
      · change rationalOneJetTwo ∈ firstOrderEnvelopeTwoSpace
        rw [rationalOneJetTwo_eq_target]
        simpa [exactFirstOrderDirections] using
          targetTwo_exactFirstOrderDirection_mem 4
      · change rationalInfinityJetTwo ∈ firstOrderEnvelopeTwoSpace
        rw [rationalInfinityJetTwo_eq_target]
        simpa [exactFirstOrderDirections] using
          targetTwo_exactFirstOrderDirection_mem 5
  | rationalPair pair =>
      exact rationalValueTwo_mem_firstOrderEnvelope
        (rationalPairRight pair)
  | degreeTwo =>
      exact dStarOneTwo_mem_firstOrderEnvelope

/-- The uniform shadow-exclusion proposition attached to a canonical
exceptional plane.  Naming it keeps each kernel-checked branch below the
ordinary heartbeat budget. -/
def ExceptionalIndependentPlane.ShadowExcluded
    (P : ExceptionalIndependentPlane) : Prop :=
  ∀ (a b a' b' : F₂) (ell m ell' m' : LinearForm),
    factorPlaneCubic ell m P.left P.right =
        factorPlaneCubic ell' m' P.left P.right →
    ∀ (u : TargetCoeff), u ∈ firstOrderEnvelopeCoeffSpace →
      lowProductQuadraticShadow a b ell m P.left P.right +
          lowProductQuadraticShadow a' b' ell' m' P.left P.right ≠
        targetTwo (firstOrderMissingCoeff + u)

private theorem rationalZeroJet_shadowExcluded :
    (ExceptionalIndependentPlane.rationalJet 0).ShadowExcluded := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact rationalZero_shadow_not_missingCoset
    a b a' b' ell m ell' m' hcubic u hu

private theorem rationalOneJet_shadowExcluded :
    (ExceptionalIndependentPlane.rationalJet 1).ShadowExcluded := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact rationalOne_shadow_not_missingCoset
    a b a' b' ell m ell' m' hcubic u hu

private theorem rationalInfinityJet_shadowExcluded :
    (ExceptionalIndependentPlane.rationalJet 2).ShadowExcluded := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact rationalInfinity_shadow_not_missingCoset
    a b a' b' ell m ell' m' hcubic u hu

private theorem rationalZeroOne_shadowExcluded :
    (ExceptionalIndependentPlane.rationalPair 0).ShadowExcluded := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact rationalPair_shadow_not_missingCoset
    0 a b a' b' ell m ell' m' hcubic u hu

private theorem rationalZeroInfinity_shadowExcluded :
    (ExceptionalIndependentPlane.rationalPair 1).ShadowExcluded := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact rationalPair_shadow_not_missingCoset
    1 a b a' b' ell m ell' m' hcubic u hu

private theorem rationalOneInfinity_shadowExcluded :
    (ExceptionalIndependentPlane.rationalPair 2).ShadowExcluded := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact rationalPair_shadow_not_missingCoset
    2 a b a' b' ell m ell' m' hcubic u hu

private theorem degreeTwo_shadowExcluded :
    ExceptionalIndependentPlane.degreeTwo.ShadowExcluded := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact dStar_shadow_not_missingCoset
    a b a' b' ell m ell' m' hcubic u hu

private theorem rationalJet_shadowExcluded (place : Fin 3) :
    (ExceptionalIndependentPlane.rationalJet place).ShadowExcluded := by
  fin_cases place
  · exact rationalZeroJet_shadowExcluded
  · exact rationalOneJet_shadowExcluded
  · exact rationalInfinityJet_shadowExcluded

private theorem rationalPair_shadowExcluded (pair : Fin 3) :
    (ExceptionalIndependentPlane.rationalPair pair).ShadowExcluded := by
  fin_cases pair
  · exact rationalZeroOne_shadowExcluded
  · exact rationalZeroInfinity_shadowExcluded
  · exact rationalOneInfinity_shadowExcluded

/-- Unified canonical form of the seven independent exceptional shadow
exclusions. -/
theorem exceptionalIndependentPlane_shadow_not_missingCoset
    (P : ExceptionalIndependentPlane) : P.ShadowExcluded := by
  cases P with
  | rationalJet place => exact rationalJet_shadowExcluded place
  | rationalPair pair => exact rationalPair_shadowExcluded pair
  | degreeTwo => exact degreeTwo_shadowExcluded

private theorem add_right_self_cancel_twoForm (X Y : TwoForm) :
    (X + Y) + Y = X := by
  funext s
  simp only [Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Missing-coset exclusion transfers across an old-envelope correction. -/
theorem missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (X Y : TwoForm)
    (hXY : X + Y ∈ firstOrderEnvelopeTwoSpace)
    (hY : ∀ (u : TargetCoeff), u ∈ firstOrderEnvelopeCoeffSpace →
      Y ≠ targetTwo (firstOrderMissingCoeff + u))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    X ≠ targetTwo (firstOrderMissingCoeff + u) := by
  intro hX
  rcases hXY with ⟨c, hc, hcXY⟩
  apply hY (u + c) (firstOrderEnvelopeCoeffSpace.add_mem hu hc)
  symm
  apply move_targetEnvelope_across_missingCoset c u Y
  rw [hcXY, add_right_self_cancel_twoForm, hX]

/-- Target-valued members of the target-clean second jet with one adjoined
decomposable direction already belong to the first-order envelope. -/
theorem targetClean_sup_decomposable_target_mem_firstOrder
    (D defect : TwoForm) (hdefect : IsDecomposableTwo defect)
    (hDtarget : D ∈ targetTwoSpace)
    (hDclean : D ∈ targetCleanSecondJetSpace ⊔
      Submodule.span F₂ ({defect} : Set TwoForm)) :
    D ∈ firstOrderEnvelopeTwoSpace := by
  have hD : D ∈ targetTwoSpace ⊓
      (targetCleanSecondJetSpace ⊔
        Submodule.span F₂ ({defect} : Set TwoForm)) :=
    ⟨hDtarget, hDclean⟩
  rw [targetTwoSpace_inf_targetClean_sup_decomposable
    defect hdefect] at hD
  exact hD

/-- Decomposable-defect bridge for an actual low-product shadow comparison.
The preceding local shadow calculations supply `hclean`; this theorem turns
target-valuedness into membership in the old first-order envelope. -/
theorem envelope_shadow_of_targetClean
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c defect : TwoForm) (hdefect : IsDecomposableTwo defect)
    (htarget :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q c ∈ targetTwoSpace)
    (hclean :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q c ∈
        targetCleanSecondJetSpace ⊔
          Submodule.span F₂ ({defect} : Set TwoForm)) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q c ∈
      firstOrderEnvelopeTwoSpace :=
  targetClean_sup_decomposable_target_mem_firstOrder
    _ defect hdefect htarget hclean

/-- A target-clean low-product comparison with one decomposable defect cannot
represent the affine missing target coset. -/
theorem envelope_shadow_of_targetClean_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c defect : TwoForm) (hdefect : IsDecomposableTwo defect)
    (hclean :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q c ∈
        targetCleanSecondJetSpace ⊔
          Submodule.span F₂ ({defect} : Set TwoForm))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q c ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  have htarget :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q c ∈
        targetTwoSpace := by
    rw [hmissing]
    exact ⟨firstOrderMissingCoeff + u, rfl⟩
  have hfirst := envelope_shadow_of_targetClean
    a b a' b' ell m ell' m' q c defect hdefect htarget hclean
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    _ hfirst 0 0 0 0 u hu
  simpa using hmissing

end

end N5
end UnrestrictedBooleanMul
