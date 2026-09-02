import UnrestrictedBooleanMul.N5.EnvelopeDependentAlgebra
import UnrestrictedBooleanMul.N5.EnvelopeComplete
import UnrestrictedBooleanMul.N5.EnvelopeIndependentComplete

/-!
# Complete first-order envelope shadow exclusion

The remaining dependent/dependent case is reduced by independent changes of
basis to two zero-left planes.  The symmetric Koszul decomposition then puts
their total quadratic shadow in the old envelope plus two decomposable forms.
Together with the already checked independent cases, this gives the uniform
first-order envelope theorem.  The proof is entirely algebraic.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The missing first-order target coset cannot be the quadratic shadow of
two products whose quadratic direction pairs are both dependent. -/
theorem dependentDependentFirstOrderPlanes_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hdep' : ¬ LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases exists_planeBasisChange_zero_left_of_dependent q c hdep with
    ⟨g, d, hg⟩
  rcases exists_planeBasisChange_zero_left_of_dependent q' c' hdep' with
    ⟨k, e, hk⟩
  let ab := g.basisPair a b
  let lm := g.basisPair ell m
  let ab' := k.basisPair a' b'
  let lm' := k.basisPair ell' m'
  have hd : d ∈ firstOrderEnvelopeTwoSpace := by
    have hpair := g.basisPair_mem_submodule firstOrderEnvelopeTwoSpace
      q c hq hc
    rw [hg] at hpair
    exact hpair.2
  have he : e ∈ firstOrderEnvelopeTwoSpace := by
    have hpair := k.basisPair_mem_submodule firstOrderEnvelopeTwoSpace
      q' c' hq' hc'
    rw [hk] at hpair
    exact hpair.2
  have hchangedHigh :
      changedLowProductHighPart g ell m q c =
        changedLowProductHighPart k ell' m' q' c' := by
    rw [planeBasisChange_high, planeBasisChange_high]
    exact hhigh
  have hnormalizedCubic :
      factorPlaneCubic lm.1 lm.2 0 d =
        factorPlaneCubic lm'.1 lm'.2 0 e := by
    have h := congrArg Prod.snd hchangedHigh
    simp only [changedLowProductHighPart] at h
    rw [hg, hk] at h
    exact h
  have hchangedExcluded : ∀ (v : TargetCoeff),
      v ∈ firstOrderEnvelopeCoeffSpace →
        changedLowProductQuadraticShadow g a b ell m q c +
            changedLowProductQuadraticShadow k a' b' ell' m' q' c' ≠
          targetTwo (firstOrderMissingCoeff + v) := by
    intro v hv hmissing
    rcases zeroLeftCubic_shadow_decomposition firstOrderEnvelopeTwoSpace
        ab.1 ab.2 ab'.1 ab'.2 lm.1 lm.2 lm'.1 lm'.2 d e
        hd he hnormalizedCubic with
      ⟨r, hr, p, s, x, y, hdecomp⟩
    apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
      r hr p s x y v hv
    apply hdecomp.symm.trans
    have hnormalizedShadow :
        changedLowProductQuadraticShadow g a b ell m q c +
            changedLowProductQuadraticShadow k a' b' ell' m' q' c' =
          lowProductQuadraticShadow ab.1 ab.2 lm.1 lm.2 0 d +
            lowProductQuadraticShadow ab'.1 ab'.2 lm'.1 lm'.2 0 e := by
      simp only [changedLowProductQuadraticShadow, ab, lm, ab', lm']
      rw [hg, hk]
    exact hnormalizedShadow.symm.trans hmissing
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (lowProductQuadraticShadow a b ell m q c +
      lowProductQuadraticShadow a' b' ell' m' q' c')
    (changedLowProductQuadraticShadow g a b ell m q c +
      changedLowProductQuadraticShadow k a' b' ell' m' q' c')
  · have hcorrection := twoPlaneBasisChanges_shadow_sum_add_original_mem
      firstOrderEnvelopeTwoSpace g k a b a' b' ell m ell' m' q c q' c'
        hq hc hq' hc'
    simpa only [add_comm] using hcorrection
  · exact hchangedExcluded
  · exact hu

/-- Uniform missing-coset exclusion for two low products supported in the
first-order envelope, with no independence hypothesis on either plane. -/
theorem envelope_shadow
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  by_cases hind : LinearIndependent F₂ (quadraticPlaneDirections q c)
  · by_cases hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c')
    · exact independentFirstOrderPlanes_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hind hind' hhigh u hu
    · exact independentDependentFirstOrderPlanes_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hind hind' hhigh u hu
  · by_cases hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c')
    · exact dependentIndependentFirstOrderPlanes_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hind hind' hhigh u hu
    · exact dependentDependentFirstOrderPlanes_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hind hind' hhigh u hu

end
end N5
end UnrestrictedBooleanMul
