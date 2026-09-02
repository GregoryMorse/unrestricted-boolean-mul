import UnrestrictedBooleanMul.N5.EnvelopeSemantic
import UnrestrictedBooleanMul.N5.EnvelopeTwoRotationExact

/-!
# Literal Boolean first-order envelope semantics

The quartic plane classifier is reused unchanged, but every branch is fed by
equality in the actual Boolean high quotient.  Equal planes use invariance of
the quadratic--quadratic overlap; distinct planes use the exact one- and
two-local rotation theorems.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Exact high-class exclusion for two distinct independent first-order
factor planes. -/
theorem independentDistinctFirstOrderPlanes_exact_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hdistinct : ∀ g : PlaneBasisChange,
      ¬ (q' = (g.basisPair q c).1 ∧ c' = (g.basisPair q c).2))
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hfour : ambientWedgeTwo q c = ambientWedgeTwo q' c' :=
    ambientWedgeTwo_eq_of_highClass_eq
      ell m ell' m' q c q' c' hhigh
  rcases independentFirstOrderPlane_classification_of_ambientWedge_eq
      q c q' c' hq hc hq' hc' hind hind' hfour with
    hsame | ⟨x, y, z, w, hx, hy, hz, hw, hlocal⟩
  · rcases hsame with ⟨g, hqg, hcg⟩
    exact (hdistinct g ⟨hqg, hcg⟩).elim
  · rcases hlocal with hone | htwo
    · rcases hone with ⟨place, hdiff⟩
      apply oneLocalKernelDifference_exact_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c' x y z w place
        hq hc hq' hc'
      · simpa only [exactFirstOrderTwoMap_apply] using hx
      · simpa only [exactFirstOrderTwoMap_apply] using hy
      · simpa only [exactFirstOrderTwoMap_apply] using hz
      · simpa only [exactFirstOrderTwoMap_apply] using hw
      · exact hind
      · exact hind'
      · exact hdiff
      · exact hhigh
      · exact hu
    · rcases htwo with ⟨place, other, hne, hdiff⟩
      apply twoLocalKernelDifference_exact_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c' x y z w place other
        hq hc hq' hc'
      · simpa only [exactFirstOrderTwoMap_apply] using hx
      · simpa only [exactFirstOrderTwoMap_apply] using hy
      · simpa only [exactFirstOrderTwoMap_apply] using hz
      · simpa only [exactFirstOrderTwoMap_apply] using hw
      · exact hind
      · exact hind'
      · exact hne
      · exact hdiff
      · exact hhigh
      · exact hu

/-- Uniform exact exclusion for two independent first-order planes. -/
theorem independentFirstOrderPlanes_exact_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  by_cases hsame : ∃ g : PlaneBasisChange,
      q' = (g.basisPair q c).1 ∧ c' = (g.basisPair q c).2
  · rcases hsame with ⟨g, hqg, hcg⟩
    apply semanticEnvelope_shadow
      a b a' b' ell m ell' m' q c q' c'
        hq hc hq' hc' hhigh
    · rw [hqg, hcg]
      exact (quadraticOverlapCubic_basisPair g q c).symm
    · exact hu
  · exact independentDistinctFirstOrderPlanes_exact_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c'
        hq hc hq' hc' hind hind'
        (fun g hg => hsame ⟨g, hg⟩) hhigh u hu

@[simp] theorem quadraticOverlapCubic_eq_zero_of_dependent
    (q c : TwoForm)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    quadraticOverlapCubic q c = 0 := by
  rcases quadraticPlaneDirections_dependent_classification q c hdep with
    hq | hc | hqc
  · subst q
    exact quadraticOverlapCubic_zero_left c
  · subst c
    exact quadraticOverlapCubic_zero_right q
  · subst c
    exact quadraticOverlapCubic_self q

/-- Presentation-free exact rational-local/dependent exclusion. -/
theorem rationalJetPresentation_exact_dependent_shadow_not_missingCoset
    (place : Fin 3)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hpresentation : IsRationalJetPresentation place q c)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases hpresentation with ⟨g, hqg, hcg⟩
  rcases exists_planeBasisChange_zero_left_of_dependent q' c' hdep with
    ⟨k, d, hk⟩
  let ab := g.inverse.basisPair a b
  let lm := g.inverse.basisPair ell m
  let abDep := k.basisPair a' b'
  let lmDep := k.basisPair ell' m'
  let P := ExceptionalIndependentPlane.rationalJet place
  let changedLocal := changedLowProductQuadraticShadow g
    ab.1 ab.2 lm.1 lm.2 P.left P.right
  let canonicalLocal := lowProductQuadraticShadow
    ab.1 ab.2 lm.1 lm.2 P.left P.right
  let changedDependent := changedLowProductQuadraticShadow k
    a' b' ell' m' q' c'
  let actualLocal := lowProductQuadraticShadow a b ell m q c
  let actualDependent := lowProductQuadraticShadow a' b' ell' m' q' c'
  have hdmem : d ∈ firstOrderEnvelopeTwoSpace := by
    have hpair := k.basisPair_mem_submodule firstOrderEnvelopeTwoSpace
      q' c' hq' hc'
    rw [hk] at hpair
    exact hpair.2
  rcases hdmem with ⟨dc, hdc, hdcEq⟩
  have hdcEq' : targetTwo dc = d := hdcEq
  have hlocalEq : changedLocal = actualLocal := by
    have hinverse := changedLowProductQuadraticShadow_inverse
      g a b ell m P.left P.right
    simpa [changedLocal, actualLocal, ab, lm, P, hqg, hcg] using hinverse
  have hdependentEq : changedDependent =
      lowProductQuadraticShadow abDep.1 abDep.2 lmDep.1 lmDep.2 0 d := by
    simp only [changedDependent, changedLowProductQuadraticShadow,
      abDep, lmDep]
    rw [hk]
  have hlocalHigh : lowProductHighClass lm.1 lm.2 P.left P.right =
      lowProductHighClass ell m q c := by
    have hinvariant := g.lowProductHighClass_basisPair
      lm.1 lm.2 P.left P.right
    have hlinear : g.basisPair lm.1 lm.2 = (ell, m) := by
      simpa only [lm] using g.basisPair_apply_inverse ell m
    rw [hlinear, ← hqg, ← hcg] at hinvariant
    exact hinvariant.symm
  have hdependentHigh :
      lowProductHighClass lmDep.1 lmDep.2 0 d =
        lowProductHighClass ell' m' q' c' := by
    have hinvariant := k.lowProductHighClass_basisPair ell' m' q' c'
    rw [hk] at hinvariant
    change lowProductHighClass lmDep.1 lmDep.2 0 d =
      lowProductHighClass ell' m' q' c'
    exact hinvariant
  have hcanonicalHigh :
      lowProductHighClass lm.1 lm.2 P.left P.right =
        lowProductHighClass lmDep.1 lmDep.2 0 (targetTwo dc) := by
    calc
      _ = lowProductHighClass ell m q c := hlocalHigh
      _ = lowProductHighClass ell' m' q' c' := hhigh
      _ = lowProductHighClass lmDep.1 lmDep.2 0 d :=
        hdependentHigh.symm
      _ = lowProductHighClass lmDep.1 lmDep.2 0 (targetTwo dc) := by
        rw [hdcEq']
  have hcanonicalCubic :
      exactLowProductCubic lm.1 lm.2 P.left P.right =
        exactLowProductCubic lmDep.1 lmDep.2 0 (targetTwo dc) :=
    exactLowProductCubic_eq_of_highClass_eq
      _ _ _ _ _ _ _ _ hcanonicalHigh
  have hlocalCorrection : changedLocal + canonicalLocal ∈
      firstOrderEnvelopeTwoSpace := by
    exact (exceptionalPlane_basisChange_high_and_shadow
      (.rationalJet place) g ab.1 ab.2 lm.1 lm.2).2
  have hdependentCorrection : changedDependent + actualDependent ∈
      firstOrderEnvelopeTwoSpace := by
    exact (planeBasisChange_high_and_shadow_mod_submodule
      firstOrderEnvelopeTwoSpace k a' b' ell' m' q' c' hq' hc').2
  have hchangedExcluded : ∀ (v : TargetCoeff),
      v ∈ firstOrderEnvelopeCoeffSpace →
      canonicalLocal + changedDependent ≠
        targetTwo (firstOrderMissingCoeff + v) := by
    intro v hv
    rw [hdependentEq, ← hdcEq']
    exact rationalJet_actual_exact_local_dependent_shadow_not_missingCoset
      place ab.1 ab.2 abDep.1 abDep.2 lm.1 lm.2 lmDep.1 lmDep.2
        dc hdc hcanonicalCubic v hv
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (actualLocal + actualDependent) (canonicalLocal + changedDependent)
  · have hreassoc :
        (actualLocal + actualDependent) +
            (canonicalLocal + changedDependent) =
          (changedLocal + canonicalLocal) +
            (changedDependent + actualDependent) := by
      rw [← hlocalEq]
      module
    rw [hreassoc]
    exact firstOrderEnvelopeTwoSpace.add_mem
      hlocalCorrection hdependentCorrection
  · exact hchangedExcluded
  · exact hu

/-- Exact mixed-plane exclusion with the independent plane first. -/
theorem independentDependentFirstOrderPlanes_exact_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hdepWedge := ambientWedgeTwo_eq_zero_of_dependent q' c' hdep
  have hlocalWedge : ambientWedgeTwo q c = 0 := by
    have hfour := ambientWedgeTwo_eq_of_highClass_eq
      ell m ell' m' q c q' c' hhigh
    rw [hdepWedge] at hfour
    exact hfour
  rcases isRationalJetPresentation_of_independent_ambientWedge_eq_zero
      q c hq hc hind hlocalWedge with ⟨place, hpresentation⟩
  exact rationalJetPresentation_exact_dependent_shadow_not_missingCoset
    place a b a' b' ell m ell' m' q c q' c'
      hq' hc' hpresentation hdep hhigh u hu

/-- Exact mixed-plane exclusion with the dependent plane first. -/
theorem dependentIndependentFirstOrderPlanes_exact_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  simpa only [add_comm] using
    independentDependentFirstOrderPlanes_exact_shadow_not_missingCoset
      a' b' a b ell' m' ell m q' c' q c
        hq' hc' hq hc hind' hdep hhigh.symm u hu

/-- Uniform literal-high-quotient shadow exclusion for two products whose
quadratic factors lie in the first-order envelope. -/
theorem semanticEnvelope_exact_shadow
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  by_cases hind : LinearIndependent F₂ (quadraticPlaneDirections q c)
  · by_cases hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c')
    · exact independentFirstOrderPlanes_exact_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hind hind' hhigh u hu
    · exact independentDependentFirstOrderPlanes_exact_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hind hind' hhigh u hu
  · by_cases hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c')
    · exact dependentIndependentFirstOrderPlanes_exact_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hind hind' hhigh u hu
    · apply semanticEnvelope_shadow
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hhigh
      · rw [quadraticOverlapCubic_eq_zero_of_dependent q c hind,
          quadraticOverlapCubic_eq_zero_of_dependent q' c' hind']
      · exact hu

end
end N5
end UnrestrictedBooleanMul
