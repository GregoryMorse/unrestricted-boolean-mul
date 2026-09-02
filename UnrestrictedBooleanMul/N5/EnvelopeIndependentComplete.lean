import UnrestrictedBooleanMul.N5.EnvelopePlaneClassification

/-!
# Complete shadow exclusion for two independent first-order planes

The intrinsic classification is combined with the existing distinct-plane,
exceptional-plane, degree-two-translate, and regular rational-value shadow
theorems.  Equal planes are transported by spans, so no coordinate or circuit
enumeration is introduced here.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The missing first-order target coset cannot be the quadratic shadow of
two products whose quadratic directions are both independent. -/
theorem independentFirstOrderPlanes_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases independentFirstOrderPlane_intrinsic_classification q c hq hc hind with
    hrigid | hexceptional | htranslate | hregular
  · exact independentClassifiedFirstOrderPlanes_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c'
      hq hc hq' hc' hind hind' (Or.inl hrigid) hhigh u hu
  · exact independentClassifiedFirstOrderPlanes_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c'
      hq hc hq' hc' hind hind' (Or.inr hexceptional) hhigh u hu
  · by_cases hsame : ∃ k : PlaneBasisChange,
        q' = (k.basisPair q c).1 ∧ c' = (k.basisPair q c).2
    · rcases htranslate with ⟨g, hqg, hcg⟩
      rcases hsame with ⟨h, hqh, hch⟩
      have hspan : Submodule.span F₂ ({q', c'} : Set TwoForm) =
          Submodule.span F₂
            ({degreeTwoTranslateLeftTwo,
              degreeTwoTranslateRightTwo} : Set TwoForm) := by
        calc
          Submodule.span F₂ ({q', c'} : Set TwoForm) =
              Submodule.span F₂ ({q, c} : Set TwoForm) := by
            rw [hqh, hch]
            exact h.span_basisPair_eq q c
          _ = Submodule.span F₂
              ({degreeTwoTranslateLeftTwo,
                degreeTwoTranslateRightTwo} : Set TwoForm) := by
            rw [hqg, hcg]
            exact g.span_basisPair_eq degreeTwoTranslateLeftTwo
              degreeTwoTranslateRightTwo
      rcases exists_planeBasisChange_of_span_eq
          degreeTwoTranslateLeftTwo degreeTwoTranslateRightTwo q' c'
          hind' hspan with ⟨k, hqk, hck⟩
      have hhigh' := hhigh
      rw [hqg, hcg, hqk, hck] at hhigh'
      have hexcluded := sharedDegreeTwoTranslatePlane_shadow_not_missingCoset
        g k a b a' b' ell m ell' m' hhigh' u hu
      rw [hqg, hcg, hqk, hck]
      exact hexcluded
    · exact independentDistinctFirstOrderPlanes_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
        hq hc hq' hc' hind hind'
        (fun k hk => hsame ⟨k, hk⟩) hhigh u hu
  · by_cases hsame : ∃ k : PlaneBasisChange,
        q' = (k.basisPair q c).1 ∧ c' = (k.basisPair q c).2
    · rcases hregular with ⟨place, d, g, hd, hdregular, hqg, hcg⟩
      rcases hsame with ⟨h, hqh, hch⟩
      have hspan : Submodule.span F₂ ({q', c'} : Set TwoForm) =
          Submodule.span F₂
            ({targetTwo (rationalValueCoeff place),
              targetTwo d} : Set TwoForm) := by
        calc
          Submodule.span F₂ ({q', c'} : Set TwoForm) =
              Submodule.span F₂ ({q, c} : Set TwoForm) := by
            rw [hqh, hch]
            exact h.span_basisPair_eq q c
          _ = Submodule.span F₂
              ({targetTwo (rationalValueCoeff place),
                targetTwo d} : Set TwoForm) := by
            rw [hqg, hcg]
            exact g.span_basisPair_eq
              (targetTwo (rationalValueCoeff place)) (targetTwo d)
      rcases exists_planeBasisChange_of_span_eq
          (targetTwo (rationalValueCoeff place)) (targetTwo d) q' c'
          hind' hspan with ⟨k, hqk, hck⟩
      have hhigh' := hhigh
      rw [hqg, hcg, hqk, hck] at hhigh'
      have hdTwo : targetTwo d ∈ firstOrderEnvelopeTwoSpace :=
        ⟨d, hd, rfl⟩
      have hexcluded := sharedRationalValueRegularPlane_shadow_not_missingCoset
        place (targetTwo d) hdTwo hdregular g k
        a b a' b' ell m ell' m' hhigh' u hu
      rw [hqg, hcg, hqk, hck]
      exact hexcluded
    · exact independentDistinctFirstOrderPlanes_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
        hq hc hq' hc' hind hind'
        (fun k hk => hsame ⟨k, hk⟩) hhigh u hu

end
end N5
end UnrestrictedBooleanMul
