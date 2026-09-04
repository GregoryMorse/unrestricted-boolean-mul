import UnrestrictedBooleanMul.N5.QuadraticReturn
import UnrestrictedBooleanMul.N5.EnvelopeDependentComplete
import UnrestrictedBooleanMul.N5.RankOneShadow

/-!
# Target geometry of a quadratic return section

An equal-high return has a quadratic shadow which, in every classified
first-order plane, is an old-envelope form plus two decomposable forms.  Such
a rank-four secant section cannot by itself expose the unique target
coordinate missing from the first-order envelope.

This is a linear/exterior-algebra statement.  It does not assert the false
claim that the returned section is decomposable, and it does not enumerate
Boolean functions or circuits.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- A one-dimensional quadratic section does not enlarge the target
intersection once every translate of the missing first-order target class is
excluded.  This is the linear-algebra wrapper around the complete envelope
shadow theorem; it uses no rank assumption on the section. -/
theorem targetTwoSpace_inf_firstOrderEnvelope_sup_of_missingCoset_exclusion
    (z : TwoForm)
    (hz : ∀ u : TargetCoeff, u ∈ firstOrderEnvelopeCoeffSpace →
      z ≠ targetTwo (firstOrderMissingCoeff + u)) :
    targetTwoSpace ⊓
        (firstOrderEnvelopeTwoSpace ⊔
          Submodule.span F₂ ({z} : Set TwoForm)) =
      firstOrderEnvelopeTwoSpace := by
  apply le_antisymm
  · rintro p ⟨hpTarget, hpSection⟩
    rcases hpTarget with ⟨c, rfl⟩
    rcases Submodule.mem_sup.mp hpSection with ⟨w, hw, s, hs, hws⟩
    rcases Submodule.mem_span_singleton.mp hs with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with ha | ha
    · rw [ha, zero_smul, add_zero] at hws
      rw [← hws]
      exact hw
    · rw [ha, one_smul] at hws
      by_cases hcEnvelope : c ∈ firstOrderEnvelopeCoeffSpace
      · exact ⟨c, hcEnvelope, rfl⟩
      · have hfunctionalNe : firstOrderMissingFunctional c ≠ 0 := by
          intro hzero
          exact hcEnvelope ((mem_firstOrderEnvelopeCoeffSpace c).2 hzero)
        have hfunctional : firstOrderMissingFunctional c = 1 :=
          (f2_eq_zero_or_one (firstOrderMissingFunctional c)).resolve_left
            hfunctionalNe
        let c₀ := c + firstOrderMissingCoeff
        have hc₀ : c₀ ∈ firstOrderEnvelopeCoeffSpace := by
          rw [mem_firstOrderEnvelopeCoeffSpace]
          simp [c₀, hfunctional, CharTwo.add_self_eq_zero]
        have hcSplit : c = firstOrderMissingCoeff + c₀ := by
          change c = firstOrderMissingCoeff +
            (c + firstOrderMissingCoeff)
          ext i
          calc
            c i = c i + 0 := (add_zero (c i)).symm
            _ = c i +
                (firstOrderMissingCoeff i + firstOrderMissingCoeff i) := by
              rw [CharTwo.add_self_eq_zero]
            _ = firstOrderMissingCoeff i +
                (c i + firstOrderMissingCoeff i) := by ac_rfl
        have hcancel : (w + z) + z = w := by
          have hzz : z + z = 0 := by
            funext s
            exact CharTwo.add_self_eq_zero (z s)
          rw [add_assoc, hzz, add_zero]
        have hsumExcluded :
            w + z ≠ targetTwo (firstOrderMissingCoeff + c₀) := by
          apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
            (w + z) z
          · rw [hcancel]
            exact hw
          · exact hz
          · exact hc₀
        exfalso
        apply hsumExcluded
        calc
          w + z = targetTwo c := hws
          _ = targetTwo (firstOrderMissingCoeff + c₀) := by rw [hcSplit]
  · intro p hp
    exact ⟨firstOrderEnvelopeTwoSpace_le_targetTwoSpace hp,
      Submodule.mem_sup_left hp⟩

/-- Universal target geometry of an equal-high quadratic return supported on
the first-order envelope.  The two products may use different, dependent or
independent quadratic planes.  The complete algebraic shadow theorem excludes
the missing target coset, and the preceding wrapper shows that adjoining the
returned quadratic section exposes no new target direction. -/
theorem targetTwoSpace_inf_firstOrderEnvelope_sup_equalHighShadow
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c') :
    let z := lowProductQuadraticShadow a b ell m q c +
      lowProductQuadraticShadow a' b' ell' m' q' c'
    targetTwoSpace ⊓
        (firstOrderEnvelopeTwoSpace ⊔
          Submodule.span F₂ ({z} : Set TwoForm)) =
      firstOrderEnvelopeTwoSpace := by
  apply targetTwoSpace_inf_firstOrderEnvelope_sup_of_missingCoset_exclusion
  intro u hu
  exact envelope_shadow a b a' b' ell m ell' m' q c q' c'
    hq hc hq' hc' hhigh u hu

/-- Adjoining a quadratic section which is an old first-order form plus two
wedges does not enlarge the target intersection of the first-order envelope.

The key point is the coefficient-one branch: a new target would identify a
member of the missing Hankel coset with an old-envelope form plus two
decomposable forms, contradicting `missingCoset_not_sum_two_decomposable`. -/
theorem targetTwoSpace_inf_firstOrderEnvelope_sup_twoWedgeSection
    (z r : TwoForm) (hr : r ∈ firstOrderEnvelopeTwoSpace)
    (u v x y : LinearForm)
    (hz : z = r + squarefreeWedge u v + squarefreeWedge x y) :
    targetTwoSpace ⊓
        (firstOrderEnvelopeTwoSpace ⊔
          Submodule.span F₂ ({z} : Set TwoForm)) =
      firstOrderEnvelopeTwoSpace := by
  apply le_antisymm
  · rintro p ⟨hpTarget, hpSection⟩
    rcases hpTarget with ⟨c, rfl⟩
    rcases Submodule.mem_sup.mp hpSection with ⟨w, hw, s, hs, hws⟩
    rcases Submodule.mem_span_singleton.mp hs with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with ha | ha
    · rw [ha, zero_smul, add_zero] at hws
      rw [← hws]
      exact hw
    · rw [ha, one_smul] at hws
      by_cases hcEnvelope : c ∈ firstOrderEnvelopeCoeffSpace
      · exact ⟨c, hcEnvelope, rfl⟩
      · have hfunctionalNe : firstOrderMissingFunctional c ≠ 0 := by
          intro hzero
          exact hcEnvelope ((mem_firstOrderEnvelopeCoeffSpace c).2 hzero)
        have hfunctional : firstOrderMissingFunctional c = 1 :=
          (f2_eq_zero_or_one (firstOrderMissingFunctional c)).resolve_left
            hfunctionalNe
        let c₀ := c + firstOrderMissingCoeff
        have hc₀ : c₀ ∈ firstOrderEnvelopeCoeffSpace := by
          rw [mem_firstOrderEnvelopeCoeffSpace]
          simp [c₀, hfunctional, CharTwo.add_self_eq_zero]
        have hcSplit : c = firstOrderMissingCoeff + c₀ := by
          change c = firstOrderMissingCoeff +
            (c + firstOrderMissingCoeff)
          ext i
          calc
            c i = c i + 0 := (add_zero (c i)).symm
            _ = c i +
                (firstOrderMissingCoeff i + firstOrderMissingCoeff i) := by
              rw [CharTwo.add_self_eq_zero]
            _ = firstOrderMissingCoeff i +
                (c i + firstOrderMissingCoeff i) := by ac_rfl
        exfalso
        apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
          (w + r) (firstOrderEnvelopeTwoSpace.add_mem hw hr)
          u v x y c₀ hc₀
        calc
          (w + r) + squarefreeWedge u v + squarefreeWedge x y =
              w + (r + squarefreeWedge u v + squarefreeWedge x y) := by
            ac_rfl
          _ = w + z := by rw [hz]
          _ = targetTwo c := hws
          _ = targetTwo (firstOrderMissingCoeff + c₀) := by rw [hcSplit]
  · intro p hp
    exact ⟨firstOrderEnvelopeTwoSpace_le_targetTwoSpace hp,
      Submodule.mem_sup_left hp⟩

end
end N5
end UnrestrictedBooleanMul
