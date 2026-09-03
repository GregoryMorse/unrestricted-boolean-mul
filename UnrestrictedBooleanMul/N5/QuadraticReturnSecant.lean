import UnrestrictedBooleanMul.N5.QuadraticReturn
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
