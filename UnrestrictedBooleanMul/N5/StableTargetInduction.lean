import UnrestrictedBooleanMul.N5.StableTarget

/-!
# One-step induction for stable target envelopes

Stable suffix statements quantify over arbitrary finite AND suffixes.  This
module reduces such a statement to preservation by one legal AND extension
and extracts the exact product equation witnessed by any failing step.

No circuit or ANF space is enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The target part of every reachable state is preserved by one further
defect-legal AND extension. -/
def TargetStepClosed
    (W U : Submodule F₂ (ANF 10)) : Prop :=
  ∀ V p q,
    DefectLegalSuffix W V →
    p ∈ V → q ∈ V →
    N4.flagDefectRank (andExtend V p q) (mulTarget 5) ≤ 3 →
    V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ affine 10 ⊔ U →
    andExtend V p q ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      affine 10 ⊔ U

/-- Induction principle for the stable-target subspace used in the suffix
budget.  All geometric work is isolated in `TargetStepClosed`. -/
theorem stableTargetSubspace_of_targetStepClosed
    {W U : Submodule F₂ (ANF 10)}
    (hbase : W ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ affine 10 ⊔ U)
    (hstep : TargetStepClosed W U) :
    StableTargetSubspace W U := by
  intro V hreach
  induction hreach with
  | refl _ => exact hbase
  | @step V hreach p q hp hq hdef ih =>
      exact hstep V p q hreach hp hq hdef ih

/-- Any failure of one-step target containment supplies an actual target
word outside the proposed envelope and an old-wire correction whose sum with
the new product is that target word. -/
theorem exists_product_correction_of_targetStep_escape
    {V U : Submodule F₂ (ANF 10)} (p q : ANF 10)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ U)
    (hescape : ¬ (andExtend V p q ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ U)) :
    ∃ t v : ANF 10,
      t ∈ N4.targetAmbient 10 (mulTarget 5) ∧ t ∉ U ∧
      v ∈ V ∧ p * q = t + v := by
  rw [SetLike.not_le_iff_exists] at hescape
  rcases hescape with ⟨t, ht, htU⟩
  have htAmbient : t ∈ N4.targetAmbient 10 (mulTarget 5) := ht.2
  have htV : t ∉ V := by
    intro htV
    exact htU (hold ⟨htV, htAmbient⟩)
  rcases Submodule.mem_sup.mp ht.1 with ⟨v, hv, z, hz, hvz⟩
  rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
  have ha : a = 1 := by
    rcases f2_eq_zero_or_one a with ha | ha
    · subst a
      exfalso
      apply htV
      have hvt : v = t := by simpa using hvz
      exact hvt ▸ hv
    · exact ha
  subst a
  have hvz' : v + p * q = t := by simpa using hvz
  refine ⟨t, v, htAmbient, htU, hv, ?_⟩
  calc
    p * q = 0 + p * q := by rw [zero_add]
    _ = (v + v) + p * q := by rw [anf_add_self]
    _ = (v + p * q) + v := by ac_rfl
    _ = t + v := by rw [hvz']

end
end N5
end UnrestrictedBooleanMul
