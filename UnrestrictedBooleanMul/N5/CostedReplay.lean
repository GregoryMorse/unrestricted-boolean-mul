import UnrestrictedBooleanMul.N5.CostedSuffix

/-!
# Cost-preserving suffix replay

Replaying a suffix from a larger state of the same target-quotient defect may
make some of the original gates redundant.  This file performs that replay
gate by gate and deletes exactly those redundant extensions.  Besides the
remaining gate count, it records the exact dimension increase of the replay
state, so every retained gate is certified nonredundant without storing a
separate gate list.

This is the structural deletion step in the manuscript's intrinsic-capacity
replay.  It is purely linear algebra on submodules and does not enumerate
circuits or Boolean functions.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- If an exact-cost suffix has gained one dimension at every retained gate,
then its length is exactly its target gain plus its target-quotient defect
gain. -/
theorem CostedDefectLegalSuffix.length_eq_totalGain_of_finrank_eq
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (hAff : affine 10 ≤ W)
    (hreach : CostedDefectLegalSuffix W k V)
    (hdim : Module.finrank F₂ V = Module.finrank F₂ W + k) :
    k = suffixTargetGain W V +
      (N4.flagDefectRank V (mulTarget 5) -
        N4.flagDefectRank W (mulTarget 5)) := by
  have hAffV : affine 10 ≤ V := hreach.affine_le hAff
  have hstart := stateTargetRank_add_flagDefectRank W hAff
  have hfinal := stateTargetRank_add_flagDefectRank V hAffV
  have htarget : stateTargetRank W ≤ stateTargetRank V :=
    stateTargetRank_mono hAff hreach.start_le
  have hdefect : N4.flagDefectRank W (mulTarget 5) ≤
      N4.flagDefectRank V (mulTarget 5) :=
    flagDefectRank_mono hreach.start_le
  have hAffDim : Module.finrank F₂ (affine 10) ≤ Module.finrank F₂ W :=
    Submodule.finrank_mono hAff
  unfold suffixTargetGain
  omega

/-- Run an exact-cost suffix from a larger base with the same initial defect,
deleting a gate whenever its product is already in the replay state.  The
replay endpoint is the sum of the larger base and the original endpoint.
Every retained gate raises dimension, hence the endpoint dimension grows by
exactly the retained length. -/
theorem CostedDefectLegalSuffix.prune_simulate_from_equal_defect
    {W' W V : Submodule F₂ (ANF 10)} {k : Nat}
    (hsub : W' ≤ W)
    (heq : N4.flagDefectRank W' (mulTarget 5) =
      N4.flagDefectRank W (mulTarget 5))
    (hWdef : N4.flagDefectRank W (mulTarget 5) ≤ 3)
    (hreach : CostedDefectLegalSuffix W' k V) :
    ∃ k' ≤ k,
      CostedDefectLegalSuffix W k' (W ⊔ V) ∧
      Module.finrank F₂ ↥(W ⊔ V) = Module.finrank F₂ W + k' := by
  induction hreach with
  | refl hdef =>
      refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · simpa [sup_eq_left.mpr hsub] using
          (CostedDefectLegalSuffix.refl (W := W) hWdef)
      · rw [sup_eq_left.mpr hsub]
  | @step k V hreach p q hp hq hdef ih =>
      rcases ih with ⟨k', hk', hsim, hdim⟩
      let B := W ⊔ V
      have hpB : p ∈ B := (le_sup_right : V ≤ W ⊔ V) hp
      have hqB : q ∈ B := (le_sup_right : V ≤ W ⊔ V) hq
      have hsmall : W' ≤ andExtend V p q :=
        hreach.start_le.trans le_sup_left
      have hlargeDef : N4.flagDefectRank
          (W ⊔ andExtend V p q) (mulTarget 5) ≤ 3 := by
        rw [flagDefectRank_sup_eq_right_of_equal_base hsub hsmall heq]
        exact hdef
      have hstate : W ⊔ andExtend V p q = andExtend B p q := by
        simp only [B, andExtend, sup_assoc]
      have hnextDef : N4.flagDefectRank (andExtend B p q)
          (mulTarget 5) ≤ 3 := by
        rw [← hstate]
        exact hlargeDef
      by_cases hproduct : p * q ∈ B
      · have hspan : Submodule.span F₂ ({p * q} : Set (ANF 10)) ≤ B := by
          rw [Submodule.span_le]
          simpa using hproduct
        have hrefl : andExtend B p q = B := by
          exact sup_eq_left.mpr hspan
        have hendpoint : W ⊔ andExtend V p q = B := by
          rw [hstate, hrefl]
        refine ⟨k', hk'.trans (Nat.le_succ k), ?_, ?_⟩
        · rwa [hendpoint]
        · rwa [hendpoint]
      · have hstep : CostedDefectLegalSuffix W (k' + 1)
            (andExtend B p q) :=
          CostedDefectLegalSuffix.step hsim p q hpB hqB hnextDef
        refine ⟨k' + 1, by omega, ?_, ?_⟩
        · rwa [hstate]
        · rw [hstate, andExtend,
            Submodule.finrank_sup_span_singleton hproduct, hdim]

end
end N5
end UnrestrictedBooleanMul
