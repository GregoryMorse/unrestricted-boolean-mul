import UnrestrictedBooleanMul.N5.CompletionDeficit

/-!
# Stable target-rank envelopes

This is the small interface between the algebraic feedback calculations and
the suffix-deficit ledger.  A stable bound quantifies over arbitrary finite
suffixes constrained only by total defect at most three; there is no replay
or gate-count search in the definition.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Every defect-legal suffix from `W` remains below target rank `b`. -/
def StableTargetRank (W : Submodule F₂ (ANF 10)) (b : Nat) : Prop :=
  ∀ V, DefectLegalSuffix W V → stateTargetRank V ≤ b

theorem StableTargetRank.mono {W : Submodule F₂ (ANF 10)} {a b : Nat}
    (h : StableTargetRank W a) (hab : a ≤ b) : StableTargetRank W b := by
  intro V hV
  exact (h V hV).trans hab

theorem suffixPostGain_le_of_stableTargetRank
    {W : Submodule F₂ (ANF 10)} {b : Nat}
    (hAff : affine 10 ≤ W)
    (hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3)
    (hstable : StableTargetRank W b) :
    suffixPostGain W ≤ b - stateTargetRank W := by
  rcases suffixPostGain_isSuffixGain W hdef with ⟨V, hreach, hgain⟩
  have hmono := stateTargetRank_mono hAff hreach.start_le
  have hbound := hstable V hreach
  unfold suffixTargetGain at hgain
  omega

theorem suffixDeficit_positive_of_stableTargetRank_eight
    {W : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ W)
    (hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3)
    (htarget : stateTargetRank W ≤ 8)
    (hstable : StableTargetRank W 8) :
    1 ≤ suffixDeficit W := by
  have hpost := suffixPostGain_le_of_stableTargetRank
    hAff hdef hstable
  unfold suffixDeficit
  omega

/-- A target subspace is an invariant envelope for every defect-legal suffix. -/
def StableTargetSubspace (W U : Submodule F₂ (ANF 10)) : Prop :=
  ∀ V, DefectLegalSuffix W V →
    V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ affine 10 ⊔ U

theorem stableTargetRank_of_subspace
    {W U : Submodule F₂ (ANF 10)} {b : Nat}
    (hAffW : affine 10 ≤ W)
    (hAffU : affine 10 ≤ U)
    (hUrank : Module.finrank F₂ U =
      Module.finrank F₂ (affine 10) + b)
    (hstable : StableTargetSubspace W U) :
    StableTargetRank W b := by
  intro V hreach
  have hdim := Submodule.finrank_mono (hstable V hreach)
  have hAffInf : affine 10 ≤
      V ⊓ N4.targetAmbient 10 (mulTarget 5) := by
    intro a ha
    exact ⟨hreach.affine_le hAffW ha,
      Submodule.mem_sup_left ha⟩
  have hbase := Submodule.finrank_mono hAffInf
  have hsup : affine 10 ⊔ U = U := sup_eq_right.mpr hAffU
  rw [hsup, hUrank] at hdim
  unfold stateTargetRank N4.flagTargetRank
  omega

end
end N5
end UnrestrictedBooleanMul
