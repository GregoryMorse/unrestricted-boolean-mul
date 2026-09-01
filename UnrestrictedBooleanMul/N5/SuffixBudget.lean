import UnrestrictedBooleanMul.N5.PrefixState

/-!
# Defect-legal unrestricted suffixes

This file defines the stable suffix budget used in the manuscript.  A suffix
has arbitrary finite length; its only restriction is that every intermediate
wire state has total quotient defect at most three.  The main result is the
correct deficit monotonicity statement for inclusions of equal defect-two
states.  In particular, it does not assert the false raw monotonicity of the
post-prefix gain.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Target rank of an arbitrary wire state. -/
def stateTargetRank (V : Submodule F₂ (ANF 10)) : Nat :=
  N4.flagTargetRank V (mulTarget 5)

/-- One legal unrestricted AND extension of a wire state. -/
def andExtend (V : Submodule F₂ (ANF 10)) (p q : ANF 10) :
    Submodule F₂ (ANF 10) :=
  V ⊔ Submodule.span F₂ {p * q}

/-- Arbitrary finite suffix reachability under the sole global condition that
the quotient defect never exceeds three. -/
inductive DefectLegalSuffix (W : Submodule F₂ (ANF 10)) :
    Submodule F₂ (ANF 10) → Prop
  | refl (hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3) :
      DefectLegalSuffix W W
  | step {V : Submodule F₂ (ANF 10)}
      (hreach : DefectLegalSuffix W V)
      (p q : ANF 10) (hp : p ∈ V) (hq : q ∈ V)
      (hdef : N4.flagDefectRank (andExtend V p q) (mulTarget 5) ≤ 3) :
      DefectLegalSuffix W (andExtend V p q)

theorem DefectLegalSuffix.start_le {W V : Submodule F₂ (ANF 10)}
    (h : DefectLegalSuffix W V) : W ≤ V := by
  induction h with
  | refl => exact le_rfl
  | step hreach p q hp hq hdef ih =>
      exact ih.trans le_sup_left

theorem DefectLegalSuffix.final_defect_le_three
    {W V : Submodule F₂ (ANF 10)} (h : DefectLegalSuffix W V) :
    N4.flagDefectRank V (mulTarget 5) ≤ 3 := by
  cases h with
  | refl hdef => exact hdef
  | step hreach p q hp hq hdef => exact hdef

theorem DefectLegalSuffix.affine_le {W V : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ W) (h : DefectLegalSuffix W V) :
    affine 10 ≤ V := hAff.trans h.start_le

/-- Target rank is monotone for wire-state inclusions containing the affine
space. -/
theorem stateTargetRank_mono {V W : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ V) (hVW : V ≤ W) :
    stateTargetRank V ≤ stateTargetRank W := by
  have hInf : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      W ⊓ N4.targetAmbient 10 (mulTarget 5) :=
    inf_le_inf hVW le_rfl
  have hdim := Submodule.finrank_mono hInf
  have hAffInf : affine 10 ≤
      V ⊓ N4.targetAmbient 10 (mulTarget 5) := by
    intro a ha
    exact ⟨hAff ha, Submodule.mem_sup_left ha⟩
  have hbase := Submodule.finrank_mono hAffInf
  unfold stateTargetRank N4.flagTargetRank
  omega

/-- No state containing the affine inputs has target rank above nine. -/
theorem stateTargetRank_le_nine {V : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ V) : stateTargetRank V ≤ 9 := by
  have hInf : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      N4.targetAmbient 10 (mulTarget 5) := inf_le_right
  have hdim := Submodule.finrank_mono hInf
  have hAffInf : affine 10 ≤
      V ⊓ N4.targetAmbient 10 (mulTarget 5) := by
    intro a ha
    exact ⟨hAff ha, Submodule.mem_sup_left ha⟩
  have hbase := Submodule.finrank_mono hAffInf
  rw [targetAmbient_five_finrank] at hdim
  unfold stateTargetRank N4.flagTargetRank
  omega

/-- Target gain of a suffix endpoint relative to its initial state. -/
def suffixTargetGain (W V : Submodule F₂ (ANF 10)) : Nat :=
  stateTargetRank V - stateTargetRank W

/-- A target gain achieved by some finite defect-legal suffix. -/
def IsSuffixGain (W : Submodule F₂ (ANF 10)) (d : Nat) : Prop :=
  ∃ V, DefectLegalSuffix W V ∧ suffixTargetGain W V = d

/-- Maximum target gain over all finite suffixes of total defect at most
three.  The search bound is the intrinsic nine-dimensional target, not a
gate-count bound. -/
noncomputable def suffixPostGain (W : Submodule F₂ (ANF 10)) : Nat := by
  classical
  exact Nat.findGreatest (IsSuffixGain W) 9

theorem suffixTargetGain_le_nine {W V : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ W) (h : DefectLegalSuffix W V) :
    suffixTargetGain W V ≤ 9 := by
  have hmono := stateTargetRank_mono hAff h.start_le
  have htop := stateTargetRank_le_nine (h.affine_le hAff)
  unfold suffixTargetGain
  omega

theorem suffixPostGain_le_nine (W : Submodule F₂ (ANF 10)) :
    suffixPostGain W ≤ 9 := by
  classical
  exact Nat.findGreatest_le 9

theorem zero_isSuffixGain (W : Submodule F₂ (ANF 10))
    (hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3) :
    IsSuffixGain W 0 := by
  exact ⟨W, .refl hdef, by simp [suffixTargetGain]⟩

/-- The maximum post-prefix gain is itself achieved. -/
theorem suffixPostGain_isSuffixGain (W : Submodule F₂ (ANF 10))
    (hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3) :
    IsSuffixGain W (suffixPostGain W) := by
  classical
  exact Nat.findGreatest_spec (m := 0) (n := 9) (Nat.zero_le _)
    (zero_isSuffixGain W hdef)

theorem IsSuffixGain.le_suffixPostGain {W : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ W) {d : Nat} (hd : IsSuffixGain W d) :
    d ≤ suffixPostGain W := by
  classical
  rcases hd with ⟨V, hreach, rfl⟩
  apply Nat.le_findGreatest
  · exact suffixTargetGain_le_nine hAff hreach
  · exact ⟨V, hreach, rfl⟩

/-! ## Simulation from a larger equal-defect base -/

@[simp] theorem stateDefectImage_sup
    (V W : Submodule F₂ (ANF 10)) :
    stateDefectImage (V ⊔ W) = stateDefectImage V ⊔ stateDefectImage W := by
  exact Submodule.map_sup _ _ _

theorem stateDefectImage_eq_of_le_of_flagDefectRank_eq
    {V W : Submodule F₂ (ANF 10)} (hVW : V ≤ W)
    (hdef : N4.flagDefectRank V (mulTarget 5) =
      N4.flagDefectRank W (mulTarget 5)) :
    stateDefectImage V = stateDefectImage W := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.map_mono hVW
  · rw [stateDefectImage_finrank, stateDefectImage_finrank, hdef]

theorem flagDefectRank_sup_eq_right_of_equal_base
    {W' W V : Submodule F₂ (ANF 10)}
    (hsub : W' ≤ W) (hWV : W' ≤ V)
    (heq : N4.flagDefectRank W' (mulTarget 5) =
      N4.flagDefectRank W (mulTarget 5)) :
    N4.flagDefectRank (W ⊔ V) (mulTarget 5) =
      N4.flagDefectRank V (mulTarget 5) := by
  have himage := stateDefectImage_eq_of_le_of_flagDefectRank_eq hsub heq
  rw [← stateDefectImage_finrank, ← stateDefectImage_finrank,
    stateDefectImage_sup, ← himage]
  have hle : stateDefectImage W' ≤ stateDefectImage V :=
    Submodule.map_mono hWV
  rw [sup_eq_right.mpr hle]

/-- Run the same finite suffix from a larger base of equal initial defect.
The resulting state is the sum of the larger base and the original endpoint. -/
theorem DefectLegalSuffix.simulate_from_equal_defect
    {W' W V : Submodule F₂ (ANF 10)}
    (hsub : W' ≤ W)
    (heq : N4.flagDefectRank W' (mulTarget 5) =
      N4.flagDefectRank W (mulTarget 5))
    (hWdef : N4.flagDefectRank W (mulTarget 5) ≤ 3)
    (hreach : DefectLegalSuffix W' V) :
    DefectLegalSuffix W (W ⊔ V) := by
  induction hreach with
  | refl hdef =>
      simpa [sup_eq_left.mpr hsub] using DefectLegalSuffix.refl (W := W) hWdef
  | @step V hreach p q hp hq hdef ih =>
      have hpLarge : p ∈ W ⊔ V := (le_sup_right : V ≤ W ⊔ V) hp
      have hqLarge : q ∈ W ⊔ V := (le_sup_right : V ≤ W ⊔ V) hq
      have hsmall : W' ≤ andExtend V p q :=
        hreach.start_le.trans le_sup_left
      have hlargeDef : N4.flagDefectRank
          (W ⊔ andExtend V p q) (mulTarget 5) ≤ 3 := by
        rw [flagDefectRank_sup_eq_right_of_equal_base hsub hsmall heq]
        exact hdef
      have hstep := DefectLegalSuffix.step ih p q hpLarge hqLarge
        (by
          simpa only [andExtend, sup_assoc] using hlargeDef)
      simpa only [andExtend, sup_assoc] using hstep

/-- Manuscript Lemma 10.6, gain form.  Passing to a smaller base of the same
defect can increase the raw suffix gain, but by at most the target dimension
removed from the base. -/
theorem suffixPostGain_mono_corrected
    {W' W : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ W') (hsub : W' ≤ W)
    (hdef' : N4.flagDefectRank W' (mulTarget 5) = 2)
    (hdef : N4.flagDefectRank W (mulTarget 5) = 2) :
    suffixPostGain W' ≤ suffixPostGain W +
      (stateTargetRank W - stateTargetRank W') := by
  have htarget : stateTargetRank W' ≤ stateTargetRank W :=
    stateTargetRank_mono hAff hsub
  rcases suffixPostGain_isSuffixGain W' (by omega) with
    ⟨V, hreach, hgain⟩
  have hsim : DefectLegalSuffix W (W ⊔ V) :=
    hreach.simulate_from_equal_defect hsub (hdef'.trans hdef.symm) (by omega)
  have hAffW : affine 10 ≤ W := hAff.trans hsub
  have hendpoint : stateTargetRank V ≤ stateTargetRank (W ⊔ V) :=
    stateTargetRank_mono (hreach.affine_le hAff) le_sup_right
  have hWV : stateTargetRank W ≤ stateTargetRank (W ⊔ V) :=
    stateTargetRank_mono hAffW le_sup_left
  have hW'V : stateTargetRank W' ≤ stateTargetRank V :=
    stateTargetRank_mono hAff hreach.start_le
  have hlargeGain : suffixTargetGain W (W ⊔ V) ≤ suffixPostGain W :=
    IsSuffixGain.le_suffixPostGain hAffW ⟨W ⊔ V, hsim, rfl⟩
  unfold suffixTargetGain at hgain hlargeGain
  omega

/-- Stable deficit attached to a state. -/
def suffixDeficit (W : Submodule F₂ (ANF 10)) : Nat :=
  (9 - stateTargetRank W) - suffixPostGain W

theorem suffixPostGain_le_missingTarget {W : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ W)
    (hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3) :
    suffixPostGain W ≤ 9 - stateTargetRank W := by
  rcases suffixPostGain_isSuffixGain W hdef with ⟨V, hreach, hgain⟩
  have hmono := stateTargetRank_mono hAff hreach.start_le
  have htop := stateTargetRank_le_nine (hreach.affine_le hAff)
  unfold suffixTargetGain at hgain
  omega

/-- Manuscript equation (10.18): the completion deficit is monotone when a
defect-two state is replaced by a containing defect-two envelope. -/
theorem suffixDeficit_mono
    {W' W : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ W') (hsub : W' ≤ W)
    (hdef' : N4.flagDefectRank W' (mulTarget 5) = 2)
    (hdef : N4.flagDefectRank W (mulTarget 5) = 2) :
    suffixDeficit W ≤ suffixDeficit W' := by
  have ht := stateTargetRank_mono hAff hsub
  have hpost := suffixPostGain_mono_corrected hAff hsub hdef' hdef
  have hAffW : affine 10 ≤ W := hAff.trans hsub
  have hmissing' := suffixPostGain_le_missingTarget hAff (by omega)
  have hmissing := suffixPostGain_le_missingTarget hAffW (by omega)
  unfold suffixDeficit
  omega

end

end N5
end UnrestrictedBooleanMul
