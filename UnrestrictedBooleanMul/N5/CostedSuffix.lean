import UnrestrictedBooleanMul.N5.CircuitSuffix

/-!
# Exact gate cost for defect-legal suffixes

The fixed-envelope saturation statement used by the first version of the
`n = 5` lower-bound architecture is false: a two-gate feedback pair can
exchange one defect birth for the missing target coordinate.  The final
circuit argument therefore has to retain the number of AND extensions.

This module adds that missing structural datum.  It contains no search and
no local feedback classification.  Its main ledger says that target-rank
gain plus quotient-defect gain is at most the exact number of suffix gates.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- A defect-legal suffix with an exact number of AND extensions. -/
inductive CostedDefectLegalSuffix (W : Submodule F₂ (ANF 10)) :
    Nat → Submodule F₂ (ANF 10) → Prop
  | refl (hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3) :
      CostedDefectLegalSuffix W 0 W
  | step {k : Nat} {V : Submodule F₂ (ANF 10)}
      (hreach : CostedDefectLegalSuffix W k V)
      (p q : ANF 10) (hp : p ∈ V) (hq : q ∈ V)
      (hdef : N4.flagDefectRank (andExtend V p q) (mulTarget 5) ≤ 3) :
      CostedDefectLegalSuffix W (k + 1) (andExtend V p q)

/-- Forgetting exact gate cost recovers the original suffix relation. -/
theorem CostedDefectLegalSuffix.toDefectLegal
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (h : CostedDefectLegalSuffix W k V) : DefectLegalSuffix W V := by
  induction h with
  | refl hdef => exact .refl hdef
  | step hreach p q hp hq hdef ih =>
      exact .step ih p q hp hq hdef

theorem CostedDefectLegalSuffix.start_le
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (h : CostedDefectLegalSuffix W k V) : W ≤ V :=
  h.toDefectLegal.start_le

theorem CostedDefectLegalSuffix.final_defect_le_three
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (h : CostedDefectLegalSuffix W k V) :
    N4.flagDefectRank V (mulTarget 5) ≤ 3 :=
  h.toDefectLegal.final_defect_le_three

theorem CostedDefectLegalSuffix.affine_le
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (hAff : affine 10 ≤ W) (h : CostedDefectLegalSuffix W k V) :
    affine 10 ≤ V := hAff.trans h.start_le

/-- One AND extension enlarges the underlying wire state by at most one
dimension, including when the new gate is redundant. -/
theorem finrank_andExtend_le_succ
    (V : Submodule F₂ (ANF 10)) (p q : ANF 10) :
    Module.finrank F₂ (andExtend V p q) ≤
      Module.finrank F₂ V + 1 := by
  by_cases hpq : p * q ∈ V
  · have hspan : Submodule.span F₂ ({p * q} : Set (ANF 10)) ≤ V := by
      rw [Submodule.span_le]
      simpa using hpq
    rw [andExtend, sup_eq_left.mpr hspan]
    omega
  · rw [andExtend, Submodule.finrank_sup_span_singleton hpq]

/-- Target rank plus quotient defect is the dimension of a state modulo the
affine inputs. -/
theorem stateTargetRank_add_flagDefectRank
    (V : Submodule F₂ (ANF 10)) (hAff : affine 10 ≤ V) :
    stateTargetRank V + N4.flagDefectRank V (mulTarget 5) =
      Module.finrank F₂ V - Module.finrank F₂ (affine 10) := by
  simpa [stateTargetRank] using
    (N4.flag_rank_ledger (V := V) (T := mulTarget 5) hAff).symm

/-- A single AND gate buys at most one unit in the joint target/defect
ledger.  Unlike fixed-envelope closure, this statement is respected by the
explicit feedback collision. -/
theorem targetDefectRank_andExtend_le_succ
    (V : Submodule F₂ (ANF 10)) (p q : ANF 10)
    (hAff : affine 10 ≤ V) :
    stateTargetRank (andExtend V p q) +
        N4.flagDefectRank (andExtend V p q) (mulTarget 5) ≤
      stateTargetRank V + N4.flagDefectRank V (mulTarget 5) + 1 := by
  have hAffNext : affine 10 ≤ andExtend V p q := hAff.trans le_sup_left
  have hV := stateTargetRank_add_flagDefectRank V hAff
  have hNext := stateTargetRank_add_flagDefectRank
    (andExtend V p q) hAffNext
  have hdim := finrank_andExtend_le_succ V p q
  have hAffDim : Module.finrank F₂ (affine 10) ≤
      Module.finrank F₂ V := Submodule.finrank_mono hAff
  rw [hV, hNext]
  omega

/-- Exact cost ledger for an arbitrary finite defect-legal suffix. -/
theorem CostedDefectLegalSuffix.targetDefectRank_le
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (hAff : affine 10 ≤ W) (h : CostedDefectLegalSuffix W k V) :
    stateTargetRank V + N4.flagDefectRank V (mulTarget 5) ≤
      stateTargetRank W + N4.flagDefectRank W (mulTarget 5) + k := by
  induction h with
  | refl hdef => omega
  | @step k V hreach p q hp hq hdef ih =>
      have hAffV : affine 10 ≤ V := hAff.trans hreach.start_le
      have hstep := targetDefectRank_andExtend_le_succ V p q hAffV
      omega

/-- Target gain plus defect gain is at most the exact suffix length. -/
theorem CostedDefectLegalSuffix.totalGain_le
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (hAff : affine 10 ≤ W) (h : CostedDefectLegalSuffix W k V) :
    suffixTargetGain W V +
        (N4.flagDefectRank V (mulTarget 5) -
          N4.flagDefectRank W (mulTarget 5)) ≤ k := by
  have htarget : stateTargetRank W ≤ stateTargetRank V :=
    stateTargetRank_mono hAff h.start_le
  have hdefect : N4.flagDefectRank W (mulTarget 5) ≤
      N4.flagDefectRank V (mulTarget 5) := flagDefectRank_mono h.start_le
  have htotal := h.targetDefectRank_le hAff
  unfold suffixTargetGain
  omega

/-- Forgetting defect gain gives the elementary exact-cost target bound. -/
theorem CostedDefectLegalSuffix.targetRank_le
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (hAff : affine 10 ≤ W) (h : CostedDefectLegalSuffix W k V) :
    stateTargetRank V ≤ stateTargetRank W + k := by
  have htotal := h.targetDefectRank_le hAff
  have hdefect : N4.flagDefectRank W (mulTarget 5) ≤
      N4.flagDefectRank V (mulTarget 5) := flagDefectRank_mono h.start_le
  omega

/-! ## Exact circuit-tail bridge -/

/-- A circuit interval has exact cost `k-j` in the costed suffix relation. -/
theorem circuitFlag_costedDefectLegalSuffix {r j k : Nat}
    (C : Circuit 10 r) (hjk : j ≤ k) (hkr : k ≤ r)
    (hdef : ∀ l, j ≤ l → l ≤ k →
      N4.flagDefectRank (N4.circuitFlag C l) (mulTarget 5) ≤ 3) :
    CostedDefectLegalSuffix (N4.circuitFlag C j) (k - j)
      (N4.circuitFlag C k) := by
  induction k with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      simpa using CostedDefectLegalSuffix.refl
        (hdef 0 (by omega) (by omega))
  | succ k ih =>
      by_cases hjEq : j = k + 1
      · subst j
        simpa using CostedDefectLegalSuffix.refl
          (hdef (k + 1) (by omega) (by omega))
      · have hjk' : j ≤ k := by omega
        have hkr' : k ≤ r := by omega
        have hklt : k < r := by omega
        have hreach := ih hjk' hkr' (fun l hjl hlk =>
          hdef l hjl (hlk.trans (Nat.le_succ k)))
        let i : Fin r := ⟨k, hklt⟩
        have hleft : C.left i ∈ N4.circuitFlag C k := by
          simpa only [N4.circuitFlag, i] using C.left_mem i
        have hright : C.right i ∈ N4.circuitFlag C k := by
          simpa only [N4.circuitFlag, i] using C.right_mem i
        have hgate : C.left i * C.right i = C.gate i := (C.gate_eq i).symm
        have hwire : N4.circuitFlag C (k + 1) =
            andExtend (N4.circuitFlag C k) (C.left i) (C.right i) := by
          change wireSpace C.gate (k + 1) =
            wireSpace C.gate k ⊔
              Submodule.span F₂ ({C.left i * C.right i} : Set (ANF 10))
          rw [hgate]
          simpa only [i] using N4.wireSpace_succ C.gate hklt
        have hnextDef : N4.flagDefectRank
            (andExtend (N4.circuitFlag C k) (C.left i) (C.right i))
              (mulTarget 5) ≤ 3 := by
          rw [← hwire]
          exact hdef (k + 1) (by omega) (by omega)
        have hstep := CostedDefectLegalSuffix.step hreach
          (C.left i) (C.right i) hleft hright hnextDef
        rw [hwire]
        convert hstep using 1
        all_goals omega

/-- Every actual tail of a circuit computing `Mul 5` with at most twelve
gates has exact cost `r-j`. -/
theorem circuitTail_costedDefectLegalSuffix {r j : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5))
    (hr : r ≤ 12) (hjr : j ≤ r) :
    CostedDefectLegalSuffix (N4.circuitFlag C j) (r - j) C.finalWire := by
  have hfinal : N4.flagDefectRank C.finalWire (mulTarget 5) ≤ 3 :=
    final_defect_le_three C hC hr
  have hdef : ∀ l, j ≤ l → l ≤ r →
      N4.flagDefectRank (N4.circuitFlag C l) (mulTarget 5) ≤ 3 := by
    intro l hjl hlr
    apply (flagDefectRank_mono (N4.wireSpace_mono hlr)).trans
    simpa [N4.circuitFlag, Circuit.finalWire] using hfinal
  simpa only [Circuit.finalWire, N4.circuitFlag] using
    circuitFlag_costedDefectLegalSuffix C hjr (le_refl r) hdef

/-- The exact target-plus-defect gain of a real tail is bounded by its
remaining number of AND gates. -/
theorem circuitTail_totalGain_le_remaining {r j : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5))
    (hr : r ≤ 12) (hjr : j ≤ r) :
    suffixTargetGain (N4.circuitFlag C j) C.finalWire +
        (N4.flagDefectRank C.finalWire (mulTarget 5) -
          N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5)) ≤
      r - j := by
  exact (circuitTail_costedDefectLegalSuffix C hC hr hjr).totalGain_le
    (affine_le_wireSpace C.gate)

end
end N5
end UnrestrictedBooleanMul
