import UnrestrictedBooleanMul.N5.SuffixBudget

/-!
# Circuit tails as defect-legal suffixes

This module connects the abstract arbitrary-length suffix relation to the
actual flag of a semantic XOR--AND circuit.  It is purely structural: one
circuit step is exactly `andExtend` by the stored gate equation.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Every interval of a circuit flag whose intermediate defects are at most
three is a `DefectLegalSuffix`. -/
theorem circuitFlag_defectLegalSuffix {r j k : Nat} (C : Circuit 10 r)
    (hjk : j ≤ k) (hkr : k ≤ r)
    (hdef : ∀ l, j ≤ l → l ≤ k →
      N4.flagDefectRank (N4.circuitFlag C l) (mulTarget 5) ≤ 3) :
    DefectLegalSuffix (N4.circuitFlag C j) (N4.circuitFlag C k) := by
  induction k with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      exact .refl (hdef 0 (by omega) (by omega))
  | succ k ih =>
      by_cases hjEq : j = k + 1
      · subst j
        exact .refl (hdef (k + 1) (by omega) (by omega))
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
        have hstep : DefectLegalSuffix (N4.circuitFlag C j)
            (andExtend (N4.circuitFlag C k) (C.left i) (C.right i)) :=
          DefectLegalSuffix.step hreach (C.left i) (C.right i)
            hleft hright hnextDef
        rw [hwire]
        exact hstep

/-- Every tail of a circuit computing `Mul 5` with at most twelve gates is a
defect-legal suffix, because defect is monotone and the final defect is at
most three. -/
theorem circuitTail_defectLegalSuffix {r j : Nat} (C : Circuit 10 r)
    (hC : C.Computes (Mul 5)) (hr : r ≤ 12) (hjr : j ≤ r) :
    DefectLegalSuffix (N4.circuitFlag C j) C.finalWire := by
  have hfinal : N4.flagDefectRank C.finalWire (mulTarget 5) ≤ 3 :=
    final_defect_le_three C hC hr
  have hdef : ∀ l, j ≤ l → l ≤ r →
      N4.flagDefectRank (N4.circuitFlag C l) (mulTarget 5) ≤ 3 := by
    intro l hjl hlr
    apply (flagDefectRank_mono (N4.wireSpace_mono hlr)).trans
    simpa [N4.circuitFlag, Circuit.finalWire] using hfinal
  simpa only [Circuit.finalWire, N4.circuitFlag] using
    circuitFlag_defectLegalSuffix C hjr (le_refl r) hdef

/-- The actual target gain of such a circuit tail is bounded by the abstract
maximum suffix gain from its initial flag. -/
theorem circuitTail_targetGain_le_suffixPostGain {r j : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) (hr : r ≤ 12)
    (hjr : j ≤ r) :
    suffixTargetGain (N4.circuitFlag C j) C.finalWire ≤
      suffixPostGain (N4.circuitFlag C j) := by
  have hreach := circuitTail_defectLegalSuffix C hC hr hjr
  exact IsSuffixGain.le_suffixPostGain
    (affine_le_wireSpace C.gate)
    ⟨C.finalWire, hreach, rfl⟩

end
end N5
end UnrestrictedBooleanMul
