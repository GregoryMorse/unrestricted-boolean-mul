import UnrestrictedBooleanMul.N5.TightCircuit

/-!
# Target-tight suffixes

Once a gate-minimal circuit has spent all of its available defect births,
every later gate must increase target rank by exactly one.  This inductive
relation retains that chronology and the literal factor membership at each
step.  It is strictly narrower than an arbitrary defect-legal suffix and is
the correct interface for the remaining boundary envelopes.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- An exact-length suffix in which every gate buys one target direction and
the quotient defect stays constant. -/
inductive TargetTightSuffix (W : Submodule F₂ (ANF 10)) :
    Nat → Submodule F₂ (ANF 10) → Prop
  | refl : TargetTightSuffix W 0 W
  | step {k : Nat} {V : Submodule F₂ (ANF 10)}
      (hreach : TargetTightSuffix W k V)
      (p q : ANF 10) (hp : p ∈ V) (hq : q ∈ V)
      (htarget : stateTargetRank (andExtend V p q) =
        stateTargetRank V + 1)
      (hdefect : N4.flagDefectRank (andExtend V p q) (mulTarget 5) =
        N4.flagDefectRank V (mulTarget 5)) :
      TargetTightSuffix W (k + 1) (andExtend V p q)

theorem TargetTightSuffix.start_le
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (h : TargetTightSuffix W k V) : W ≤ V := by
  induction h with
  | refl => exact le_rfl
  | step hreach p q hp hq htarget hdefect ih =>
      exact ih.trans le_sup_left

/-- Target rank grows by the exact number of gates in a tight suffix. -/
theorem TargetTightSuffix.targetRank_eq
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (h : TargetTightSuffix W k V) :
    stateTargetRank V = stateTargetRank W + k := by
  induction h with
  | refl => omega
  | step hreach p q hp hq htarget hdefect ih => omega

/-- Total quotient defect is constant throughout a tight suffix. -/
theorem TargetTightSuffix.defectRank_eq
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (h : TargetTightSuffix W k V) :
    N4.flagDefectRank V (mulTarget 5) =
      N4.flagDefectRank W (mulTarget 5) := by
  induction h with
  | refl => rfl
  | step hreach p q hp hq htarget hdefect ih =>
      exact hdefect.trans ih

/-- A tight suffix of defect at most three is, in particular, an exact-cost
defect-legal suffix. -/
theorem TargetTightSuffix.toCostedDefectLegal
    {W V : Submodule F₂ (ANF 10)} {k : Nat}
    (h : TargetTightSuffix W k V)
    (hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3) :
    CostedDefectLegalSuffix W k V := by
  induction h with
  | refl => exact .refl hdef
  | step hreach p q hp hq htarget hdefect ih =>
      exact .step ih p q hp hq (by rw [hdefect, hreach.defectRank_eq]; exact hdef)

/-- A nonredundant circuit interval with equal endpoint defects is target
tight: monotonicity prevents a hidden intermediate defect birth. -/
theorem circuitFlag_targetTightSuffix {r j k : Nat}
    (C : Circuit 10 r) (hnr : ∀ i : Fin r, N4.NonredundantAt C i)
    (hjk : j ≤ k) (hkr : k ≤ r)
    (hdefect : N4.flagDefectRank (N4.circuitFlag C k) (mulTarget 5) =
      N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5)) :
    TargetTightSuffix (N4.circuitFlag C j) (k - j)
      (N4.circuitFlag C k) := by
  induction k with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      simpa using TargetTightSuffix.refl
  | succ k ih =>
      by_cases hjEq : j = k + 1
      · subst j
        simpa using TargetTightSuffix.refl
      · have hjk' : j ≤ k := by omega
        have hkr' : k ≤ r := by omega
        have hklt : k < r := by omega
        have hdefectMono : N4.flagDefectRank
            (N4.circuitFlag C j) (mulTarget 5) ≤
            N4.flagDefectRank (N4.circuitFlag C k) (mulTarget 5) :=
          flagDefectRank_mono (N4.wireSpace_mono hjk')
        have hdefectStep : N4.flagDefectRank
            (N4.circuitFlag C k) (mulTarget 5) ≤
            N4.flagDefectRank (N4.circuitFlag C (k + 1)) (mulTarget 5) :=
          flagDefectRank_mono (N4.wireSpace_mono (by omega))
        have hdefectK : N4.flagDefectRank
            (N4.circuitFlag C k) (mulTarget 5) =
            N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) := by
          omega
        have hreach := ih hjk' hkr' hdefectK
        let i : Fin r := ⟨k, hklt⟩
        have hkind := gate_target_or_defect_of_nonredundant C hnr i
        have htarget : stateTargetRank (N4.circuitFlag C (k + 1)) =
            stateTargetRank (N4.circuitFlag C k) + 1 := by
          rcases hkind with htarget | hbirth
          · simpa only [i] using htarget.1
          · have hbad : N4.flagDefectRank
                (N4.circuitFlag C (k + 1)) (mulTarget 5) =
              N4.flagDefectRank (N4.circuitFlag C k) (mulTarget 5) + 1 := by
                simpa only [i] using hbirth.2
            omega
        have hdefectSame : N4.flagDefectRank
            (N4.circuitFlag C (k + 1)) (mulTarget 5) =
            N4.flagDefectRank (N4.circuitFlag C k) (mulTarget 5) := by
          omega
        have hleft : C.left i ∈ N4.circuitFlag C k := by
          simpa only [N4.circuitFlag, i] using C.left_mem i
        have hright : C.right i ∈ N4.circuitFlag C k := by
          simpa only [N4.circuitFlag, i] using C.right_mem i
        have hwire : N4.circuitFlag C (k + 1) =
            andExtend (N4.circuitFlag C k) (C.left i) (C.right i) := by
          change wireSpace C.gate (k + 1) = wireSpace C.gate k ⊔
            Submodule.span F₂ ({C.left i * C.right i} : Set (ANF 10))
          rw [show C.left i * C.right i = C.gate i from (C.gate_eq i).symm]
          simpa only [i] using N4.wireSpace_succ C.gate hklt
        have hstep := TargetTightSuffix.step hreach
          (C.left i) (C.right i) hleft hright
          (by rwa [← hwire]) (by rwa [← hwire])
        rw [hwire]
        convert hstep using 1
        all_goals omega

/-- If the first high gate after the last quadratic prefix exhausts the final
defect budget, the rest of the actual circuit is target tight. -/
theorem circuitTail_targetTightSuffix_after_lastQuadratic {r : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) (hr : r ≤ 12)
    (hnr : ∀ i : Fin r, N4.NonredundantAt C i)
    (hspent : N4.flagDefectRank C.finalWire (mulTarget 5) =
      N4.flagDefectRank
        (N4.circuitFlag C (lastQuadraticPrefix C)) (mulTarget 5) + 1) :
    TargetTightSuffix
      (N4.circuitFlag C (lastQuadraticPrefix C + 1))
      (r - (lastQuadraticPrefix C + 1)) C.finalWire := by
  have hproper : lastQuadraticPrefix C < r := by
    by_contra hnot
    have heq : lastQuadraticPrefix C = r :=
      Nat.le_antisymm (lastQuadraticPrefix_le C) (Nat.le_of_not_gt hnot)
    apply no_all_quadratic_circuit_le_twelve C hC hr
    intro i
    exact allQuadraticPrefix_last C i (by omega)
  let i : Fin r := ⟨lastQuadraticPrefix C, hproper⟩
  have hbirth := firstHighGate_defect_succ C i
    (fun k hk => allQuadraticPrefix_last C k hk)
    (gate_lastQuadraticPrefix_not_quadratic C hproper) (hnr i)
  have hdefect : N4.flagDefectRank C.finalWire (mulTarget 5) =
      N4.flagDefectRank
        (N4.circuitFlag C (lastQuadraticPrefix C + 1)) (mulTarget 5) := by
    change N4.flagDefectRank
        (N4.circuitFlag C (lastQuadraticPrefix C + 1)) (mulTarget 5) =
      N4.flagDefectRank
        (N4.circuitFlag C (lastQuadraticPrefix C)) (mulTarget 5) + 1 at hbirth
    omega
  simpa only [Circuit.finalWire, N4.circuitFlag] using
    circuitFlag_targetTightSuffix C hnr
      (Nat.succ_le_of_lt hproper) (le_refl r) hdefect

end
end N5
end UnrestrictedBooleanMul
