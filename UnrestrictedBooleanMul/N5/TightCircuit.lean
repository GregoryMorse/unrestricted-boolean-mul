import UnrestrictedBooleanMul.CircuitPruning
import UnrestrictedBooleanMul.N5.CostedSuffix
import UnrestrictedBooleanMul.N5.OneHighDefectOneClosure
import UnrestrictedBooleanMul.N5.Upper

/-!
# Gate-minimal five-term circuits and tight defect accounting

After redundant gates are removed, every prefix satisfies the exact flag
ledger.  Consequently a minimum circuit computing `Mul 5` has final defect
exactly `r - 9`, and every completing tail saturates the joint target/defect
gate budget.  This replaces the much looser bookkeeping needed for a padded
twelve-gate circuit.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- A nonredundant circuit computing `Mul 5` has the exact final defect
predicted by its gate count. -/
theorem final_defect_eq_sub_nine_of_nonredundant {r : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5))
    (hnr : ∀ i : Fin r, N4.NonredundantAt C i) :
    N4.flagDefectRank C.finalWire (mulTarget 5) = r - 9 := by
  have hcount := N4.circuit_flag_defect_count C (mulTarget 5)
    (j := r) (le_refl r) (fun i _ => hnr i)
  have htarget := final_target_rank_five C hC
  change r = N4.flagTargetRank C.finalWire (mulTarget 5) +
    N4.flagDefectRank C.finalWire (mulTarget 5) at hcount
  omega

/-- Every prefix of a nonredundant circuit satisfies `j = target + defect`. -/
theorem prefix_target_add_defect_eq_of_nonredundant {r j : Nat}
    (C : Circuit 10 r) (hj : j ≤ r)
    (hnr : ∀ i : Fin r, N4.NonredundantAt C i) :
    stateTargetRank (N4.circuitFlag C j) +
        N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) = j := by
  have hcount := N4.circuit_flag_defect_count C (mulTarget 5) hj
    (fun i _ => hnr i)
  simpa only [stateTargetRank, add_comm] using hcount.symm

/-- In a nonredundant completing circuit of at most twelve gates, the actual
tail uses every available unit of joint target/defect dimension. -/
theorem circuitTail_totalGain_eq_remaining_of_nonredundant {r j : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5))
    (hj : j ≤ r) (hnr : ∀ i : Fin r, N4.NonredundantAt C i) :
    suffixTargetGain (N4.circuitFlag C j) C.finalWire +
        (N4.flagDefectRank C.finalWire (mulTarget 5) -
          N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5)) =
      r - j := by
  have hprefix := prefix_target_add_defect_eq_of_nonredundant C hj hnr
  have hfinalDefect := final_defect_eq_sub_nine_of_nonredundant C hC hnr
  have hfinalTarget := stateTargetRank_final C hC
  have hgateLower : 9 ≤ r := mul_five_dimension_lower r ⟨⟨C, hC⟩⟩
  have htargetMono : stateTargetRank (N4.circuitFlag C j) ≤
      stateTargetRank C.finalWire := by
    apply stateTargetRank_mono (affine_le_wireSpace C.gate)
    change wireSpace C.gate j ≤ wireSpace C.gate r
    exact N4.wireSpace_mono hj
  have hdefectMono : N4.flagDefectRank
      (N4.circuitFlag C j) (mulTarget 5) ≤
      N4.flagDefectRank C.finalWire (mulTarget 5) := by
    apply flagDefectRank_mono
    change wireSpace C.gate j ≤ wireSpace C.gate r
    exact N4.wireSpace_mono hj
  unfold suffixTargetGain
  omega

/-- The last quadratic prefix has strictly smaller defect than the final state:
the first nonquadratic gate is an unavoidable defect birth. -/
theorem lastQuadraticPrefix_defect_lt_final {r : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) (hr : r ≤ 12) :
    N4.flagDefectRank
        (N4.circuitFlag C (lastQuadraticPrefix C)) (mulTarget 5) <
      N4.flagDefectRank C.finalWire (mulTarget 5) := by
  have hproper : lastQuadraticPrefix C < r := by
    by_contra hnot
    have heq : lastQuadraticPrefix C = r :=
      Nat.le_antisymm (lastQuadraticPrefix_le C) (Nat.le_of_not_gt hnot)
    apply no_all_quadratic_circuit_le_twelve C hC hr
    intro i
    exact allQuadraticPrefix_last C i (by omega)
  let i : Fin r := ⟨lastQuadraticPrefix C, hproper⟩
  have hnri : N4.NonredundantAt C i := by
    intro hred
    apply gate_lastQuadraticPrefix_not_quadratic C hproper
    apply N4.wireSpace_le_quadratic_of_prefix C.gate
      (fun k hk => allQuadraticPrefix_last C k hk)
    simpa [N4.NonredundantAt, N4.circuitFlag, i] using hred
  have hbirth := firstHighGate_defect_succ C i
    (fun k hk => allQuadraticPrefix_last C k hk)
    (gate_lastQuadraticPrefix_not_quadratic C hproper) hnri
  have hmono : N4.flagDefectRank
      (N4.circuitFlag C (i.val + 1)) (mulTarget 5) ≤
      N4.flagDefectRank C.finalWire (mulTarget 5) := by
    apply flagDefectRank_mono
    change wireSpace C.gate (i.val + 1) ≤ wireSpace C.gate r
    exact N4.wireSpace_mono (Nat.succ_le_of_lt hproper)
  change N4.flagDefectRank
      (N4.circuitFlag C (lastQuadraticPrefix C)) (mulTarget 5) < _
  change N4.flagDefectRank
      (N4.circuitFlag C (lastQuadraticPrefix C + 1)) (mulTarget 5) =
        N4.flagDefectRank
          (N4.circuitFlag C (lastQuadraticPrefix C)) (mulTarget 5) + 1 at hbirth
  change N4.flagDefectRank
      (N4.circuitFlag C (lastQuadraticPrefix C + 1)) (mulTarget 5) ≤ _ at hmono
  omega

/-- The minimum circuit is already forced into sizes eleven, twelve, or
thirteen.  Its final defect and every prefix ledger are exact. -/
theorem exists_tight_minimal_mul_five :
    ∃ r, ∃ C : Circuit 10 r, C.Computes (Mul 5) ∧
      (∀ i : Fin r, N4.NonredundantAt C i) ∧
      11 ≤ r ∧ r ≤ 13 ∧
      N4.flagDefectRank C.finalWire (mulTarget 5) = r - 9 ∧
      MC(Mul 5) = r := by
  rcases exists_minimalCircuit_all_nonredundant mul_five_upper with
    ⟨r, C, hC, hnr, hmin⟩
  have hrUpper : r ≤ 13 := hmin 13 mul_five_upper
  have hrLower : 11 ≤ r := by
    by_contra hnot
    have hrTen : r ≤ 10 := by omega
    have hdef := final_defect_eq_sub_nine_of_nonredundant C hC hnr
    exact no_circuit_of_final_defect_le_one C hC (by omega) (by omega)
  have hdef := final_defect_eq_sub_nine_of_nonredundant C hC hnr
  have hmc : MC(Mul 5) = r :=
    mc_eq_of_lower_upper ⟨⟨C, hC⟩⟩ hmin
  exact ⟨r, C, hC, hnr, hrLower, hrUpper, hdef, hmc⟩

/-- The only two cases still requiring exclusion are a defect-two eleven-gate
minimum and a defect-three twelve-gate minimum. -/
theorem tight_minimal_mul_five_gate_cases :
    ∃ r, ∃ C : Circuit 10 r, C.Computes (Mul 5) ∧
      (∀ i : Fin r, N4.NonredundantAt C i) ∧
      (r = 11 ∨ r = 12 ∨ r = 13) ∧
      N4.flagDefectRank C.finalWire (mulTarget 5) = r - 9 ∧
      MC(Mul 5) = r := by
  rcases exists_tight_minimal_mul_five with
    ⟨r, C, hC, hnr, hrLower, hrUpper, hdef, hmc⟩
  refine ⟨r, C, hC, hnr, ?_, hdef, hmc⟩
  omega

end
end N5
end UnrestrictedBooleanMul
