import UnrestrictedBooleanMul.N5.CircuitSuffix

/-!
# Completion forces zero suffix deficit

This file records the arithmetic endpoint shared by all nonlinear regimes.
If a circuit tail reaches the full nine-dimensional target, its initial state
cannot have a positive stable suffix deficit.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem stateTargetRank_final {r : Nat} (C : Circuit 10 r)
    (hC : C.Computes (Mul 5)) : stateTargetRank C.finalWire = 9 :=
  final_target_rank_five C hC

/-- The target gain of a completing circuit tail is exactly the target rank
missing at its initial flag. -/
theorem circuitTail_targetGain_eq_missing {r j : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) :
    suffixTargetGain (N4.circuitFlag C j) C.finalWire =
      9 - stateTargetRank (N4.circuitFlag C j) := by
  unfold suffixTargetGain
  rw [stateTargetRank_final C hC]

/-- Any initial state of an actual completing tail with at most twelve gates
has zero suffix deficit. -/
theorem circuitTail_suffixDeficit_eq_zero {r j : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) (hr : r ≤ 12)
    (hjr : j ≤ r) :
    suffixDeficit (N4.circuitFlag C j) = 0 := by
  let W := N4.circuitFlag C j
  have hAff : affine 10 ≤ W := affine_le_wireSpace C.gate
  have hreach := circuitTail_defectLegalSuffix C hC hr hjr
  have hdef : N4.flagDefectRank W (mulTarget 5) ≤ 3 :=
    (flagDefectRank_mono hreach.start_le).trans
      hreach.final_defect_le_three
  have hpostLe := suffixPostGain_le_missingTarget hAff hdef
  have hactualLe := circuitTail_targetGain_le_suffixPostGain C hC hr hjr
  have hactual := circuitTail_targetGain_eq_missing (j := j) C hC
  rw [hactual] at hactualLe
  unfold suffixDeficit
  omega

/-- Positive suffix deficit at a circuit flag contradicts completion. -/
theorem no_circuit_completion_of_positive_suffixDeficit {r j : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) (hr : r ≤ 12)
    (hjr : j ≤ r)
    (hpositive : 1 ≤ suffixDeficit (N4.circuitFlag C j)) : False := by
  rw [circuitTail_suffixDeficit_eq_zero C hC hr hjr] at hpositive
  omega

/-- A defect-two flag dominated by an equal-defect envelope with positive
deficit cannot occur as the initial state of a completing circuit tail. -/
theorem no_circuit_completion_of_twoDefect_envelope
    {r j : Nat} (C : Circuit 10 r) (hC : C.Computes (Mul 5))
    (hr : r ≤ 12) (hjr : j ≤ r)
    (W : Submodule F₂ (ANF 10))
    (hsub : N4.circuitFlag C j ≤ W)
    (hflagDef : N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) = 2)
    (hWDef : N4.flagDefectRank W (mulTarget 5) = 2)
    (hWpositive : 1 ≤ suffixDeficit W) : False := by
  have hmono := suffixDeficit_mono
    (affine_le_wireSpace C.gate) hsub hflagDef hWDef
  exact no_circuit_completion_of_positive_suffixDeficit C hC hr hjr
    (hWpositive.trans hmono)

end
end N5
end UnrestrictedBooleanMul
