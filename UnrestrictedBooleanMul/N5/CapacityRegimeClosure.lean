import UnrestrictedBooleanMul.N5.CapacityReplay
import UnrestrictedBooleanMul.N5.MainInterface
import UnrestrictedBooleanMul.N5.PrefixState
import UnrestrictedBooleanMul.N5.StableTarget

/-!
# Final circuit split through intrinsic capacity states

The history-free first-order envelope used by an earlier proof attempt is
too large and is not stable.  The correct interface enlarges an
all-quadratic prefix only to the intrinsic capacity state of its own
decomposable presentation.  Equal-defect replay then reduces the full lower
bound to stability of those intrinsic states in defect dimensions zero, one,
and two.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Intrinsic capacity states of quadratic defect at most one never acquire
all nine target directions while total defect remains at most three. -/
def StableIntrinsicCapacityAtMostOne : Prop :=
  ∀ {j : Nat} (p : Fin j → TwoForm),
    (∀ i, IsDecomposableTwo (p i)) →
    Module.finrank F₂ (presentationDefect p) ≤ 1 →
    StableTargetRank (intrinsicCapacityState p) 8

/-- Intrinsic capacity states of quadratic defect exactly two satisfy the
same rank-eight bound. -/
def StableIntrinsicCapacityAtTwo : Prop :=
  ∀ {j : Nat} (p : Fin j → TwoForm),
    (∀ i, IsDecomposableTwo (p i)) →
    Module.finrank F₂ (presentationDefect p) = 2 →
    StableTargetRank (intrinsicCapacityState p) 8

/-- The corrected intrinsic-capacity obligations exclude every twelve-gate
circuit.  All circuit bookkeeping and replay are discharged here. -/
theorem no_twelve_gate_circuit_of_intrinsic_capacity_stability
    (hFirst : StableIntrinsicCapacityAtMostOne)
    (hTwo : StableIntrinsicCapacityAtTwo) :
    ¬ HasCircuit (Mul 5) 12 := by
  rintro ⟨⟨C, hC⟩⟩
  let j := lastQuadraticPrefix C
  have hj : j ≤ 12 := lastQuadraticPrefix_le C
  have hall : AllQuadraticPrefix C j := allQuadraticPrefix_last C
  let hflat := quadraticPrefixFlattening_of_all_quadratic C hj hall
  have hprefixDefect : N4.flagDefectRank
      (N4.circuitFlag C j) (mulTarget 5) ≤ 2 :=
    lastQuadraticPrefix_defect_le_two C hC (by omega)
  have hQ : Module.finrank F₂ (presentationDefect hflat.generator) ≤ 2 := by
    rw [quadraticPrefixFlattening_defect_eq_flagDefect C hflat hall]
    exact hprefixDefect
  have hstable : StableTargetRank
      (intrinsicCapacityState hflat.generator) 8 := by
    by_cases htwo : Module.finrank F₂
        (presentationDefect hflat.generator) = 2
    · exact hTwo hflat.generator hflat.decomposable htwo
    · exact hFirst hflat.generator hflat.decomposable (by omega)
  have htail : DefectLegalSuffix (N4.circuitFlag C j) C.finalWire :=
    circuitTail_defectLegalSuffix C hC (by omega) hj
  have hreplay : DefectLegalSuffix
      (intrinsicCapacityState hflat.generator)
      (intrinsicCapacityState hflat.generator ⊔ C.finalWire) :=
    htail.replay_from_intrinsicCapacityState C hflat hall
  have hbound := hstable _ hreplay
  have hmono : stateTargetRank C.finalWire ≤
      stateTargetRank
        (intrinsicCapacityState hflat.generator ⊔ C.finalWire) := by
    apply stateTargetRank_mono
      (affine_le_wireSpace C.gate)
      (le_sup_right : C.finalWire ≤
        intrinsicCapacityState hflat.generator ⊔ C.finalWire)
  have hfinal := stateTargetRank_final C hC
  omega

/-- Exact five-term theorem with the corrected, intrinsic stability surface.
No false anchored-envelope premise remains. -/
theorem mc_mul_five_of_intrinsic_capacity_stability
    (hFirst : StableIntrinsicCapacityAtMostOne)
    (hTwo : StableIntrinsicCapacityAtTwo) : MainStatement :=
  mc_mul_five_of_no_twelve
    (no_twelve_gate_circuit_of_intrinsic_capacity_stability hFirst hTwo)

end
end N5
end UnrestrictedBooleanMul
