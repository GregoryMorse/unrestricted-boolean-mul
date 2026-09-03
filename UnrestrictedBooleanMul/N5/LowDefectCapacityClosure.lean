import UnrestrictedBooleanMul.N5.CapacityReplay
import UnrestrictedBooleanMul.N5.CapacityRegimeClosure
import UnrestrictedBooleanMul.N5.DefectOneCapacity
import UnrestrictedBooleanMul.N5.HighDefect

/-!
# Correct low-defect obligations after capacity replay

The old history-free first-order envelope is false.  This file records the
strictly smaller statements that the repaired proof uses.  At defect zero we
need rank-eight stability of the canonical state `Aff + R`.  At defect one
we retain the intrinsic capacity base and charge target gain to the nonzero
high colours actually present at the endpoint.

The exponent `2^s - 1` is the number of nonzero colours in an `s`-dimensional
binary high space.  The fixed-block certificates prove that a rooted shadow
family for one colour has rank at most one; the remaining semantic step is to
assign every target-tight gate to such a rooted family without translating
its target origin.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The anchor-free intrinsic capacity state is stable at target rank eight.
By `intrinsicCapacityState_eq_rational_of_defectRank_zero`, this quantifies
only over the canonical state `Aff + R`, despite retaining presentation data
for direct use by capacity replay. -/
def StableIntrinsicCapacityAtZero : Prop :=
  ∀ {j : Nat} (p : Fin j → TwoForm),
    (∀ i, IsDecomposableTwo (p i)) →
    Module.finrank F₂ (presentationDefect p) = 0 →
    StableTargetRank (intrinsicCapacityState p) 8

/-- The exact one-defect colour ledger.  Starting from the intrinsic
capacity base, an endpoint with high rank `s` gains at most one target
direction for each of its `2^s - 1` nonzero high colours. -/
def IntrinsicOneDefectColourLedger : Prop :=
  ∀ {j : Nat} (p : Fin j → TwoForm),
    (∀ i, IsDecomposableTwo (p i)) →
    Module.finrank F₂ (presentationDefect p) = 1 →
    ∀ V, DefectLegalSuffix (intrinsicCapacityState p) V →
      stateTargetRank V ≤
        stateTargetRank (intrinsicCapacityState p) +
          (2 ^ stateHighRank V - 1)

/-- Pure linear-algebra endgame for the two-high-colour case: three rooted
colour images of rank at most one have combined rank at most three. -/
theorem finrank_le_three_of_le_three_rank_one_images
    {E : Type*} [AddCommGroup E] [Module F₂ E] [Module.Finite F₂ E]
    (G A B C : Submodule F₂ E)
    (hG : G ≤ A ⊔ B ⊔ C)
    (hA : Module.finrank F₂ A ≤ 1)
    (hB : Module.finrank F₂ B ≤ 1)
    (hC : Module.finrank F₂ C ≤ 1) :
    Module.finrank F₂ G ≤ 3 := by
  have hAB := Submodule.finrank_add_le_finrank_add_finrank A B
  have hABC := Submodule.finrank_add_le_finrank_add_finrank (A ⊔ B) C
  have hmono := Submodule.finrank_mono hG
  omega

/-- The two repaired low-defect obligations imply the rank-eight stability
surface consumed by the final circuit split. -/
theorem stableIntrinsicCapacityAtMostOne_of_lowDefectLedgers
    (hZero : StableIntrinsicCapacityAtZero)
    (hOne : IntrinsicOneDefectColourLedger) :
    StableIntrinsicCapacityAtMostOne := by
  intro j p hdec hdef
  by_cases hzero : Module.finrank F₂ (presentationDefect p) = 0
  · exact hZero p hdec hzero
  have hone : Module.finrank F₂ (presentationDefect p) = 1 := by omega
  intro V hreach
  have hquad : intrinsicCapacityState p ≤ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace _
  have hbudget := hreach.quadraticDefect_add_high_le_three hquad
  rw [intrinsicCapacityState_defectRank p hdec, hone] at hbudget
  have hbase : stateTargetRank (intrinsicCapacityState p) ≤ 5 := by
    rw [intrinsicCapacityState_targetRank]
    exact targetCapacity_le_five_of_finrank_le_one _ (by omega)
  have hgain := hOne p hdec hone V hreach
  have hhigh : stateHighRank V = 0 ∨
      stateHighRank V = 1 ∨ stateHighRank V = 2 := by omega
  rcases hhigh with hhigh | hhigh | hhigh
  · simp [hhigh] at hgain
    omega
  · simp [hhigh] at hgain
    omega
  · simp [hhigh] at hgain
    omega

end
end N5
end UnrestrictedBooleanMul
