import UnrestrictedBooleanMul.N5.StableTarget
import UnrestrictedBooleanMul.N5.E2.EnvelopeStates
import UnrestrictedBooleanMul.N5.FirstOrderEnvelope

/-!
# The codimension-one first-order envelope as an ANF state

This lifts the eight-dimensional target envelope `U` of Section 11 into the
actual ten-variable circuit state.  It is entirely contained in `Aff + T`,
has target rank eight, and has zero quotient defect.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def firstOrderEnvelopeState : Submodule F₂ (ANF 10) :=
  E2.quadraticEnvelopeState firstOrderEnvelopeTwoSpace

theorem affine_le_firstOrderEnvelopeState :
    affine 10 ≤ firstOrderEnvelopeState :=
  E2.affine_le_quadraticEnvelopeState firstOrderEnvelopeTwoSpace

theorem firstOrderEnvelopeState_le_targetAmbient :
    firstOrderEnvelopeState ≤ N4.targetAmbient 10 (mulTarget 5) := by
  rw [firstOrderEnvelopeState, E2.quadraticEnvelopeState,
    E2.targetAmbient_eq_affine_sup_quadraticLift]
  exact sup_le_sup le_rfl
    (Submodule.map_mono firstOrderEnvelopeTwoSpace_le_targetTwoSpace)

theorem firstOrderEnvelopeState_targetRank :
    stateTargetRank firstOrderEnvelopeState = 8 := by
  rw [stateTargetRank, firstOrderEnvelopeState,
    E2.quadraticEnvelopeState_targetRank,
    inf_eq_left.mpr firstOrderEnvelopeTwoSpace_le_targetTwoSpace,
    firstOrderEnvelopeTwoSpace_finrank]

theorem firstOrderEnvelopeState_defectRank :
    N4.flagDefectRank firstOrderEnvelopeState (mulTarget 5) = 0 := by
  rw [firstOrderEnvelopeState, E2.quadraticEnvelopeState_defectRank,
    inf_eq_left.mpr firstOrderEnvelopeTwoSpace_le_targetTwoSpace,
    firstOrderEnvelopeTwoSpace_finrank]

/-- The stable-subspace formulation of Theorem 12.3 immediately gives the
rank-eight stable-target formulation used by the final deficit ledger. -/
theorem stableFirstOrder_targetRank
    {W : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ W)
    (hstable : StableTargetSubspace W firstOrderEnvelopeState) :
    StableTargetRank W 8 := by
  apply stableTargetRank_of_subspace hAff
    affine_le_firstOrderEnvelopeState
  · have hfin := E2.quadraticEnvelopeState_finrank
      firstOrderEnvelopeTwoSpace
    rw [firstOrderEnvelopeTwoSpace_finrank] at hfin
    exact hfin
  · exact hstable

end
end N5
end UnrestrictedBooleanMul
