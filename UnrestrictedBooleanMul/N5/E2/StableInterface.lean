import UnrestrictedBooleanMul.N5.StableTarget
import UnrestrictedBooleanMul.N5.E2.EnvelopeStates

/-!
# Stable-envelope interface to the completion contradiction

Once the feedback calculations prove the rank-eight invariant for a concrete
nonextremal envelope, the remaining suffix arithmetic is automatic.  These
lemmas keep that interface explicit and prevent per-source bounds from being
silently added.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

noncomputable section

theorem wStar_suffixDeficit_positive
    (hstable : StableTargetRank wStarState 8) :
    1 ≤ suffixDeficit wStarState := by
  apply suffixDeficit_positive_of_stableTargetRank_eight
    (W := wStarState)
  · exact affine_le_quadraticEnvelopeState wStarTwoSpace
  · rw [wStarState_defectRank]
    omega
  · rw [stateTargetRank, wStarState_targetRank]
    omega
  · exact hstable

theorem wPQ_suffixDeficit_positive
    (hstable : StableTargetRank wPQState 8) :
    1 ≤ suffixDeficit wPQState := by
  apply suffixDeficit_positive_of_stableTargetRank_eight
    (W := wPQState)
  · exact affine_le_quadraticEnvelopeState wPQTwoSpace
  · rw [wPQState_defectRank]
    omega
  · rw [stateTargetRank, wPQState_targetRank]
    omega
  · exact hstable

theorem wThreeP_suffixDeficit_positive
    (hstable : StableTargetRank wThreePState 8) :
    1 ≤ suffixDeficit wThreePState := by
  apply suffixDeficit_positive_of_stableTargetRank_eight
    (W := wThreePState)
  · exact affine_le_quadraticEnvelopeState wThreePTwoSpace
  · rw [wThreePState_defectRank]
    omega
  · rw [stateTargetRank, wThreePState_targetRank]
    omega
  · exact hstable

end
end E2
end N5
end UnrestrictedBooleanMul
