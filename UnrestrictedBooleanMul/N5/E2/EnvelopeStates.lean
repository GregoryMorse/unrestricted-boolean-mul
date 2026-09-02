import UnrestrictedBooleanMul.N5.QuadraticLift
import UnrestrictedBooleanMul.N5.E2.EnvelopeIntersections

/-!
# Concrete quadratic envelopes as ANF wire states

The coordinate envelopes are lifted through the canonical pure-quadratic
section and adjoined to the affine input space.  This file proves the generic
target/defect formulas and specializes them to the three nonextremal
two-defect envelopes of Section 10.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

noncomputable section

theorem quadraticLiftSpace_targetTwoSpace :
    quadraticLiftSpace targetTwoSpace = mulTarget 5 := by
  apply le_antisymm
  · rintro p ⟨q, ⟨c, rfl⟩, rfl⟩
    change quadraticANFOfForm (targetTwo c) ∈ mulTarget 5
    rw [quadraticANFOfForm_targetTwo]
    exact targetANF_mem_mulTarget c
  · intro p hp
    rcases exists_targetCoeff_of_mem_mulTarget hp with ⟨c, rfl⟩
    rw [← quadraticANFOfForm_targetTwo]
    exact ⟨targetTwo c, ⟨c, rfl⟩, rfl⟩

theorem targetAmbient_eq_affine_sup_quadraticLift :
    N4.targetAmbient 10 (mulTarget 5) =
      affine 10 ⊔ quadraticLiftSpace targetTwoSpace := by
  rw [N4.targetAmbient, quadraticLiftSpace_targetTwoSpace]

/-- The ANF state associated with a quadratic coordinate envelope. -/
def quadraticEnvelopeState (W : Submodule F₂ TwoForm) :
    Submodule F₂ (ANF 10) :=
  affine 10 ⊔ quadraticLiftSpace W

theorem affine_le_quadraticEnvelopeState (W : Submodule F₂ TwoForm) :
    affine 10 ≤ quadraticEnvelopeState W := le_sup_left

theorem quadraticEnvelopeState_finrank (W : Submodule F₂ TwoForm) :
    Module.finrank F₂ (quadraticEnvelopeState W) =
      Module.finrank F₂ (affine 10) + Module.finrank F₂ W := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (affine 10) (quadraticLiftSpace W)
  rw [(affine_disjoint_quadraticLiftSpace W).eq_bot, finrank_bot,
    add_zero, quadraticLiftSpace_finrank] at hdim
  exact hdim

theorem quadraticEnvelopeState_inf_targetAmbient
    (W : Submodule F₂ TwoForm) :
    quadraticEnvelopeState W ⊓ N4.targetAmbient 10 (mulTarget 5) =
      affine 10 ⊔ quadraticLiftSpace (W ⊓ targetTwoSpace) := by
  rw [quadraticEnvelopeState, targetAmbient_eq_affine_sup_quadraticLift]
  apply le_antisymm
  · rintro p ⟨hpW, hpT⟩
    rcases Submodule.mem_sup.mp hpW with ⟨a, ha, x, hx, rfl⟩
    rcases hx with ⟨q, hqW, rfl⟩
    rcases Submodule.mem_sup.mp hpT with ⟨b, hb, y, hy, heq⟩
    rcases hy with ⟨t, htT, rfl⟩
    change b + quadraticANFOfForm t = a + quadraticANFOfForm q at heq
    have hsum : quadraticANFOfForm q + quadraticANFOfForm t = a + b := by
      calc
        quadraticANFOfForm q + quadraticANFOfForm t =
            (a + a) +
              (quadraticANFOfForm q + quadraticANFOfForm t) := by
                rw [anf_add_self, zero_add]
        _ = a + (a + quadraticANFOfForm q) +
              quadraticANFOfForm t := by ac_rfl
        _ = a + (b + quadraticANFOfForm t) +
              quadraticANFOfForm t := by rw [← heq]
        _ = a + b +
              (quadraticANFOfForm t + quadraticANFOfForm t) := by ac_rfl
        _ = a + b := by rw [anf_add_self, add_zero]
    have hpure : quadraticANFOfForm q + quadraticANFOfForm t ∈
        pureQuadraticANFSpace :=
      pureQuadraticANFSpace.add_mem ⟨q, rfl⟩ ⟨t, rfl⟩
    have haff : quadraticANFOfForm q + quadraticANFOfForm t ∈
        affine 10 := hsum.symm ▸ (affine 10).add_mem ha hb
    have hzero : quadraticANFOfForm q + quadraticANFOfForm t = 0 := by
      have hbot := (disjoint_iff_inf_le.mp
        affine_disjoint_pureQuadraticANFSpace) ⟨haff, hpure⟩
      simpa using hbot
    have hqt : q = t := by
      apply quadraticANFOfFormLinear_injective
      calc
        quadraticANFOfForm q = quadraticANFOfForm q + 0 := by rw [add_zero]
        _ = quadraticANFOfForm q +
            (quadraticANFOfForm q + quadraticANFOfForm t) := by rw [hzero]
        _ = (quadraticANFOfForm q + quadraticANFOfForm q) +
            quadraticANFOfForm t := by ac_rfl
        _ = quadraticANFOfForm t := by rw [anf_add_self, zero_add]
    subst t
    exact Submodule.add_mem _
      (Submodule.mem_sup_left ha)
      (Submodule.mem_sup_right ⟨q, ⟨hqW, htT⟩, rfl⟩)
  · apply sup_le
    · intro a ha
      exact ⟨Submodule.mem_sup_left ha, Submodule.mem_sup_left ha⟩
    · rintro p ⟨q, ⟨hqW, hqT⟩, rfl⟩
      exact ⟨Submodule.mem_sup_right ⟨q, hqW, rfl⟩,
        Submodule.mem_sup_right ⟨q, hqT, rfl⟩⟩

theorem quadraticEnvelopeState_targetRank (W : Submodule F₂ TwoForm) :
    N4.flagTargetRank (quadraticEnvelopeState W) (mulTarget 5) =
      Module.finrank F₂ ↑(W ⊓ targetTwoSpace) := by
  have hdim := quadraticEnvelopeState_finrank (W ⊓ targetTwoSpace)
  unfold N4.flagTargetRank
  rw [quadraticEnvelopeState_inf_targetAmbient]
  change Module.finrank F₂
      ↑(quadraticEnvelopeState (W ⊓ targetTwoSpace)) -
        Module.finrank F₂ (affine 10) = _
  rw [hdim]
  omega

theorem quadraticEnvelopeState_defectRank (W : Submodule F₂ TwoForm) :
    N4.flagDefectRank (quadraticEnvelopeState W) (mulTarget 5) =
      Module.finrank F₂ W -
        Module.finrank F₂ ↑(W ⊓ targetTwoSpace) := by
  have hstate := quadraticEnvelopeState_finrank W
  have hinter := quadraticEnvelopeState_finrank (W ⊓ targetTwoSpace)
  have hle : Module.finrank F₂ ↑(W ⊓ targetTwoSpace) ≤
      Module.finrank F₂ W := Submodule.finrank_mono inf_le_left
  unfold N4.flagDefectRank
  rw [quadraticEnvelopeState_inf_targetAmbient]
  change Module.finrank F₂ (quadraticEnvelopeState W) -
      Module.finrank F₂
        (quadraticEnvelopeState (W ⊓ targetTwoSpace)) = _
  rw [hstate, hinter]
  omega

def wStarState : Submodule F₂ (ANF 10) :=
  quadraticEnvelopeState wStarTwoSpace

def wPQState : Submodule F₂ (ANF 10) :=
  quadraticEnvelopeState wPQTwoSpace

def wThreePState : Submodule F₂ (ANF 10) :=
  quadraticEnvelopeState wThreePTwoSpace

theorem wStarState_targetRank :
    N4.flagTargetRank wStarState (mulTarget 5) = 5 := by
  rw [wStarState, quadraticEnvelopeState_targetRank, inf_comm,
    wStar_target_intersection_finrank]

theorem wStarState_defectRank :
    N4.flagDefectRank wStarState (mulTarget 5) = 2 := by
  rw [wStarState, quadraticEnvelopeState_defectRank,
    wStarTwoSpace_finrank, inf_comm, wStar_target_intersection_finrank]

theorem wPQState_targetRank :
    N4.flagTargetRank wPQState (mulTarget 5) = 5 := by
  rw [wPQState, quadraticEnvelopeState_targetRank, inf_comm,
    wPQ_target_intersection_finrank]

theorem wPQState_defectRank :
    N4.flagDefectRank wPQState (mulTarget 5) = 2 := by
  rw [wPQState, quadraticEnvelopeState_defectRank,
    wPQTwoSpace_finrank, inf_comm, wPQ_target_intersection_finrank]

theorem wThreePState_targetRank :
    N4.flagTargetRank wThreePState (mulTarget 5) = 5 := by
  rw [wThreePState, quadraticEnvelopeState_targetRank, inf_comm,
    wThreeP_target_intersection_finrank]

theorem wThreePState_defectRank :
    N4.flagDefectRank wThreePState (mulTarget 5) = 2 := by
  rw [wThreePState, quadraticEnvelopeState_defectRank,
    wThreePTwoSpace_finrank, inf_comm,
    wThreeP_target_intersection_finrank]

end
end E2
end N5
end UnrestrictedBooleanMul
