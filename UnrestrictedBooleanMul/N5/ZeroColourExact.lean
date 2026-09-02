import UnrestrictedBooleanMul.N5.ZeroColourEscapeReduction
import UnrestrictedBooleanMul.N5.FirstOrderLowCollisionExact

/-!
# Exact closure of the fixed first-order zero-colour branch

When the quadratic part has not grown and there is at most one old high
direction, the suffix reduction expresses a putative zero-colour escape as a
collision of two products of first-order-envelope wires.  The literal
envelope theorem excludes that collision without a same-plane hypothesis.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem zeroColour_step_closed_of_fixedFirstOrder_highRank_le_one
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hreach : DefectLegalSuffix firstOrderEnvelopeState V)
    (hquad : stateQuadraticPart V = firstOrderEnvelopeState)
    (hhigh : stateHighRank V ≤ 1)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hXquad : X ∈ N4.quadraticANFSpace 10)
    (hYquad : Y ∈ N4.quadraticANFSpace 10)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState) :
    andExtend V X Y ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState := by
  by_contra hescape
  rcases exists_base_twoProduct_equation_of_zeroColour_escape
      X Y hreach
      (E2.quadraticEnvelopeState_le_quadraticANFSpace
        firstOrderEnvelopeTwoSpace)
      hquad hhigh hX hY hXquad hYquad hold hescape with
    ⟨a, ell, u, p, q, w, hu, hXenv, hYenv,
      hpEnv, hqEnv, hwEnv, _hpqV, heq⟩
  have hpQuad : p ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      firstOrderEnvelopeTwoSpace hpEnv
  have hqQuad : q ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      firstOrderEnvelopeTwoSpace hqEnv
  exact firstOrder_missing_escape_ne_oldProduct_ANF
    X Y p q hXquad hYquad hpQuad hqQuad
      hXenv hYenv hpEnv hqEnv a ell u hu w hwEnv heq

/-- Anchored form when the decomposable anchor is already target-valued. -/
theorem zeroColour_step_closed_of_fixedAnchor_highRank_le_one
    (anchor : TwoForm) (hanchorDec : IsDecomposableTwo anchor)
    (hanchorTarget : anchor ∈ targetTwoSpace)
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hreach : DefectLegalSuffix (firstOrderAnchorState anchor) V)
    (hquad : stateQuadraticPart V = firstOrderAnchorState anchor)
    (hhigh : stateHighRank V ≤ 1)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hXquad : X ∈ N4.quadraticANFSpace 10)
    (hYquad : Y ∈ N4.quadraticANFSpace 10)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState) :
    andExtend V X Y ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState := by
  have hanchor := firstOrderAnchorState_eq_firstOrderEnvelope_of_mem_target
    anchor hanchorDec hanchorTarget
  rw [hanchor] at hreach hquad
  exact zeroColour_step_closed_of_fixedFirstOrder_highRank_le_one
    V X Y hreach hquad hhigh hX hY hXquad hYquad hold

end
end N5
end UnrestrictedBooleanMul
