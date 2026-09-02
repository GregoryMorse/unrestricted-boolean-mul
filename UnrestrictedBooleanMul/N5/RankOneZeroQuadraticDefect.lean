import UnrestrictedBooleanMul.N5.RankOneCorrectionColour

/-!
# Rank-one closure at zero quadratic defect

When the current state has no defect inside its quadratic part, every old
quadratic wire is target-valued.  Under the first-order target-containment
hypothesis, the correction-colour rewiring therefore places both its
quadratic factor and its quadratic correction inside the first-order envelope.
The checked target-clean absorption theorem then excludes the escape.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Zero quadratic defect means that every quadratic member of the state is
already in `Aff + T`. -/
theorem stateQuadraticPart_le_targetAmbient_of_defectRank_eq_zero
    (V : Submodule F₂ (ANF 10))
    (hdef : stateQuadraticDefectRank V = 0) :
    stateQuadraticPart V ≤ N4.targetAmbient 10 (mulTarget 5) := by
  have himageRank : Module.finrank F₂
      (stateDefectImage (stateQuadraticPart V)) = 0 := by
    rw [stateDefectImage_finrank]
    exact hdef
  have himageBot : stateDefectImage (stateQuadraticPart V) = ⊥ :=
    Submodule.finrank_eq_zero.mp himageRank
  intro p hp
  have hpImage : Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) p ∈
      stateDefectImage (stateQuadraticPart V) := ⟨p, hp, rfl⟩
  rw [himageBot] at hpImage
  have hpZero : Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) p = 0 := by
    simpa using hpImage
  exact (Submodule.Quotient.mk_eq_zero _).1 hpZero

theorem quadratic_mem_targetAmbient_of_stateQuadraticDefectRank_eq_zero
    (V : Submodule F₂ (ANF 10)) {p : ANF 10}
    (hdef : stateQuadraticDefectRank V = 0)
    (hpV : p ∈ V) (hpquad : p ∈ N4.quadraticANFSpace 10) :
    p ∈ N4.targetAmbient 10 (mulTarget 5) :=
  stateQuadraticPart_le_targetAmbient_of_defectRank_eq_zero V hdef
    ⟨hpV, hpquad⟩

/-- A reconstructed affine-plus-Hankel quadratic is a member of the target
ambient. -/
theorem quadraticCoordinateANF_target_mem_targetAmbient
    (a : F₂) (ell : LinearForm) (c : TargetCoeff) :
    quadraticCoordinateANF a ell (targetTwo c) ∈
      N4.targetAmbient 10 (mulTarget 5) := by
  have haff : a • (1 : ANF 10) + linearANFTen ell ∈ affine 10 :=
    (affine 10).add_mem
      ((affine 10).smul_mem a (one_mem_affine 10))
      (linearANFTen_mem_affine ell)
  rw [quadraticCoordinateANF, quadraticANFOfForm_targetTwo]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left haff)
    (Submodule.mem_sup_right (targetANF_mem_mulTarget c))

/-- The rank-one colour branch is closed whenever the current state has zero
quadratic defect and at most one high direction. -/
theorem rankOne_step_closed_of_zero_quadraticDefect_highRank_le_one
    (q : TwoForm) (hqdec : IsDecomposableTwo q)
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (g : (ANF 10) ⧸ N4.quadraticANFSpace 10)
    (hreach : DefectLegalSuffix (firstOrderAnchorState q) V)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hg : g ≠ 0)
    (hpattern : RankOneColourPattern
      (Submodule.mkQ (N4.quadraticANFSpace 10)) g X Y)
    (hquadDef : stateQuadraticDefectRank V = 0)
    (hhigh : stateHighRank V ≤ 1) :
    andExtend V X Y ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState := by
  by_contra hescape
  rcases exists_normalized_rankOne_missing_escape
      V X Y hX hY hold hescape g hg hpattern with
    ⟨U, c, a, ell, u, v, hUV, hUhigh, hcV, hcquad, hu, hv,
      hextend, _hleft, _hright, heq⟩
  have hAffV : affine 10 ≤ V :=
    (E2.affine_le_quadraticEnvelopeState
      (firstOrderAnchorTwoSpace q)).trans hreach.start_le
  rcases exists_rankOne_rewiring_of_stateHighRank_le_one
      V U c (quadraticCoordinateANF a ell
        (targetTwo (firstOrderMissingCoeff + u))) v
      hAffV hUV hcV hUhigh hcquad heq hv hhigh with
    ⟨c', v', hc'V, hc'quad, hv'V, hv'quad, hextend', heq',
      _hleft', hright'⟩
  have hc'Target :=
    quadratic_mem_targetAmbient_of_stateQuadraticDefectRank_eq_zero
      V hquadDef hc'V hc'quad
  have hv'Target :=
    quadratic_mem_targetAmbient_of_stateQuadraticDefectRank_eq_zero
      V hquadDef hv'V hv'quad
  have hc'Envelope : c' ∈ firstOrderEnvelopeState :=
    hold ⟨hc'V, hc'Target⟩
  have hv'Envelope : v' ∈ firstOrderEnvelopeState :=
    hold ⟨hv'V, hv'Target⟩
  have hc'Two : quadraticProjection 10 c' ∈
      firstOrderEnvelopeTwoSpace :=
    ((E2.mem_quadraticEnvelopeState_iff
      firstOrderEnvelopeTwoSpace c').1 hc'Envelope).2
  have hc'Clean : quadraticProjection 10 c' ∈
      targetCleanSecondJetSpace ⊔
        Submodule.span F₂ ({q} : Set TwoForm) :=
    firstOrderAnchorTwoSpace_le_targetClean_sup_anchor q
      (Submodule.mem_sup_left hc'Two)
  apply rankOne_envelopeCorrected_escape_impossible
    U c' hUhigh hc'quad a ell u hu q hqdec hc'Clean
      v' hv'Envelope heq' hright'

end
end N5
end UnrestrictedBooleanMul
