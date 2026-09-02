import UnrestrictedBooleanMul.N5.FirstOrderAnchorState
import UnrestrictedBooleanMul.N5.HighDefect

/-!
# Quadratic part of a suffix state with no new quadratic defect

A canonical anchor already contains the full first-order target envelope.
Consequently, if a reachable state has the same quadratic quotient defect as
the anchor, every quadratic word in that state is already in the anchor.
The proof uses equality of quotient images, not a choice of coordinates.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Above a canonical anchor, equality of quadratic defect forces equality of
the whole quadratic state. -/
theorem stateQuadraticPart_eq_firstOrderAnchor_of_equal_defect
    (q : TwoForm) {V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix (firstOrderAnchorState q) V)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hdef : stateQuadraticDefectRank V =
      N4.flagDefectRank (firstOrderAnchorState q) (mulTarget 5)) :
    stateQuadraticPart V = firstOrderAnchorState q := by
  have hanchorQuad : firstOrderAnchorState q ≤
      N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      (firstOrderAnchorTwoSpace q)
  have hsub : firstOrderAnchorState q ≤ stateQuadraticPart V := by
    intro p hp
    exact ⟨hreach.start_le hp, hanchorQuad hp⟩
  have himageEq : stateDefectImage (firstOrderAnchorState q) =
      stateDefectImage (stateQuadraticPart V) :=
    stateDefectImage_eq_of_le_of_flagDefectRank_eq hsub (by
      unfold stateQuadraticDefectRank at hdef
      exact hdef.symm)
  apply le_antisymm
  · intro p hp
    have hpImage : Submodule.mkQ
        (N4.targetAmbient 10 (mulTarget 5)) p ∈
        stateDefectImage (stateQuadraticPart V) := ⟨p, hp, rfl⟩
    rw [← himageEq] at hpImage
    rcases hpImage with ⟨a, ha, hmap⟩
    have hpaTarget : p + a ∈ N4.targetAmbient 10 (mulTarget 5) := by
      apply (Submodule.Quotient.mk_eq_zero _).1
      change Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5))
        (p + a) = 0
      rw [map_add, ← hmap]
      calc
        Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) a +
            Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) a =
          ((1 : F₂) + 1) •
            Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) a := by
              rw [add_smul, one_smul]
        _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
    have hpaV : p + a ∈ V :=
      V.add_mem hp.1 (hreach.start_le ha)
    have hpaEnvelope : p + a ∈ firstOrderEnvelopeState :=
      hold ⟨hpaV, hpaTarget⟩
    have hpaAnchor : p + a ∈ firstOrderAnchorState q :=
      firstOrderEnvelopeState_le_firstOrderAnchorState q hpaEnvelope
    have hpEq : p = (p + a) + a := by
      calc
        p = p + 0 := by rw [add_zero]
        _ = p + (a + a) := by rw [anf_add_self]
        _ = (p + a) + a := by ac_rfl
    rw [hpEq]
    exact (firstOrderAnchorState q).add_mem hpaAnchor ha
  · exact hsub

/-- Elementwise form used by factor localizations. -/
theorem quadratic_mem_firstOrderAnchor_of_equal_quadraticDefect
    (q : TwoForm) {V : Submodule F₂ (ANF 10)} {p : ANF 10}
    (hreach : DefectLegalSuffix (firstOrderAnchorState q) V)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hdef : stateQuadraticDefectRank V =
      N4.flagDefectRank (firstOrderAnchorState q) (mulTarget 5))
    (hpV : p ∈ V) (hpquad : p ∈ N4.quadraticANFSpace 10) :
    p ∈ firstOrderAnchorState q := by
  rw [← stateQuadraticPart_eq_firstOrderAnchor_of_equal_defect
    q hreach hold hdef]
  exact ⟨hpV, hpquad⟩

end
end N5
end UnrestrictedBooleanMul
