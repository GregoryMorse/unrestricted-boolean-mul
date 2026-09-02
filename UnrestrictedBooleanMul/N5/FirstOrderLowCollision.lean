import UnrestrictedBooleanMul.N5.FirstOrderEscape
import UnrestrictedBooleanMul.N5.EnvelopeSemantic

/-!
# Closing a first-order escape against an old low product

This module converts the normalized first-escape equation into the intrinsic
two-product collision excluded by the first-order envelope theorem.  The
argument is purely algebraic: an envelope correction changes only the allowed
quadratic target coefficient.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxHeartbeats 600000

/-- Every word in the lifted first-order envelope has an allowed target
coefficient as its quadratic projection. -/
theorem exists_firstOrderCoeff_of_mem_envelopeState
    {w : ANF 10} (hw : w ∈ firstOrderEnvelopeState) :
    ∃ u : TargetCoeff, u ∈ firstOrderEnvelopeCoeffSpace ∧
      quadraticProjection 10 w = targetTwo u := by
  change w ∈ E2.quadraticEnvelopeState firstOrderEnvelopeTwoSpace at hw
  have hprojection :=
    ((E2.mem_quadraticEnvelopeState_iff
      firstOrderEnvelopeTwoSpace w).1 hw).2
  rcases hprojection with ⟨u, hu, htarget⟩
  exact ⟨u, hu, htarget.symm⟩

/-- A normalized missing-target escape cannot be corrected by an old low
product whose independent quadratic factor pair spans the same intrinsic
plane, even after adding an arbitrary word already in the envelope. -/
theorem firstOrder_missing_escape_ne_sameSpan_oldProduct
    (a b a' b' aT : F₂)
    (ell m ell' m' ellt : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hspan : Submodule.span F₂ ({q', c'} : Set TwoForm) =
      Submodule.span F₂ ({q, c} : Set TwoForm))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (w : ANF 10) (hw : w ∈ firstOrderEnvelopeState) :
    quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c ≠
      quadraticCoordinateANF aT ellt
          (targetTwo (firstOrderMissingCoeff + u)) +
        (quadraticCoordinateANF a' ell' q' *
          quadraticCoordinateANF b' m' c' + w) := by
  intro heq
  rcases exists_firstOrderCoeff_of_mem_envelopeState hw with
    ⟨uw, huw, hprojectionW⟩
  have hsum :
      quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c' ∈
        N4.quadraticANFSpace 10 := by
    have hsumEq :
        quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
            quadraticCoordinateANF a' ell' q' *
              quadraticCoordinateANF b' m' c' =
          quadraticCoordinateANF aT ellt
              (targetTwo (firstOrderMissingCoeff + u)) + w := by
      rw [heq]
      calc
        (quadraticCoordinateANF aT ellt
              (targetTwo (firstOrderMissingCoeff + u)) +
            (quadraticCoordinateANF a' ell' q' *
              quadraticCoordinateANF b' m' c' + w)) +
              quadraticCoordinateANF a' ell' q' *
                quadraticCoordinateANF b' m' c' =
            quadraticCoordinateANF aT ellt
                (targetTwo (firstOrderMissingCoeff + u)) + w +
              ((quadraticCoordinateANF a' ell' q' *
                  quadraticCoordinateANF b' m' c') +
                (quadraticCoordinateANF a' ell' q' *
                  quadraticCoordinateANF b' m' c')) := by ac_rfl
        _ = quadraticCoordinateANF aT ellt
              (targetTwo (firstOrderMissingCoeff + u)) + w := by
          rw [anf_add_self, add_zero]
    rw [hsumEq]
    exact (N4.quadraticANFSpace 10).add_mem
      (quadraticCoordinateANF_mem_quadraticANFSpace aT ellt
        (targetTwo (firstOrderMissingCoeff + u)))
      (E2.quadraticEnvelopeState_le_quadraticANFSpace
        firstOrderEnvelopeTwoSpace hw)
  have hforbidden := sameSpan_actualLowProducts_projection_ne_missing
    a b a' b' ell m ell' m' q c q' c' hq hc hind' hspan
      (u + uw) ((firstOrderEnvelopeCoeffSpace).add_mem hu huw) hsum
  apply hforbidden
  have hsumEq :
      quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c' =
        quadraticCoordinateANF aT ellt
            (targetTwo (firstOrderMissingCoeff + u)) + w := by
    rw [heq]
    calc
      (quadraticCoordinateANF aT ellt
            (targetTwo (firstOrderMissingCoeff + u)) +
          (quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c' + w)) +
            quadraticCoordinateANF a' ell' q' *
              quadraticCoordinateANF b' m' c' =
          quadraticCoordinateANF aT ellt
              (targetTwo (firstOrderMissingCoeff + u)) + w +
            ((quadraticCoordinateANF a' ell' q' *
                quadraticCoordinateANF b' m' c') +
              (quadraticCoordinateANF a' ell' q' *
                quadraticCoordinateANF b' m' c')) := by ac_rfl
      _ = quadraticCoordinateANF aT ellt
            (targetTwo (firstOrderMissingCoeff + u)) + w := by
        rw [anf_add_self, add_zero]
  rw [hsumEq, map_add, quadraticProjection_quadraticCoordinateANF,
    hprojectionW]
  change targetTwoLinear (firstOrderMissingCoeff + u) +
      targetTwoLinear uw =
    targetTwoLinear (firstOrderMissingCoeff + (u + uw))
  rw [← targetTwoLinear.map_add]
  congr 1
  ac_rfl

end
end N5
end UnrestrictedBooleanMul
