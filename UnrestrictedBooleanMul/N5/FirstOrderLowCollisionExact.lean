import UnrestrictedBooleanMul.N5.EnvelopeSemanticExact
import UnrestrictedBooleanMul.N5.FirstOrderLowCollision

/-!
# Exact first-order collisions with an arbitrary old low product

The literal envelope theorem removes the former same-plane restriction.  A
first escaping low--low product cannot be corrected by any other product of
quadratic wires in the first-order envelope.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxHeartbeats 600000

theorem firstOrderEnvelope_actualLowProducts_projection_ne_missing
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hsum :
      quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c' ∈
        N4.quadraticANFSpace 10) :
    quadraticProjection 10
        (quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c') ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c' :=
    lowProductHighClass_eq_of_product_sum_mem_quadratic
      a b a' b' ell m ell' m' q c q' c' hsum
  have hshadow := semanticEnvelope_exact_shadow
    a b a' b' ell m ell' m' q c q' c'
      hq hc hq' hc' hhigh u hu
  intro hprojection
  apply hshadow
  simpa only [map_add, quadraticProjection_quadraticCoordinateANF_mul]
    using hprojection

theorem firstOrder_missing_escape_ne_oldProduct
    (a b a' b' aT : F₂)
    (ell m ell' m' ellT : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (w : ANF 10) (hw : w ∈ firstOrderEnvelopeState) :
    quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c ≠
      quadraticCoordinateANF aT ellT
          (targetTwo (firstOrderMissingCoeff + u)) +
        (quadraticCoordinateANF a' ell' q' *
          quadraticCoordinateANF b' m' c' + w) := by
  intro heq
  rcases exists_firstOrderCoeff_of_mem_envelopeState hw with
    ⟨uw, huw, hprojectionW⟩
  have hsumEq :
      quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c' =
        quadraticCoordinateANF aT ellT
            (targetTwo (firstOrderMissingCoeff + u)) + w := by
    rw [heq]
    calc
      (quadraticCoordinateANF aT ellT
            (targetTwo (firstOrderMissingCoeff + u)) +
          (quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c' + w)) +
            quadraticCoordinateANF a' ell' q' *
              quadraticCoordinateANF b' m' c' =
          quadraticCoordinateANF aT ellT
              (targetTwo (firstOrderMissingCoeff + u)) + w +
            ((quadraticCoordinateANF a' ell' q' *
                quadraticCoordinateANF b' m' c') +
              (quadraticCoordinateANF a' ell' q' *
                quadraticCoordinateANF b' m' c')) := by ac_rfl
      _ = quadraticCoordinateANF aT ellT
            (targetTwo (firstOrderMissingCoeff + u)) + w := by
        rw [anf_add_self, add_zero]
  have hsum :
      quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c' ∈
        N4.quadraticANFSpace 10 := by
    rw [hsumEq]
    exact (N4.quadraticANFSpace 10).add_mem
      (quadraticCoordinateANF_mem_quadraticANFSpace aT ellT
        (targetTwo (firstOrderMissingCoeff + u)))
      (E2.quadraticEnvelopeState_le_quadraticANFSpace
        firstOrderEnvelopeTwoSpace hw)
  have hforbidden := firstOrderEnvelope_actualLowProducts_projection_ne_missing
    a b a' b' ell m ell' m' q c q' c'
      hq hc hq' hc' (u + uw)
      ((firstOrderEnvelopeCoeffSpace).add_mem hu huw) hsum
  apply hforbidden
  calc
    quadraticProjection 10
        (quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c') =
        quadraticProjection 10
          (quadraticCoordinateANF aT ellT
            (targetTwo (firstOrderMissingCoeff + u)) + w) :=
      congrArg (quadraticProjection 10) hsumEq
    _ = targetTwo (firstOrderMissingCoeff + u) + targetTwo uw := by
      rw [map_add, quadraticProjection_quadraticCoordinateANF, hprojectionW]
    _ = targetTwo ((firstOrderMissingCoeff + u) + uw) := by
      exact (targetTwoLinear.map_add _ _).symm
    _ = targetTwo (firstOrderMissingCoeff + (u + uw)) := by
      rw [add_assoc]

/-- Coordinate-free wire-level form of the arbitrary old-product collision. -/
theorem firstOrder_missing_escape_ne_oldProduct_ANF
    (X Y P Q : ANF 10)
    (hXquad : X ∈ N4.quadraticANFSpace 10)
    (hYquad : Y ∈ N4.quadraticANFSpace 10)
    (hPquad : P ∈ N4.quadraticANFSpace 10)
    (hQquad : Q ∈ N4.quadraticANFSpace 10)
    (hXenv : X ∈ firstOrderEnvelopeState)
    (hYenv : Y ∈ firstOrderEnvelopeState)
    (hPenv : P ∈ firstOrderEnvelopeState)
    (hQenv : Q ∈ firstOrderEnvelopeState)
    (aT : F₂) (ellT : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (w : ANF 10) (hw : w ∈ firstOrderEnvelopeState) :
    X * Y ≠ quadraticCoordinateANF aT ellT
        (targetTwo (firstOrderMissingCoeff + u)) + (P * Q + w) := by
  rcases exists_quadraticCoordinates hXquad with ⟨a, ell, x, hX⟩
  rcases exists_quadraticCoordinates hYquad with ⟨b, m, y, hY⟩
  rcases exists_quadraticCoordinates hPquad with ⟨a', ell', p, hP⟩
  rcases exists_quadraticCoordinates hQquad with ⟨b', m', q, hQ⟩
  have hxU : x ∈ firstOrderEnvelopeTwoSpace := by
    have hx := ((E2.mem_quadraticEnvelopeState_iff
      firstOrderEnvelopeTwoSpace X).1 hXenv).2
    rwa [hX, quadraticProjection_quadraticCoordinateANF] at hx
  have hyU : y ∈ firstOrderEnvelopeTwoSpace := by
    have hy := ((E2.mem_quadraticEnvelopeState_iff
      firstOrderEnvelopeTwoSpace Y).1 hYenv).2
    rwa [hY, quadraticProjection_quadraticCoordinateANF] at hy
  have hpU : p ∈ firstOrderEnvelopeTwoSpace := by
    have hp := ((E2.mem_quadraticEnvelopeState_iff
      firstOrderEnvelopeTwoSpace P).1 hPenv).2
    rwa [hP, quadraticProjection_quadraticCoordinateANF] at hp
  have hqU : q ∈ firstOrderEnvelopeTwoSpace := by
    have hq := ((E2.mem_quadraticEnvelopeState_iff
      firstOrderEnvelopeTwoSpace Q).1 hQenv).2
    rwa [hQ, quadraticProjection_quadraticCoordinateANF] at hq
  rw [hX, hY, hP, hQ]
  exact firstOrder_missing_escape_ne_oldProduct
    a b a' b' aT ell m ell' m' ellT x y p q
      hxU hyU hpU hqU u hu w hw

end
end N5
end UnrestrictedBooleanMul
