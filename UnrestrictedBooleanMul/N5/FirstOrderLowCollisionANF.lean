import UnrestrictedBooleanMul.N5.FirstOrderLowCollision

/-!
# Coordinate-free ANF wrapper for the first-order low-product collision

The complete shadow theorem is stated in constant/linear/two-form coordinates.
This module reconstructs those coordinates internally for four actual
quadratic wires, leaving only the intrinsic equality of their quadratic
factor planes in the public interface.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Two actual products of first-order-envelope quadratic wires whose old
factor pair is independent and spans the same quadratic plane cannot differ
by the missing target coset plus an envelope correction. -/
theorem firstOrder_missing_escape_ne_sameSpan_oldProduct_ANF
    (X Y P Q : ANF 10)
    (hXquad : X ∈ N4.quadraticANFSpace 10)
    (hYquad : Y ∈ N4.quadraticANFSpace 10)
    (hPquad : P ∈ N4.quadraticANFSpace 10)
    (hQquad : Q ∈ N4.quadraticANFSpace 10)
    (hXenv : X ∈ firstOrderEnvelopeState)
    (hYenv : Y ∈ firstOrderEnvelopeState)
    (hind : LinearIndependent F₂
      (quadraticPlaneDirections
        (quadraticProjection 10 P) (quadraticProjection 10 Q)))
    (hspan : Submodule.span F₂
        ({quadraticProjection 10 P, quadraticProjection 10 Q} : Set TwoForm) =
      Submodule.span F₂
        ({quadraticProjection 10 X, quadraticProjection 10 Y} : Set TwoForm))
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
  have hind' : LinearIndependent F₂ (quadraticPlaneDirections p q) := by
    simpa [hP, hQ, quadraticProjection_quadraticCoordinateANF] using hind
  have hspan' : Submodule.span F₂ ({p, q} : Set TwoForm) =
      Submodule.span F₂ ({x, y} : Set TwoForm) := by
    simpa [hX, hY, hP, hQ,
      quadraticProjection_quadraticCoordinateANF] using hspan
  rw [hX, hY, hP, hQ]
  exact firstOrder_missing_escape_ne_sameSpan_oldProduct
    a b a' b' aT ell m ell' m' ellT x y p q hxU hyU hind' hspan'
      u hu w hw

end
end N5
end UnrestrictedBooleanMul
