import UnrestrictedBooleanMul.N5.OneHighBirth
import UnrestrictedBooleanMul.N5.FirstOrderEscape

/-!
# Zero-colour escape as a two-product base equation

In the fixed-quadratic/one-high regime, the correction in a first escape is
one actual product of base quadratic wires plus a base correction.  Therefore
a zero-colour escaping gate reduces to a literal equation between two products
whose four factors all lie in the fixed base.  No suffix history remains in
the conclusion.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Semantic reduction of a zero-colour first escape to the two-product
equation consumed by the envelope-shadow layer. -/
theorem exists_base_twoProduct_equation_of_zeroColour_escape
    {A V : Submodule F₂ (ANF 10)} (X Y : ANF 10)
    (hreach : DefectLegalSuffix A V)
    (hAquad : A ≤ N4.quadraticANFSpace 10)
    (hquad : stateQuadraticPart V = A)
    (hhigh : stateHighRank V ≤ 1)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hXquad : X ∈ N4.quadraticANFSpace 10)
    (hYquad : Y ∈ N4.quadraticANFSpace 10)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hescape : ¬ (andExtend V X Y ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState)) :
    ∃ (a : F₂) (ell : LinearForm) (u : TargetCoeff)
        (p q w : ANF 10),
      u ∈ firstOrderEnvelopeCoeffSpace ∧
      X ∈ A ∧ Y ∈ A ∧ p ∈ A ∧ q ∈ A ∧ w ∈ A ∧
      p * q ∈ V ∧
      X * Y = quadraticCoordinateANF a ell
        (targetTwo (firstOrderMissingCoeff + u)) + (p * q + w) := by
  have hXA : X ∈ A := by
    have : X ∈ stateQuadraticPart V := ⟨hX, hXquad⟩
    rwa [hquad] at this
  have hYA : Y ∈ A := by
    have : Y ∈ stateQuadraticPart V := ⟨hY, hYquad⟩
    rwa [hquad] at this
  rcases exists_missing_product_equation_of_firstOrder_step_escape
      X Y hold hescape with ⟨a, ell, u, v, hu, hv, heq⟩
  rcases exists_base_lowProduct_add_base_of_highRank_le_one
      hreach hAquad hquad hhigh v hv with
    ⟨p, q, w, hpA, hqA, hwA, hpqV, hvEq⟩
  refine ⟨a, ell, u, p, q, w, hu, hXA, hYA,
    hpA, hqA, hwA, hpqV, ?_⟩
  rw [heq, hvEq]

end
end N5
end UnrestrictedBooleanMul
