import UnrestrictedBooleanMul.N5.ColourCases
import UnrestrictedBooleanMul.N5.FirstOrderEscape

/-!
# Circuit-level normalization of a rank-one escape

This module joins the literal high-quotient factor split, Boolean rewiring,
and the codimension-one first-escape equation.  The result is the exact data
consumed by the target-clean rank-one contradiction.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- A failing rank-one-colour step has normalized high/low factors, unchanged
wire extension, both Boolean absorption identities, and a missing-coset
product equation corrected by one old wire. -/
theorem exists_normalized_rankOne_missing_escape
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hescape : ¬ (andExtend V X Y ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState))
    (g : (ANF 10) ⧸ N4.quadraticANFSpace 10) (hg : g ≠ 0)
    (hpattern : RankOneColourPattern
      (Submodule.mkQ (N4.quadraticANFSpace 10)) g X Y) :
    ∃ (U c : ANF 10) (a : F₂) (ell : LinearForm)
        (u : TargetCoeff) (v : ANF 10),
      U ∈ V ∧ U ∉ N4.quadraticANFSpace 10 ∧
      c ∈ V ∧ c ∈ N4.quadraticANFSpace 10 ∧
      u ∈ firstOrderEnvelopeCoeffSpace ∧ v ∈ V ∧
      andExtend V U c = andExtend V X Y ∧
      U * (U * c) = U * c ∧ (U * c) * c = U * c ∧
      U * c = quadraticCoordinateANF a ell
        (targetTwo (firstOrderMissingCoeff + u)) + v := by
  rcases highQuotient_rankOne_normalize V g X Y hg hX hY hpattern with
    ⟨U, c, hUV, hUhigh, hcV, hcquad, hextend, hleft, hright⟩
  have hescape' : ¬ (andExtend V U c ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState) := by
    rwa [hextend]
  rcases exists_missing_product_equation_of_firstOrder_step_escape
      U c hold hescape' with
    ⟨a, ell, u, v, hu, hv, hequation⟩
  exact ⟨U, c, a, ell, u, v, hUV, hUhigh, hcV, hcquad,
    hu, hv, hextend, hleft, hright, hequation⟩

end
end N5
end UnrestrictedBooleanMul
