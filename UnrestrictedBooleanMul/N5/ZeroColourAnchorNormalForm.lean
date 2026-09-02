import UnrestrictedBooleanMul.N5.FirstOrderAnchorAlgebra
import UnrestrictedBooleanMul.N5.ZeroColourEscapeReduction

/-!
# Normal form for an anchored zero-colour escape

In the fixed-quadratic, one-high regime, a zero-colour escape is already a
collision of two old low products.  Applying the exact Boolean basis-change
normalization to both factor pairs leaves only two quadratic plane types:
`(u,v)` and `(u+d,v)`, with `u,v` in the first-order envelope.  All product
changes are absorbed into the old anchored correction.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/- A small intermediate record prevents the two independent basis changes
from being elaborated inside the final circuit-facing construction. -/
private structure AnchorWirePairNormalization
    (d : TwoForm) (X Y : ANF 10) where
  first : ANF 10
  second : ANF 10
  delta : ANF 10
  first_mem : first ∈ firstOrderAnchorState d
  second_mem : second ∈ firstOrderAnchorState d
  delta_mem : delta ∈ firstOrderAnchorState d
  normal : IsFirstOrderAnchorWirePairNormalForm d first second
  product_eq : first * second = X * Y + delta

private theorem exists_anchorWirePairNormalization
    (d : TwoForm) (X Y : ANF 10)
    (hX : X ∈ firstOrderAnchorState d)
    (hY : Y ∈ firstOrderAnchorState d) :
    Nonempty (AnchorWirePairNormalization d X Y) := by
  rcases exists_basisChange_isFirstOrderAnchorWirePairNormalForm
      d X Y hX hY with ⟨g, hfirst, hsecond, hdelta, hnormal⟩
  let first := (g.basisPair X Y).1
  let second := (g.basisPair X Y).2
  let delta := first * second + X * Y
  refine ⟨{
    first := first
    second := second
    delta := delta
    first_mem := by simpa only [first] using hfirst
    second_mem := by simpa only [second] using hsecond
    delta_mem := by simpa only [first, second, delta] using hdelta
    normal := by simpa only [first, second] using hnormal
    product_eq := ?_
  }⟩
  simp only [delta]
  calc
    first * second = first * second + 0 := by rw [add_zero]
    _ = first * second + (X * Y + X * Y) := by rw [anf_add_self]
    _ = X * Y + (first * second + X * Y) := by ac_rfl

/-- Data of the normalized collision left by a fixed-anchor zero-colour
escape.  A structure keeps the circuit interface inexpensive to elaborate. -/
structure NormalizedAnchorTwoProductEquation
    (d : TwoForm) (V : Submodule F₂ (ANF 10)) where
  targetConst : F₂
  targetLinear : LinearForm
  targetCoeff : TargetCoeff
  leftFirst : ANF 10
  leftSecond : ANF 10
  rightFirst : ANF 10
  rightSecond : ANF 10
  correction : ANF 10
  targetCoeff_mem : targetCoeff ∈ firstOrderEnvelopeCoeffSpace
  leftFirst_mem : leftFirst ∈ firstOrderAnchorState d
  leftSecond_mem : leftSecond ∈ firstOrderAnchorState d
  rightFirst_mem : rightFirst ∈ firstOrderAnchorState d
  rightSecond_mem : rightSecond ∈ firstOrderAnchorState d
  correction_mem : correction ∈ firstOrderAnchorState d
  rightProduct_mem : rightFirst * rightSecond ∈ V
  left_normal : IsFirstOrderAnchorWirePairNormalForm d leftFirst leftSecond
  right_normal : IsFirstOrderAnchorWirePairNormalForm d rightFirst rightSecond
  equation : leftFirst * leftSecond =
    quadraticCoordinateANF targetConst targetLinear
      (targetTwo (firstOrderMissingCoeff + targetCoeff)) +
        (rightFirst * rightSecond + correction)

private theorem normalizedAnchorTwoProductEquation_of_base
    (d : TwoForm) (V : Submodule F₂ (ANF 10))
    (a : F₂) (ell : LinearForm) (u : TargetCoeff)
    (X Y P Q w : ANF 10)
    (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hXA : X ∈ firstOrderAnchorState d)
    (hYA : Y ∈ firstOrderAnchorState d)
    (hPA : P ∈ firstOrderAnchorState d)
    (hQA : Q ∈ firstOrderAnchorState d)
    (hwA : w ∈ firstOrderAnchorState d)
    (hPQV : P * Q ∈ V)
    (hstart : firstOrderAnchorState d ≤ V)
    (heq : X * Y = quadraticCoordinateANF a ell
      (targetTwo (firstOrderMissingCoeff + u)) + (P * Q + w)) :
    Nonempty (NormalizedAnchorTwoProductEquation d V) := by
  rcases exists_anchorWirePairNormalization d X Y hXA hYA with ⟨left⟩
  rcases exists_anchorWirePairNormalization d P Q hPA hQA with ⟨right⟩
  let correction := w + left.delta + right.delta
  have hcorrection : correction ∈ firstOrderAnchorState d :=
    (firstOrderAnchorState d).add_mem
      ((firstOrderAnchorState d).add_mem hwA left.delta_mem) right.delta_mem
  have hrightProduct : right.first * right.second ∈ V := by
    rw [right.product_eq]
    exact V.add_mem hPQV (hstart right.delta_mem)
  refine ⟨{
    targetConst := a
    targetLinear := ell
    targetCoeff := u
    leftFirst := left.first
    leftSecond := left.second
    rightFirst := right.first
    rightSecond := right.second
    correction := correction
    targetCoeff_mem := hu
    leftFirst_mem := left.first_mem
    leftSecond_mem := left.second_mem
    rightFirst_mem := right.first_mem
    rightSecond_mem := right.second_mem
    correction_mem := hcorrection
    rightProduct_mem := hrightProduct
    left_normal := left.normal
    right_normal := right.normal
    equation := ?_
  }⟩
  rw [left.product_eq, heq, right.product_eq]
  simp only [correction]
  calc
    _ = quadraticCoordinateANF a ell
        (targetTwo (firstOrderMissingCoeff + u)) +
          (P * Q + w + left.delta) := by ac_rfl
    _ = quadraticCoordinateANF a ell
        (targetTwo (firstOrderMissingCoeff + u)) +
          (P * Q + w + left.delta + (right.delta + right.delta)) := by
      rw [anf_add_self, add_zero]
    _ = _ := by ac_rfl

/-- Fixed-anchor zero-colour escapes reduce to a collision of two normalized
anchored products.  This is the circuit-facing normal form consumed by the
remaining target-clean localization. -/
theorem exists_normalized_anchor_twoProduct_equation_of_zeroColour_escape
    (d : TwoForm) (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hreach : DefectLegalSuffix (firstOrderAnchorState d) V)
    (hquad : stateQuadraticPart V = firstOrderAnchorState d)
    (hhigh : stateHighRank V ≤ 1)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hXquad : X ∈ N4.quadraticANFSpace 10)
    (hYquad : Y ∈ N4.quadraticANFSpace 10)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hescape : ¬ (andExtend V X Y ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState)) :
    Nonempty (NormalizedAnchorTwoProductEquation d V) := by
  rcases exists_base_twoProduct_equation_of_zeroColour_escape
      X Y hreach
      (E2.quadraticEnvelopeState_le_quadraticANFSpace
        (firstOrderAnchorTwoSpace d))
      hquad hhigh hX hY hXquad hYquad hold hescape with
    ⟨a, ell, u, P, Q, w, hu, hXA, hYA, hPA, hQA, hwA, hPQV, heq⟩
  exact normalizedAnchorTwoProductEquation_of_base d V a ell u X Y P Q w
    hu hXA hYA hPA hQA hwA hPQV hreach.start_le heq

end
end N5
end UnrestrictedBooleanMul
