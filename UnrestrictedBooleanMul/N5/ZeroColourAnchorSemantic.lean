import UnrestrictedBooleanMul.N5.ZeroColourAnchorNormalForm

/-!
# Semantic core of a normalized anchored zero-colour escape

The circuit reduction leaves an equality between two products of quadratic
wires.  This file applies the literal high quotient and the exact quadratic
projection once and for all.  The remaining obstruction is therefore a
finite-dimensional algebraic shadow statement, with no suffix history or
gate count in its interface.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The two possible quadratic plane types after anchored basis change. -/
def IsFirstOrderAnchorPlaneNormalForm
    (d q c : TwoForm) : Prop :=
  ∃ u ∈ firstOrderEnvelopeTwoSpace,
    ∃ v ∈ firstOrderEnvelopeTwoSpace,
      ((q = u ∧ c = v) ∨ (q = u + d ∧ c = v))

/-- The exact high and quadratic data left by a normalized anchored
two-product equation. -/
structure NormalizedAnchorShadowEquation (d : TwoForm) where
  targetCoeff : TargetCoeff
  targetCoeff_mem : targetCoeff ∈ firstOrderEnvelopeCoeffSpace
  correctionTwo : TwoForm
  correctionTwo_mem : correctionTwo ∈ firstOrderAnchorTwoSpace d
  leftConst : F₂
  leftSecondConst : F₂
  rightConst : F₂
  rightSecondConst : F₂
  leftLinear : LinearForm
  leftSecondLinear : LinearForm
  rightLinear : LinearForm
  rightSecondLinear : LinearForm
  leftTwo : TwoForm
  leftSecondTwo : TwoForm
  rightTwo : TwoForm
  rightSecondTwo : TwoForm
  left_normal :
    IsFirstOrderAnchorPlaneNormalForm d leftTwo leftSecondTwo
  right_normal :
    IsFirstOrderAnchorPlaneNormalForm d rightTwo rightSecondTwo
  high_eq :
    lowProductHighClass leftLinear leftSecondLinear
        leftTwo leftSecondTwo =
      lowProductHighClass rightLinear rightSecondLinear
        rightTwo rightSecondTwo
  shadow_eq :
    lowProductQuadraticShadow leftConst leftSecondConst
        leftLinear leftSecondLinear leftTwo leftSecondTwo =
      targetTwo (firstOrderMissingCoeff + targetCoeff) +
        (lowProductQuadraticShadow rightConst rightSecondConst
          rightLinear rightSecondLinear rightTwo rightSecondTwo +
            correctionTwo)

private theorem wireNormalForm_to_planeNormalForm
    (d : TwoForm) (X Y : ANF 10)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hX : X = quadraticCoordinateANF a ell q)
    (hY : Y = quadraticCoordinateANF b m c)
    (hnormal : IsFirstOrderAnchorWirePairNormalForm d X Y) :
    IsFirstOrderAnchorPlaneNormalForm d q c := by
  simpa [IsFirstOrderAnchorWirePairNormalForm,
    IsFirstOrderAnchorPlaneNormalForm, hX, hY] using hnormal

/-- A normalized circuit equation has exactly the semantic shadow data above.
This is the bridge from the suffix reduction to the remaining local algebra. -/
theorem NormalizedAnchorTwoProductEquation.exists_shadowEquation
    {d : TwoForm} {V : Submodule F₂ (ANF 10)}
    (h : NormalizedAnchorTwoProductEquation d V) :
    Nonempty (NormalizedAnchorShadowEquation d) := by
  have hleftFirstQuad : h.leftFirst ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      (firstOrderAnchorTwoSpace d) h.leftFirst_mem
  have hleftSecondQuad : h.leftSecond ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      (firstOrderAnchorTwoSpace d) h.leftSecond_mem
  have hrightFirstQuad : h.rightFirst ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      (firstOrderAnchorTwoSpace d) h.rightFirst_mem
  have hrightSecondQuad : h.rightSecond ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      (firstOrderAnchorTwoSpace d) h.rightSecond_mem
  have hcorrectionQuad : h.correction ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      (firstOrderAnchorTwoSpace d) h.correction_mem
  rcases exists_quadraticCoordinates hleftFirstQuad with
    ⟨a, ell, q, hleftFirst⟩
  rcases exists_quadraticCoordinates hleftSecondQuad with
    ⟨b, m, c, hleftSecond⟩
  rcases exists_quadraticCoordinates hrightFirstQuad with
    ⟨a', ell', q', hrightFirst⟩
  rcases exists_quadraticCoordinates hrightSecondQuad with
    ⟨b', m', c', hrightSecond⟩
  let correctionTwo := quadraticProjection 10 h.correction
  have hcorrectionTwo : correctionTwo ∈ firstOrderAnchorTwoSpace d := by
    exact ((E2.mem_quadraticEnvelopeState_iff
      (firstOrderAnchorTwoSpace d) h.correction).1 h.correction_mem).2
  have hhigh := congrArg highProjectionTen h.equation
  have htargetQuad : quadraticCoordinateANF h.targetConst h.targetLinear
      (targetTwo (firstOrderMissingCoeff + h.targetCoeff)) ∈
        N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace _ _ _
  have hhighEq :
      lowProductHighClass ell m q c =
        lowProductHighClass ell' m' q' c' := by
    rw [hleftFirst, hleftSecond, hrightFirst, hrightSecond] at hhigh
    rw [map_add, map_add,
      highProjectionTen_eq_zero_of_quadratic htargetQuad,
      highProjectionTen_eq_zero_of_quadratic hcorrectionQuad,
      zero_add, add_zero] at hhigh
    rw [highProjectionTen_quadraticCoordinateANF_mul,
      highProjectionTen_quadraticCoordinateANF_mul] at hhigh
    exact hhigh
  have hshadow := congrArg (quadraticProjection 10) h.equation
  have hshadowEq :
      lowProductQuadraticShadow a b ell m q c =
        targetTwo (firstOrderMissingCoeff + h.targetCoeff) +
          (lowProductQuadraticShadow a' b' ell' m' q' c' +
            correctionTwo) := by
    rw [hleftFirst, hleftSecond, hrightFirst, hrightSecond] at hshadow
    rw [map_add, map_add, quadraticProjection_quadraticCoordinateANF] at hshadow
    rw [quadraticProjection_quadraticCoordinateANF_mul,
      quadraticProjection_quadraticCoordinateANF_mul] at hshadow
    exact hshadow
  exact ⟨{
    targetCoeff := h.targetCoeff
    targetCoeff_mem := h.targetCoeff_mem
    correctionTwo := correctionTwo
    correctionTwo_mem := hcorrectionTwo
    leftConst := a
    leftSecondConst := b
    rightConst := a'
    rightSecondConst := b'
    leftLinear := ell
    leftSecondLinear := m
    rightLinear := ell'
    rightSecondLinear := m'
    leftTwo := q
    leftSecondTwo := c
    rightTwo := q'
    rightSecondTwo := c'
    left_normal := wireNormalForm_to_planeNormalForm
      d h.leftFirst h.leftSecond a b ell m q c
        hleftFirst hleftSecond h.left_normal
    right_normal := wireNormalForm_to_planeNormalForm
      d h.rightFirst h.rightSecond a' b' ell' m' q' c'
        hrightFirst hrightSecond h.right_normal
    high_eq := hhighEq
    shadow_eq := hshadowEq
  }⟩

/-- The circuit-facing consequence: every fixed-anchor zero-colour escape
produces the finite-dimensional normalized shadow obstruction. -/
theorem exists_normalizedAnchorShadowEquation_of_zeroColour_escape
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
    Nonempty (NormalizedAnchorShadowEquation d) := by
  rcases exists_normalized_anchor_twoProduct_equation_of_zeroColour_escape
      d V X Y hreach hquad hhigh hX hY hXquad hYquad hold hescape with ⟨h⟩
  exact h.exists_shadowEquation

end
end N5
end UnrestrictedBooleanMul
