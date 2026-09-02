import UnrestrictedBooleanMul.N5.ZeroColourAnchorNormalForm
import UnrestrictedBooleanMul.N5.EnvelopeSemanticExact
import UnrestrictedBooleanMul.N5.RationalEnvelopeSymmetry

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

theorem IsFirstOrderAnchorPlaneNormalForm.members_of_anchor_mem
    {d q c : TwoForm} (h : IsFirstOrderAnchorPlaneNormalForm d q c)
    (hd : d ∈ firstOrderEnvelopeTwoSpace) :
    q ∈ firstOrderEnvelopeTwoSpace ∧ c ∈ firstOrderEnvelopeTwoSpace := by
  rcases h with ⟨u, hu, v, hv, hnormal | hnormal⟩
  · exact ⟨hnormal.1 ▸ hu, hnormal.2 ▸ hv⟩
  · exact ⟨hnormal.1 ▸ firstOrderEnvelopeTwoSpace.add_mem hu hd,
      hnormal.2 ▸ hv⟩

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

/-- Exact algebraic interface of the decomposable-defect clause in the
manuscript's envelope-shadow lemma.  It states that equal complete high
parts over the two normalized anchored plane types have total Boolean
quadratic shadow in the target-clean second jet plus the anchor line. -/
def AnchoredEnvelopeShadowLocalizedAt (d : TwoForm) : Prop :=
  ∀ (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm),
    IsFirstOrderAnchorPlaneNormalForm d q c →
    IsFirstOrderAnchorPlaneNormalForm d q' c' →
    lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c' →
    ∀ (alpha : F₂) (u : TargetCoeff),
      u ∈ firstOrderEnvelopeCoeffSpace →
      lowProductQuadraticShadow a b ell m q c +
            lowProductQuadraticShadow a' b' ell' m' q' c' +
            alpha • d =
          targetTwo (firstOrderMissingCoeff + u) →
        ∃ place : Fin 3,
          lowProductQuadraticShadow a b ell m q c +
              lowProductQuadraticShadow a' b' ell' m' q' c' ∈
            rationalPlaceTargetCleanSecondJetSpace place ⊔
              Submodule.span F₂ ({d} : Set TwoForm)

def AnchoredEnvelopeShadowLocalization : Prop :=
  ∀ (d : TwoForm), IsDecomposableTwo d →
    AnchoredEnvelopeShadowLocalizedAt d

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

/-- Absorb the old anchored correction into the target coefficient and one
Boolean scalar multiple of the anchor.  This leaves the exact eight-case
algebraic obstruction: two normalized plane types and one anchor bit. -/
theorem NormalizedAnchorShadowEquation.exists_reducedEquation
    {d : TwoForm} (h : NormalizedAnchorShadowEquation d) :
    ∃ (alpha : F₂) (u : TargetCoeff),
      u ∈ firstOrderEnvelopeCoeffSpace ∧
      lowProductQuadraticShadow h.leftConst h.leftSecondConst
          h.leftLinear h.leftSecondLinear h.leftTwo h.leftSecondTwo +
          lowProductQuadraticShadow h.rightConst h.rightSecondConst
            h.rightLinear h.rightSecondLinear h.rightTwo h.rightSecondTwo +
          alpha • d =
        targetTwo (firstOrderMissingCoeff + u) := by
  rcases Submodule.mem_sup.mp h.correctionTwo_mem with
    ⟨old, hold, anchor, hanchor, hcorrection⟩
  rcases hold with ⟨oldCoeff, holdCoeff, holdEq⟩
  rcases Submodule.mem_span_singleton.mp hanchor with ⟨alpha, rfl⟩
  refine ⟨alpha, h.targetCoeff + oldCoeff,
    firstOrderEnvelopeCoeffSpace.add_mem h.targetCoeff_mem holdCoeff, ?_⟩
  rw [h.shadow_eq, ← hcorrection, ← holdEq]
  calc
    (targetTwo (firstOrderMissingCoeff + h.targetCoeff) +
          (lowProductQuadraticShadow h.rightConst h.rightSecondConst
            h.rightLinear h.rightSecondLinear h.rightTwo h.rightSecondTwo +
              (targetTwo oldCoeff + alpha • d))) +
        lowProductQuadraticShadow h.rightConst h.rightSecondConst
          h.rightLinear h.rightSecondLinear h.rightTwo h.rightSecondTwo +
        alpha • d =
      targetTwo (firstOrderMissingCoeff + h.targetCoeff) +
        targetTwo oldCoeff := by
          funext s
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring_nf
          simp only [N3Certificate.two_eq_zero_f2, mul_zero, add_zero]
    _ = targetTwo
        ((firstOrderMissingCoeff + h.targetCoeff) + oldCoeff) := by
      exact (targetTwoLinear.map_add _ _).symm
    _ = targetTwo
        (firstOrderMissingCoeff + (h.targetCoeff + oldCoeff)) := by
      rw [add_assoc]

private theorem twoForm_recover_after_duplicate
    (x y : TwoForm) : x = (x + y) + y := by
  funext s
  change x s = (x s + y s) + y s
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- If the optional anchor was already in the first-order envelope, the
localized statement is vacuous: the exact envelope-shadow theorem excludes
the target-capable comparison itself.  This removes the zero-defect anchor
case before the genuinely external decomposable-anchor calculation. -/
theorem anchoredEnvelopeShadowLocalizedAt_of_mem_envelope
    (d : TwoForm) (hd : d ∈ firstOrderEnvelopeTwoSpace) :
    AnchoredEnvelopeShadowLocalizedAt d := by
  intro a b a' b' ell m ell' m' q c q' c'
    hleft hright hhigh alpha u hu heq
  have hleftMem := hleft.members_of_anchor_mem hd
  have hrightMem := hright.members_of_anchor_mem hd
  rcases hd with ⟨dCoeff, hdCoeff, hdEq⟩
  have hu' : u + alpha • dCoeff ∈ firstOrderEnvelopeCoeffSpace :=
    firstOrderEnvelopeCoeffSpace.add_mem hu
      (firstOrderEnvelopeCoeffSpace.smul_mem alpha hdCoeff)
  have hforbidden := semanticEnvelope_exact_shadow
    a b a' b' ell m ell' m' q c q' c'
    hleftMem.1 hleftMem.2 hrightMem.1 hrightMem.2 hhigh
    (u + alpha • dCoeff) hu'
  exfalso
  apply hforbidden
  calc
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' =
      (lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q' c' +
          alpha • d) + alpha • d :=
      twoForm_recover_after_duplicate _ _
    _ = targetTwo (firstOrderMissingCoeff + u) + alpha • d := by
      rw [heq]
    _ = targetTwo (firstOrderMissingCoeff + u) +
        alpha • targetTwo dCoeff := by
      exact congrArg
        (fun z : TwoForm => targetTwo (firstOrderMissingCoeff + u) + alpha • z)
        hdEq.symm
    _ = targetTwo (firstOrderMissingCoeff + u) +
        targetTwo (alpha • dCoeff) := by
      exact congrArg
        (fun z : TwoForm => targetTwo (firstOrderMissingCoeff + u) + z)
        (targetTwoLinear.map_smul alpha dCoeff).symm
    _ = targetTwo
        ((firstOrderMissingCoeff + u) + alpha • dCoeff) := by
      exact (targetTwoLinear.map_add _ _).symm
    _ = targetTwo
        (firstOrderMissingCoeff + (u + alpha • dCoeff)) := by
      rw [add_assoc]

/-- The only remaining part of the anchored envelope-shadow statement is
the genuinely external decomposable anchor. -/
def ExternalAnchoredEnvelopeShadowLocalization : Prop :=
  ∀ (d : TwoForm), IsDecomposableTwo d →
    d ∉ firstOrderEnvelopeTwoSpace →
    AnchoredEnvelopeShadowLocalizedAt d

theorem anchoredEnvelopeShadowLocalization_of_external
    (hexternal : ExternalAnchoredEnvelopeShadowLocalization) :
    AnchoredEnvelopeShadowLocalization := by
  intro d hddec
  by_cases hd : d ∈ firstOrderEnvelopeTwoSpace
  · exact anchoredEnvelopeShadowLocalizedAt_of_mem_envelope d hd
  · exact hexternal d hddec hd

/-- The reduced obstruction is impossible when the anchor was target-valued:
then both normalized planes and the anchor correction all return to the
literal first-order envelope theorem. -/
theorem NormalizedAnchorShadowEquation.false_of_anchor_mem_envelope
    {d : TwoForm} (h : NormalizedAnchorShadowEquation d)
    (hd : d ∈ firstOrderEnvelopeTwoSpace) : False := by
  rcases hd with ⟨dCoeff, hdCoeff, hdEq⟩
  have hleft := h.left_normal.members_of_anchor_mem
    (show d ∈ firstOrderEnvelopeTwoSpace from ⟨dCoeff, hdCoeff, hdEq⟩)
  have hright := h.right_normal.members_of_anchor_mem
    (show d ∈ firstOrderEnvelopeTwoSpace from ⟨dCoeff, hdCoeff, hdEq⟩)
  rcases h.exists_reducedEquation with ⟨alpha, u, hu, heq⟩
  have hforbidden := semanticEnvelope_exact_shadow
    h.leftConst h.leftSecondConst h.rightConst h.rightSecondConst
    h.leftLinear h.leftSecondLinear h.rightLinear h.rightSecondLinear
    h.leftTwo h.leftSecondTwo h.rightTwo h.rightSecondTwo
    hleft.1 hleft.2 hright.1 hright.2 h.high_eq
    (u + alpha • dCoeff)
    (firstOrderEnvelopeCoeffSpace.add_mem hu
      (firstOrderEnvelopeCoeffSpace.smul_mem alpha hdCoeff))
  apply hforbidden
  calc
    lowProductQuadraticShadow h.leftConst h.leftSecondConst
          h.leftLinear h.leftSecondLinear h.leftTwo h.leftSecondTwo +
        lowProductQuadraticShadow h.rightConst h.rightSecondConst
          h.rightLinear h.rightSecondLinear h.rightTwo h.rightSecondTwo =
      (lowProductQuadraticShadow h.leftConst h.leftSecondConst
            h.leftLinear h.leftSecondLinear h.leftTwo h.leftSecondTwo +
          lowProductQuadraticShadow h.rightConst h.rightSecondConst
            h.rightLinear h.rightSecondLinear h.rightTwo h.rightSecondTwo +
          alpha • d) + alpha • d :=
      twoForm_recover_after_duplicate _ _
    _ = targetTwo (firstOrderMissingCoeff + u) + alpha • d := by
      rw [heq]
    _ = targetTwo (firstOrderMissingCoeff + u) +
        alpha • targetTwo dCoeff := by
      exact congrArg
        (fun z : TwoForm => targetTwo (firstOrderMissingCoeff + u) + alpha • z)
        hdEq.symm
    _ = targetTwo (firstOrderMissingCoeff + u) +
        targetTwo (alpha • dCoeff) := by
      exact congrArg
        (fun z : TwoForm => targetTwo (firstOrderMissingCoeff + u) + z)
        (targetTwoLinear.map_smul alpha dCoeff).symm
    _ = targetTwo
        ((firstOrderMissingCoeff + u) + alpha • dCoeff) := by
      exact (targetTwoLinear.map_add _ _).symm
    _ = targetTwo
        (firstOrderMissingCoeff + (u + alpha • dCoeff)) := by
      rw [add_assoc]

/-- Once the anchored envelope-shadow localization is supplied, equation
(11.7) turns every normalized anchored collision into a contradiction. -/
theorem NormalizedAnchorShadowEquation.false_of_localization
    {d : TwoForm} (h : NormalizedAnchorShadowEquation d)
    (hddec : IsDecomposableTwo d)
    (hloc : AnchoredEnvelopeShadowLocalization) : False := by
  rcases h.exists_reducedEquation with ⟨alpha, u, hu, heq⟩
  let shadow :=
    lowProductQuadraticShadow h.leftConst h.leftSecondConst
        h.leftLinear h.leftSecondLinear h.leftTwo h.leftSecondTwo +
      lowProductQuadraticShadow h.rightConst h.rightSecondConst
        h.rightLinear h.rightSecondLinear h.rightTwo h.rightSecondTwo
  rcases hloc d hddec
      h.leftConst h.leftSecondConst h.rightConst h.rightSecondConst
      h.leftLinear h.leftSecondLinear h.rightLinear h.rightSecondLinear
      h.leftTwo h.leftSecondTwo h.rightTwo h.rightSecondTwo
      h.left_normal h.right_normal h.high_eq alpha u hu heq with
    ⟨place, hshadow⟩
  have hanchor : alpha • d ∈
      Submodule.span F₂ ({d} : Set TwoForm) :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  have htargetClean : targetTwo (firstOrderMissingCoeff + u) ∈
      rationalPlaceTargetCleanSecondJetSpace place ⊔
        Submodule.span F₂ ({d} : Set TwoForm) := by
    rw [← heq]
    exact (rationalPlaceTargetCleanSecondJetSpace place ⊔
      Submodule.span F₂ ({d} : Set TwoForm)).add_mem hshadow
        (Submodule.mem_sup_right hanchor)
  have htarget : targetTwo (firstOrderMissingCoeff + u) ∈ targetTwoSpace :=
    ⟨firstOrderMissingCoeff + u, rfl⟩
  have hfirst : targetTwo (firstOrderMissingCoeff + u) ∈
      firstOrderEnvelopeTwoSpace := by
    have hinter : targetTwo (firstOrderMissingCoeff + u) ∈
        targetTwoSpace ⊓
          (rationalPlaceTargetCleanSecondJetSpace place ⊔
            Submodule.span F₂ ({d} : Set TwoForm)) :=
      ⟨htarget, htargetClean⟩
    rw [targetTwoSpace_inf_rationalPlaceTargetClean_sup_decomposable
      place d hddec] at hinter
    exact hinter
  exact missingCoset_targetTwo_not_mem_firstOrderAnchor
    d hddec u hu (Submodule.mem_sup_left hfirst)

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

/-- Circuit-facing fixed-anchor zero-colour closure obtained from the single
algebraic localization interface above. -/
theorem zeroColour_step_closed_of_fixedAnchor_highRank_le_one_of_localization
    (hloc : AnchoredEnvelopeShadowLocalization)
    (d : TwoForm) (hddec : IsDecomposableTwo d)
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hreach : DefectLegalSuffix (firstOrderAnchorState d) V)
    (hquad : stateQuadraticPart V = firstOrderAnchorState d)
    (hhigh : stateHighRank V ≤ 1)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hXquad : X ∈ N4.quadraticANFSpace 10)
    (hYquad : Y ∈ N4.quadraticANFSpace 10)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState) :
    andExtend V X Y ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState := by
  by_contra hescape
  rcases exists_normalizedAnchorShadowEquation_of_zeroColour_escape
      d V X Y hreach hquad hhigh hX hY hXquad hYquad hold hescape with ⟨h⟩
  exact h.false_of_localization hddec hloc

end
end N5
end UnrestrictedBooleanMul
