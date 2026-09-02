import UnrestrictedBooleanMul.N5.ZeroColourAnchorNormalForm
import UnrestrictedBooleanMul.N5.EnvelopeSemanticExact
import UnrestrictedBooleanMul.N5.RationalEnvelopeSymmetry
import UnrestrictedBooleanMul.N5.Displacement

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

/-- Scalar-bit form of the anchored plane normal form.  It replaces the
disjunction by the coefficient of the unique external anchor direction. -/
theorem IsFirstOrderAnchorPlaneNormalForm.exists_anchorBit
    {d q c : TwoForm} (h : IsFirstOrderAnchorPlaneNormalForm d q c) :
    ∃ u ∈ firstOrderEnvelopeTwoSpace,
      ∃ v ∈ firstOrderEnvelopeTwoSpace,
        ∃ epsilon : F₂, q = u + epsilon • d ∧ c = v := by
  rcases h with ⟨u, hu, v, hv, hnormal | hnormal⟩
  · exact ⟨u, hu, v, hv, 0, by simpa using hnormal.1, hnormal.2⟩
  · exact ⟨u, hu, v, hv, 1, by simpa using hnormal.1, hnormal.2⟩

/-- Conversely, a scalar anchor coefficient over `F₂` is one of the two
normalized anchored plane types. -/
theorem isFirstOrderAnchorPlaneNormalForm_of_anchorBit
    (d u v : TwoForm) (epsilon : F₂)
    (hu : u ∈ firstOrderEnvelopeTwoSpace)
    (hv : v ∈ firstOrderEnvelopeTwoSpace) :
    IsFirstOrderAnchorPlaneNormalForm d (u + epsilon • d) v := by
  refine ⟨u, hu, v, hv, ?_⟩
  rcases f2_eq_zero_or_one epsilon with rfl | rfl
  · left
    simp
  · right
    simp

/-- Exact high-part expansion of one normalized anchored factor plane. -/
theorem IsFirstOrderAnchorPlaneNormalForm.exists_highExpansion
    {d q c : TwoForm} (h : IsFirstOrderAnchorPlaneNormalForm d q c)
    (ell m : LinearForm) :
    ∃ u ∈ firstOrderEnvelopeTwoSpace,
      ∃ v ∈ firstOrderEnvelopeTwoSpace,
        ∃ epsilon : F₂,
          q = u + epsilon • d ∧ c = v ∧
          lowProductHighClass ell m q c =
            lowProductHighClass ell m u v +
              epsilon • lowProductHighClass 0 m d v := by
  rcases h.exists_anchorBit with ⟨u, hu, v, hv, epsilon, hq, hc⟩
  refine ⟨u, hu, v, hv, epsilon, hq, hc, ?_⟩
  rw [hq, hc]
  simpa using
    lowProductHighClass_add_smul_anchor ell m u v d epsilon 0

/-- Exact Boolean quadratic-shadow expansion of one normalized anchored
factor plane.  All dependence on the external anchor is explicit. -/
theorem IsFirstOrderAnchorPlaneNormalForm.exists_shadowExpansion
    {d q c : TwoForm} (h : IsFirstOrderAnchorPlaneNormalForm d q c)
    (a b : F₂) (ell m : LinearForm) :
    ∃ u ∈ firstOrderEnvelopeTwoSpace,
      ∃ v ∈ firstOrderEnvelopeTwoSpace,
        ∃ epsilon : F₂,
          q = u + epsilon • d ∧ c = v ∧
          lowProductQuadraticShadow a b ell m q c =
            lowProductQuadraticShadow a b ell m u v +
              (b * epsilon) • d +
              epsilon • ambientBooleanContraction m d +
              epsilon • ambientTwoHadamard d v := by
  rcases h.exists_anchorBit with ⟨u, hu, v, hv, epsilon, hq, hc⟩
  refine ⟨u, hu, v, hv, epsilon, hq, hc, ?_⟩
  rw [hq, hc]
  simpa using
    lowProductQuadraticShadow_add_smul_anchor
      a b ell m u v d epsilon 0

theorem IsFirstOrderAnchorPlaneNormalForm.members_of_anchor_mem
    {d q c : TwoForm} (h : IsFirstOrderAnchorPlaneNormalForm d q c)
    (hd : d ∈ firstOrderEnvelopeTwoSpace) :
    q ∈ firstOrderEnvelopeTwoSpace ∧ c ∈ firstOrderEnvelopeTwoSpace := by
  rcases h with ⟨u, hu, v, hv, hnormal | hnormal⟩
  · exact ⟨hnormal.1 ▸ hu, hnormal.2 ▸ hv⟩
  · exact ⟨hnormal.1 ▸ firstOrderEnvelopeTwoSpace.add_mem hu hd,
      hnormal.2 ▸ hv⟩

/-- Both directions of a normalized anchored plane lie in the canonical
one-anchor quadratic space. -/
theorem IsFirstOrderAnchorPlaneNormalForm.members_anchorSpace
    {d q c : TwoForm} (h : IsFirstOrderAnchorPlaneNormalForm d q c) :
    q ∈ firstOrderAnchorTwoSpace d ∧
      c ∈ firstOrderAnchorTwoSpace d := by
  rcases h.exists_anchorBit with ⟨u, hu, v, hv, epsilon, hq, hc⟩
  constructor
  · rw [hq]
    exact (firstOrderAnchorTwoSpace d).add_mem
      (Submodule.mem_sup_left hu)
      (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)))
  · rw [hc]
    exact Submodule.mem_sup_left hv

/-- The canonical one-anchor quadratic space is contained in every rational
target-clean second-jet enlargement with that same anchor adjoined. -/
theorem firstOrderAnchorTwoSpace_le_rationalPlaceTargetClean_sup_anchor
    (place : Fin 3) (d : TwoForm) :
    firstOrderAnchorTwoSpace d ≤
      rationalPlaceTargetCleanSecondJetSpace place ⊔
        Submodule.span F₂ ({d} : Set TwoForm) := by
  exact sup_le_sup
    (firstOrderEnvelopeTwoSpace_le_rationalPlaceTargetClean place)
    (le_refl _)

/-- Any ordered basis change of a normalized anchored factor plane changes
its Boolean quadratic shadow only inside every rational clean space with the
anchor adjoined. -/
theorem normalizedAnchorPlane_basisChange_shadow_localized
    (place : Fin 3) (d : TwoForm) (g : PlaneBasisChange)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hnormal : IsFirstOrderAnchorPlaneNormalForm d q c) :
    changedLowProductQuadraticShadow g a b ell m q c +
        lowProductQuadraticShadow a b ell m q c ∈
      rationalPlaceTargetCleanSecondJetSpace place ⊔
        Submodule.span F₂ ({d} : Set TwoForm) := by
  have hmem := hnormal.members_anchorSpace
  exact firstOrderAnchorTwoSpace_le_rationalPlaceTargetClean_sup_anchor
    place d
    (planeBasisChange_high_and_shadow_mod_submodule
      (firstOrderAnchorTwoSpace d) g a b ell m q c hmem.1 hmem.2).2

/-- Generic equal-plane branch of anchored shadow localization.  If the
common intrinsic plane is cubic-rigid, literal high-class equality forces
the total quadratic shadow into the one-anchor space, hence into every
rational target-clean enlargement with that anchor. -/
theorem sameSpanCubicRigidAnchorPlane_shadow_localized
    (place : Fin 3) (d : TwoForm)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hnormal : IsFirstOrderAnchorPlaneNormalForm d q c)
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hspan : Submodule.span F₂ ({q', c'} : Set TwoForm) =
      Submodule.span F₂ ({q, c} : Set TwoForm))
    (hrigid : CubicRigidPlane q c)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c') :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ∈
      rationalPlaceTargetCleanSecondJetSpace place ⊔
        Submodule.span F₂ ({d} : Set TwoForm) := by
  rcases exists_planeBasisChange_of_span_eq
      q c q' c' hind' hspan with ⟨g, hq', hc'⟩
  have hoverlap : quadraticOverlapCubic q c =
      quadraticOverlapCubic q' c' := by
    rw [hq', hc']
    exact (quadraticOverlapCubic_basisPair g q c).symm
  have hcomplete : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c' :=
    lowProductHighPart_eq_of_highClass_eq_of_overlap_eq
      ell m ell' m' q c q' c' hhigh hoverlap
  have hmem := hnormal.members_anchorSpace
  have hshadow :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q' c' ∈
        firstOrderAnchorTwoSpace d :=
    sharedCubicRigidPlane_shadow_mem_submodule
      (firstOrderAnchorTwoSpace d)
      a b a' b' ell m ell' m' q c q' c' g
      hmem.1 hmem.2 hq' hc' hrigid hcomplete
  exact firstOrderAnchorTwoSpace_le_rationalPlaceTargetClean_sup_anchor
    place d hshadow

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

/-- Every target-capable normalized comparison really uses the anchor: in
the scalar normal form, at least one of the two factor-plane bits or the
quadratic correction bit is nonzero.  The all-zero branch is exactly the
already-checked first-order envelope shadow exclusion. -/
theorem NormalizedAnchorShadowEquation.exists_activeAnchorBits
    {d : TwoForm} (h : NormalizedAnchorShadowEquation d) :
    ∃ (q₀ c₀ q₁ c₁ : TwoForm) (ε₀ ε₁ alpha : F₂)
        (u : TargetCoeff),
      q₀ ∈ firstOrderEnvelopeTwoSpace ∧
      c₀ ∈ firstOrderEnvelopeTwoSpace ∧
      q₁ ∈ firstOrderEnvelopeTwoSpace ∧
      c₁ ∈ firstOrderEnvelopeTwoSpace ∧
      u ∈ firstOrderEnvelopeCoeffSpace ∧
      h.leftTwo = q₀ + ε₀ • d ∧ h.leftSecondTwo = c₀ ∧
      h.rightTwo = q₁ + ε₁ • d ∧ h.rightSecondTwo = c₁ ∧
      lowProductQuadraticShadow h.leftConst h.leftSecondConst
            h.leftLinear h.leftSecondLinear h.leftTwo h.leftSecondTwo +
          lowProductQuadraticShadow h.rightConst h.rightSecondConst
            h.rightLinear h.rightSecondLinear h.rightTwo h.rightSecondTwo +
          alpha • d =
        targetTwo (firstOrderMissingCoeff + u) ∧
      (ε₀ ≠ 0 ∨ ε₁ ≠ 0 ∨ alpha ≠ 0) := by
  rcases h.left_normal.exists_anchorBit with
    ⟨q₀, hq₀, c₀, hc₀, ε₀, hleftQ, hleftC⟩
  rcases h.right_normal.exists_anchorBit with
    ⟨q₁, hq₁, c₁, hc₁, ε₁, hrightQ, hrightC⟩
  rcases h.exists_reducedEquation with ⟨alpha, u, hu, heq⟩
  refine ⟨q₀, c₀, q₁, c₁, ε₀, ε₁, alpha, u,
    hq₀, hc₀, hq₁, hc₁, hu,
    hleftQ, hleftC, hrightQ, hrightC, heq, ?_⟩
  by_contra hnone
  have hε₀ : ε₀ = 0 := by
    by_contra hne
    exact hnone (Or.inl hne)
  have hε₁ : ε₁ = 0 := by
    by_contra hne
    exact hnone (Or.inr (Or.inl hne))
  have halpha : alpha = 0 := by
    by_contra hne
    exact hnone (Or.inr (Or.inr hne))
  have hforbidden := semanticEnvelope_exact_shadow
    h.leftConst h.leftSecondConst h.rightConst h.rightSecondConst
    h.leftLinear h.leftSecondLinear h.rightLinear h.rightSecondLinear
    q₀ c₀ q₁ c₁ hq₀ hc₀ hq₁ hc₁ (by
      simpa [hleftQ, hleftC, hrightQ, hrightC, hε₀, hε₁] using
        h.high_eq) u hu
  apply hforbidden
  simpa [hleftQ, hleftC, hrightQ, hrightC, hε₀, hε₁, halpha]
    using heq

/-- A genuinely external decomposable anchor cannot itself be target-valued.
All decomposable target points already lie in the first-order envelope. -/
theorem externalDecomposableAnchor_not_mem_targetTwoSpace
    {d : TwoForm} (hddec : IsDecomposableTwo d)
    (hdU : d ∉ firstOrderEnvelopeTwoSpace) :
    d ∉ targetTwoSpace := by
  intro hdT
  apply hdU
  have hdInf : d ∈ targetTwoSpace ⊓ firstOrderAnchorTwoSpace d :=
    ⟨hdT, Submodule.mem_sup_right
      (Submodule.mem_span_singleton_self d)⟩
  rwa [targetTwoSpace_inf_firstOrderAnchorTwoSpace d hddec] at hdInf

/-- Hence the quadratic quotient class of an external decomposable anchor
is nonzero. -/
theorem externalDecomposableAnchor_quotient_ne_zero
    {d : TwoForm} (hddec : IsDecomposableTwo d)
    (hdU : d ∉ firstOrderEnvelopeTwoSpace) :
    quadraticQuotientProjection d ≠ 0 := by
  intro hzero
  exact externalDecomposableAnchor_not_mem_targetTwoSpace hddec hdU
    ((quadraticQuotientProjection_eq_zero_iff d).1 hzero)

/-- If a second decomposable form is obtained by translating a decomposable
anchor by an old-envelope direction, then the translating target word is
either rational or the common quotient fiber is one of the effective fibers
classified by the closed-place atlas. -/
theorem decomposableEnvelopeTranslate_rational_or_effective
    (d p old : TwoForm)
    (hd : IsDecomposableTwo d) (hp : IsDecomposableTwo p)
    (hold : old ∈ firstOrderEnvelopeTwoSpace)
    (htranslate : p = old + d) :
    ∃ c : TargetCoeff,
      c ∈ firstOrderEnvelopeCoeffSpace ∧ old = targetTwo c ∧
      (c ∈ rationalCoeffSpace ∨
        IsEffectiveFiber (quadraticQuotientProjection d)) := by
  rcases hold with ⟨c, hc, hold⟩
  change targetTwo c = old at hold
  refine ⟨c, hc, hold.symm, ?_⟩
  by_cases hrat : c ∈ rationalCoeffSpace
  · exact Or.inl hrat
  · right
    apply isEffectiveFiber_of_decomposable_target_translate d p c hd hp hrat
    calc
      p = old + d := htranslate
      _ = targetTwo c + d := by rw [← hold]
      _ = d + targetTwo c := add_comm _ _

/-- Closed-place refinement of the decomposable-translate split.  In the
non-rational branch the common quotient class is represented by one of the
four effective closed-place charts, so later shadow arguments may separate
the three rational places from the degree-two place without reopening the
global fiber classification. -/
theorem decomposableEnvelopeTranslate_rational_or_closedPlace
    (d p old : TwoForm)
    (hd : IsDecomposableTwo d) (hp : IsDecomposableTwo p)
    (hold : old ∈ firstOrderEnvelopeTwoSpace)
    (htranslate : p = old + d) :
    ∃ c : TargetCoeff,
      c ∈ firstOrderEnvelopeCoeffSpace ∧ old = targetTwo c ∧
      (c ∈ rationalCoeffSpace ∨
        ∃ x : ClosedPlaceEffectiveParam,
          quadraticQuotientProjection d = closedPlaceEffectivePoint x) := by
  rcases decomposableEnvelopeTranslate_rational_or_effective
      d p old hd hp hold htranslate with ⟨c, hc, holdEq, hcase⟩
  refine ⟨c, hc, holdEq, ?_⟩
  rcases hcase with hrat | heffective
  · exact Or.inl hrat
  · exact Or.inr
      (exists_closedPlaceEffectiveParam_of_effectiveFiber heffective)

/-- Once the quotient place is known, the translating old-envelope target
word lies in the intrinsic displacement space of that fiber, hence in the
rational directions plus the target plane of the same closed place. -/
theorem decomposableEnvelopeTranslate_mem_closedPlaceDisplacement
    (x : ClosedPlaceEffectiveParam) (d p old : TwoForm)
    (hd : IsDecomposableTwo d) (hp : IsDecomposableTwo p)
    (hold : old ∈ firstOrderEnvelopeTwoSpace)
    (htranslate : p = old + d)
    (hplace : quadraticQuotientProjection d =
      closedPlaceEffectivePoint x) :
    old ∈ rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1 := by
  have holdTarget : old ∈ targetTwoSpace :=
    firstOrderEnvelopeTwoSpace_le_targetTwoSpace hold
  have holdProjection : quadraticQuotientProjection old = 0 :=
    (quadraticQuotientProjection_eq_zero_iff old).2 holdTarget
  have hdFiber : d ∈ decomposableFiber (closedPlaceEffectivePoint x) :=
    ⟨hd, hplace⟩
  have hpProjection : quadraticQuotientProjection p =
      closedPlaceEffectivePoint x := by
    calc
      quadraticQuotientProjection p =
          quadraticQuotientProjection (old + d) := by rw [htranslate]
      _ = quadraticQuotientProjection old +
          quadraticQuotientProjection d := map_add _ _ _
      _ = 0 + closedPlaceEffectivePoint x := by
        rw [holdProjection, hplace]
      _ = closedPlaceEffectivePoint x := zero_add _
  have hpFiber : p ∈ decomposableFiber (closedPlaceEffectivePoint x) :=
    ⟨hp, hpProjection⟩
  have hdifference : p - d ∈
      fiberDifferenceSpace (closedPlaceEffectivePoint x) d :=
    Submodule.subset_span ⟨p, hpFiber, rfl⟩
  have hlocal := fiberDifferenceSpace_closedPlace_le x hdFiber hdifference
  have holdEq : old = p - d := by
    rw [htranslate]
    module
  rwa [holdEq]

/-- Final translate interface used by the anchored shadow calculation.  A
decomposable anchor translate is either rational already, or comes with an
explicit effective closed place and a proof that its target displacement is
supported by that place together with the rational directions. -/
theorem decomposableEnvelopeTranslate_rational_or_localDisplacement
    (d p old : TwoForm)
    (hd : IsDecomposableTwo d) (hp : IsDecomposableTwo p)
    (hold : old ∈ firstOrderEnvelopeTwoSpace)
    (htranslate : p = old + d) :
    ∃ c : TargetCoeff,
      c ∈ firstOrderEnvelopeCoeffSpace ∧ old = targetTwo c ∧
      (c ∈ rationalCoeffSpace ∨
        ∃ x : ClosedPlaceEffectiveParam,
          quadraticQuotientProjection d = closedPlaceEffectivePoint x ∧
          old ∈ rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1) := by
  rcases decomposableEnvelopeTranslate_rational_or_closedPlace
      d p old hd hp hold htranslate with
    ⟨c, hc, holdEq, hrat | ⟨x, hplace⟩⟩
  · exact ⟨c, hc, holdEq, Or.inl hrat⟩
  · exact ⟨c, hc, holdEq, Or.inr ⟨x, hplace,
      decomposableEnvelopeTranslate_mem_closedPlaceDisplacement
        x d p old hd hp hold htranslate hplace⟩⟩

/-- Every rational target direction belongs to the first-order envelope.
This is recorded at coefficient level so later local arguments can reuse the
inclusion without unfolding the two-form maps. -/
theorem rationalCoeffSpace_le_firstOrderEnvelopeCoeffSpace :
    rationalCoeffSpace ≤ firstOrderEnvelopeCoeffSpace := by
  apply Submodule.span_le.mpr
  intro c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl
  · exact Submodule.subset_span ⟨0, by simp [closedPlaceDirections]⟩
  · exact Submodule.subset_span ⟨1, by simp [closedPlaceDirections]⟩
  · exact Submodule.subset_span ⟨2, by simp [closedPlaceDirections]⟩

/-- Two-form version of the rational-direction inclusion. -/
theorem rationalTwoSpace_le_firstOrderEnvelopeTwoSpace :
    rationalTwoSpace ≤ firstOrderEnvelopeTwoSpace := by
  rintro p ⟨c, hc, rfl⟩
  exact ⟨c, rationalCoeffSpace_le_firstOrderEnvelopeCoeffSpace hc, rfl⟩

/-- Any decomposable lift of an effective closed-place quotient is a local
Klein lift plus a displacement supported by the rational directions and the
target plane of that same place. -/
theorem exists_localForm_add_displacement_of_decomposableLift
    (x : ClosedPlaceEffectiveParam) (d : TwoForm)
    (hd : d ∈ decomposableFiber (closedPlaceEffectivePoint x)) :
    ∃ p : LocalKleinCoord,
      SatisfiesKlein p ∧
      ∃ z ∈ rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1,
        d = localTwoForm x.1 p + z := by
  rcases exists_localDecomposableLift_of_closedPlaceEffectiveParam x with
    ⟨p, hpKlein, hpFiber⟩
  let z := d - localTwoForm x.1 p
  have hz : z ∈ rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1 :=
    fiberDifferenceSpace_closedPlace_le x hpFiber
      (Submodule.subset_span ⟨d, hd, rfl⟩)
  refine ⟨p, hpKlein, z, hz, ?_⟩
  dsimp [z]
  module

/-- At a rational effective place, every decomposable lift already belongs
to the target-clean second-jet space normalized at that place. -/
theorem decomposableLift_mem_rationalPlaceTargetClean
    (place : Fin 3) (q : EffectiveParamAt place.castSucc)
    (d : TwoForm) (hd : IsDecomposableTwo d)
    (hplace : quadraticQuotientProjection d =
      closedPlaceQuotientPoint place.castSucc q.1) :
    d ∈ rationalPlaceTargetCleanSecondJetSpace place := by
  let x : ClosedPlaceEffectiveParam := ⟨place.castSucc, q⟩
  have hdFiber : d ∈ decomposableFiber (closedPlaceEffectivePoint x) := by
    refine ⟨hd, ?_⟩
    simpa [x, closedPlaceEffectivePoint] using hplace
  rcases exists_localForm_add_displacement_of_decomposableLift x d hdFiber with
    ⟨p, _hpKlein, z, hz, hdEq⟩
  have hpClean : localTwoForm x.1 p ∈
      rationalPlaceTargetCleanSecondJetSpace place := by
    change localTwoForm place.castSucc p ∈
      rationalPlaceTargetCleanSecondJetSpace place
    exact rationalPlace_localTwoForm_mem_targetClean place p
  rcases Submodule.mem_sup.mp hz with ⟨r, hr, t, ht, hrt⟩
  have hrClean : r ∈ rationalPlaceTargetCleanSecondJetSpace place :=
    firstOrderEnvelopeTwoSpace_le_rationalPlaceTargetClean place
      (rationalTwoSpace_le_firstOrderEnvelopeTwoSpace hr)
  have htClean : t ∈ rationalPlaceTargetCleanSecondJetSpace place := by
    rcases ht with ⟨w, rfl⟩
    rw [closedPlaceTargetTwoLinear_apply,
      targetTwo_closedPlaceTargetCoeff]
    exact rationalPlace_localTwoForm_mem_targetClean place
      (closedPlaceTargetCoord place.castSucc w)
  rw [hdEq, ← hrt]
  exact (rationalPlaceTargetCleanSecondJetSpace place).add_mem hpClean
    ((rationalPlaceTargetCleanSecondJetSpace place).add_mem hrClean htClean)

/-- A decomposable target two-form is one of the rational evaluation
directions (or zero), hence belongs to their span.  This is the subspace
form of the zero-fiber classification used by the anchored plane split. -/
theorem decomposableTarget_mem_rationalTwoSpace
    {p : TwoForm} (hpdec : IsDecomposableTwo p)
    (hpTarget : p ∈ targetTwoSpace) :
    p ∈ rationalTwoSpace := by
  have hpFiber : p ∈ decomposableFiber 0 :=
    ⟨hpdec, (quadraticQuotientProjection_eq_zero_iff p).2 hpTarget⟩
  rw [zeroFiber_eq_rational] at hpFiber
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpFiber
  rcases hpFiber with rfl | rfl | rfl | rfl
  · exact Submodule.zero_mem _
  · exact ⟨rZeroCoeff, Submodule.subset_span (by simp), rfl⟩
  · exact ⟨rOneCoeff, Submodule.subset_span (by simp), rfl⟩
  · exact ⟨rInfinityCoeff, Submodule.subset_span (by simp), rfl⟩

/-- A target displacement of a decomposable anchor is localized when it is
rational, or when the common nonzero quotient fiber supplies a closed-place
chart containing that displacement. -/
def AnchorTranslateLocalized (d old : TwoForm) : Prop :=
  old ∈ rationalTwoSpace ∨
    ∃ x : ClosedPlaceEffectiveParam,
      quadraticQuotientProjection d = closedPlaceEffectivePoint x ∧
      old ∈ rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1

/-- The closed-place witness of a fixed nonzero quotient class is unique,
including its effective local parameter, by injectivity of the atlas. -/
theorem closedPlaceEffectiveParam_eq_of_anchor_projection
    {d : TwoForm} {x y : ClosedPlaceEffectiveParam}
    (hx : quadraticQuotientProjection d = closedPlaceEffectivePoint x)
    (hy : quadraticQuotientProjection d = closedPlaceEffectivePoint y) :
    x = y := by
  apply closedPlaceEffectivePoint_injective
  exact hx.symm.trans hy

/-- Once one effective chart for an anchor is fixed, every localized target
translate of that anchor lies in the rational-plus-local displacement space
of that same chart. -/
theorem AnchorTranslateLocalized.mem_at_closedPlace
    {d old : TwoForm} {x : ClosedPlaceEffectiveParam}
    (h : AnchorTranslateLocalized d old)
    (hx : quadraticQuotientProjection d = closedPlaceEffectivePoint x) :
    old ∈ rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1 := by
  rcases h with hrat | ⟨y, hy, hlocal⟩
  · exact Submodule.mem_sup_left hrat
  · have hyx : y = x := closedPlaceEffectiveParam_eq_of_anchor_projection hy hx
    simpa [hyx] using hlocal

/-- Any old-envelope translation that preserves decomposability is localized
in the preceding sense. -/
theorem anchorTranslateLocalized_of_decomposable
    (d p old : TwoForm)
    (hd : IsDecomposableTwo d) (hp : IsDecomposableTwo p)
    (hold : old ∈ firstOrderEnvelopeTwoSpace)
    (htranslate : p = old + d) :
    AnchorTranslateLocalized d old := by
  rcases decomposableEnvelopeTranslate_rational_or_localDisplacement
      d p old hd hp hold htranslate with
    ⟨c, _, holdEq, hrat | ⟨x, hplace, hlocal⟩⟩
  · left
    exact ⟨c, hrat, holdEq.symm⟩
  · exact Or.inr ⟨x, hplace, hlocal⟩

/-- Algebraic profile of a non-rigid plane with one external decomposable
anchor direction.  The dependent-syzygy branches expose either a rational
old direction or a closed-place-localized anchor translate; only the final
branch retains an independent cubic syzygy. -/
theorem nonCubicRigidAnchoredPlane_profile
    (d q c : TwoForm) (hd : IsDecomposableTwo d)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hnonrigid : ¬ CubicRigidPlane (q + d) c) :
    c ∈ rationalTwoSpace ∨
      AnchorTranslateLocalized d q ∨
      AnchorTranslateLocalized d (q + c) ∨
      ∃ x y : LinearForm, LinearIndependent F₂ ![x, y] ∧
        factorPlaneCubic x y (q + d) c = 0 := by
  rcases nonCubicRigidPlane_decomposableDirection_or_independentSyzygy
      (q + d) c hnonrigid with hcdec | hqdec | hsumdec | hsyzygy
  · exact Or.inl (decomposableTarget_mem_rationalTwoSpace hcdec
      (firstOrderEnvelopeTwoSpace_le_targetTwoSpace hc))
  · exact Or.inr (Or.inl
      (anchorTranslateLocalized_of_decomposable
        d (q + d) q hd hqdec hq rfl))
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    apply anchorTranslateLocalized_of_decomposable
      d ((q + d) + c) (q + c) hd hsumdec
      (firstOrderEnvelopeTwoSpace.add_mem hq hc)
    module
  · exact Or.inr (Or.inr (Or.inr hsyzygy))

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
