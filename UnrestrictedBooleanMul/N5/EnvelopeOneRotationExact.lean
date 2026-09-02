import UnrestrictedBooleanMul.N5.EnvelopeRationalExact
import UnrestrictedBooleanMul.N5.EnvelopeOneRotation

/-!
# Exact Boolean closure of the one-rotation envelope branch

This module reuses the checked Pluecker normal form and quadratic-shadow
transport.  Its high premise is the literal Boolean quotient class; exact
cubic rewiring and the exact rational local/dependent theorem discharge the
only semantic difference from the normalized development.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem rationalLocalOneRotation_exact_shadow_not_missingCoset
    (place : Fin 3) (g h k : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' p q₀ t : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hg : g.basisPair q c = (p, q₀))
    (hh : h.basisPair
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right = (p, t))
    (hk : k.basisPair q' c' = (p, q₀ + t))
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  let A : F₂ := (g.basisPair a b).1
  let B : F₂ := (g.basisPair a b).2 + (k.basisPair a' b').2
  let A' : F₂ := (g.basisPair a b).1 + (k.basisPair a' b').1
  let B' : F₂ := (k.basisPair a' b').2
  let L : LinearForm := (g.basisPair ell m).1
  let M : LinearForm :=
    (g.basisPair ell m).2 + (k.basisPair ell' m').2
  let X : LinearForm :=
    (g.basisPair ell m).1 + (k.basisPair ell' m').1
  let Y : LinearForm := (k.basisPair ell' m').2
  let AB : F₂ × F₂ := h.inverse.basisPair A B
  let LM : LinearForm × LinearForm := h.inverse.basisPair L M
  let d : TwoForm := q₀ + t
  have hgc := g.basisPair_mem_submodule
    firstOrderEnvelopeTwoSpace q c hq hc
  have hq₀ : q₀ ∈ firstOrderEnvelopeTwoSpace := by
    have hmem := hgc.2
    rw [hg] at hmem
    exact hmem
  have ht : t ∈ firstOrderEnvelopeTwoSpace := by
    have hlocal := h.basisPair_mem_submodule firstOrderEnvelopeTwoSpace
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
      (ExceptionalIndependentPlane.left_mem_firstOrderEnvelope _)
      (ExceptionalIndependentPlane.right_mem_firstOrderEnvelope _)
    have hmem := hlocal.2
    rw [hh] at hmem
    exact hmem
  have hd : d ∈ firstOrderEnvelopeTwoSpace :=
    firstOrderEnvelopeTwoSpace.add_mem hq₀ ht
  rcases hd with ⟨dc, hdc, hdcEq⟩
  have hrewireCubic : exactLowProductCubic L M p t =
      exactLowProductCubic X Y 0 (targetTwo dc) := by
    have h := oneRotation_local_eq_dependent_exactCubic_of_highClass_eq
      g k ell m ell' m' q c q' c' p q₀ t hg hk hhigh
    change exactLowProductCubic L M p t =
      exactLowProductCubic X Y 0 d at h
    change exactLowProductCubic L M p t =
      exactLowProductCubic X Y 0 (targetTwoLinear dc)
    rw [hdcEq]
    exact h
  have hcanonicalCubic :
      exactLowProductCubic LM.1 LM.2
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
        exactLowProductCubic X Y 0 (targetTwo dc) := by
    have hlinear : h.basisPair LM.1 LM.2 = (L, M) := by
      simpa only [LM] using h.basisPair_apply_inverse L M
    have hinvariant := h.lowProductHighClass_basisPair LM.1 LM.2
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
    rw [hlinear, hh] at hinvariant
    have hcanonicalToLocal :
        exactLowProductCubic LM.1 LM.2
            (ExceptionalIndependentPlane.rationalJet place).left
            (ExceptionalIndependentPlane.rationalJet place).right =
          exactLowProductCubic L M p t :=
      exactLowProductCubic_eq_of_highClass_eq
        _ _ _ _ _ _ _ _ hinvariant.symm
    exact hcanonicalToLocal.trans hrewireCubic
  let changedLocal : TwoForm :=
    changedLowProductQuadraticShadow h AB.1 AB.2 LM.1 LM.2
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
  let canonicalLocal : TwoForm :=
    lowProductQuadraticShadow AB.1 AB.2 LM.1 LM.2
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
  let dependent : TwoForm :=
    lowProductQuadraticShadow A' B' X Y 0 (targetTwo dc)
  have hchangedLocal : changedLocal =
      lowProductQuadraticShadow A B L M p t := by
    have hinverse := changedLowProductQuadraticShadow_inverse h A B L M
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
    simpa only [changedLocal, AB, LM, hh] using hinverse
  have hlocalCorrection : changedLocal + canonicalLocal ∈
      firstOrderEnvelopeTwoSpace := by
    exact (exceptionalPlane_basisChange_high_and_shadow
      (.rationalJet place) h AB.1 AB.2 LM.1 LM.2).2
  have hrewiredExcluded : ∀ (v : TargetCoeff),
      v ∈ firstOrderEnvelopeCoeffSpace →
      lowProductQuadraticShadow A B L M p t +
          lowProductQuadraticShadow A' B' X Y 0 (targetTwo dc) ≠
        targetTwo (firstOrderMissingCoeff + v) := by
    intro v hv
    rw [← hchangedLocal]
    apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
      (changedLocal + dependent) (canonicalLocal + dependent)
    · have hreassoc :
          (changedLocal + dependent) + (canonicalLocal + dependent) =
            changedLocal + canonicalLocal := by
        calc
          _ = (changedLocal + canonicalLocal) +
              (dependent + dependent) := by module
          _ = changedLocal + canonicalLocal := by
            have hzero : dependent + dependent = 0 := by
              funext s
              exact CharTwo.add_self_eq_zero (dependent s)
            rw [hzero, add_zero]
      rw [hreassoc]
      exact hlocalCorrection
    · intro w hw
      exact rationalJet_actual_exact_local_dependent_shadow_not_missingCoset
        place AB.1 AB.2 A' B' LM.1 LM.2 X Y dc hdc
          hcanonicalCubic w hw
    · exact hv
  have hchangedExcluded : ∀ (v : TargetCoeff),
      v ∈ firstOrderEnvelopeCoeffSpace →
      changedLowProductQuadraticShadow g a b ell m q c +
          changedLowProductQuadraticShadow k a' b' ell' m' q' c' ≠
        targetTwo (firstOrderMissingCoeff + v) := by
    intro v hv
    have hrewireShadow := changedLowProductQuadraticShadow_oneRotation_rewire
      g k a b a' b' ell m ell' m' q c q' c' p q₀ t hg hk
    change changedLowProductQuadraticShadow g a b ell m q c +
        changedLowProductQuadraticShadow k a' b' ell' m' q' c' =
      lowProductQuadraticShadow A B L M p t +
        lowProductQuadraticShadow A' B' X Y 0 d at hrewireShadow
    have hdcEq' : targetTwo dc = d := hdcEq
    have hrewireShadow' :
        changedLowProductQuadraticShadow g a b ell m q c +
            changedLowProductQuadraticShadow k a' b' ell' m' q' c' =
          lowProductQuadraticShadow A B L M p t +
            lowProductQuadraticShadow A' B' X Y 0 (targetTwo dc) := by
      calc
        _ = lowProductQuadraticShadow A B L M p t +
            lowProductQuadraticShadow A' B' X Y 0 d := hrewireShadow
        _ = _ := by rw [hdcEq']
    rw [hrewireShadow']
    exact hrewiredExcluded v hv
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (lowProductQuadraticShadow a b ell m q c +
      lowProductQuadraticShadow a' b' ell' m' q' c')
    (changedLowProductQuadraticShadow g a b ell m q c +
      changedLowProductQuadraticShadow k a' b' ell' m' q' c')
  · have hcorrection := twoPlaneBasisChanges_shadow_sum_add_original_mem
      firstOrderEnvelopeTwoSpace g k a b a' b' ell m ell' m'
        q c q' c' hq hc hq' hc'
    simpa only [add_comm] using hcorrection
  · intro v hv
    exact hchangedExcluded v hv
  · exact hu

/-- Exact high-class form of the actual one-local Pluecker branch. -/
theorem oneLocalKernelDifference_exact_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂) (place : Fin 3)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections place)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hxy := exactFirstOrderCoordinates_linearIndependent
    q c x y hx hy hind
  have hzw := exactFirstOrderCoordinates_linearIndependent
    q' c' z w hz hw hind'
  rcases oneLocalKernelDifference_actualNormalForm
      q c q' c' x y z w place hx hy hz hw hxy hzw hdiff with
    ⟨p, q₀, t, g, h, k, _hp, hg, hh, hk⟩
  have hh' : h.basisPair
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = (p, t) := by
    simpa only [exactFirstOrderTwoMap_localValueCoordinates,
      exactFirstOrderTwoMap_localJetCoordinates] using hh
  exact rationalLocalOneRotation_exact_shadow_not_missingCoset
    place g h k a b a' b' ell m ell' m' q c q' c' p q₀ t
      hq hc hq' hc' hg hh' hk hhigh u hu

end
end N5
end UnrestrictedBooleanMul
