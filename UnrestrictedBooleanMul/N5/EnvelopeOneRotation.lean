import UnrestrictedBooleanMul.N5.EnvelopeLocalSymmetry

/-!
# Closing the one-rotation envelope branch

The Pluecker classifier puts a one-local difference into quadratic planes
`(p,q)` and `(p,q+t)`, with `(p,t)` an ordered presentation of one rational
value--jet plane.  The algebraic product rewiring then produces one product
on `(p,t)` and one on the dependent plane `(0,q+t)`.  This module transports
the first product back to the canonical rational frame and applies the
uniform local/dependent exclusion.

Only linear basis changes, exterior identities, and old-envelope corrections
are used.  No circuit states or Boolean assignments are enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Both members of an ordered basis change stay in a submodule containing
the original pair. -/
theorem PlaneBasisChange.basisPair_mem_submodule
    (W : Submodule F₂ TwoForm) (g : PlaneBasisChange) (q c : TwoForm)
    (hq : q ∈ W) (hc : c ∈ W) :
    (g.basisPair q c).1 ∈ W ∧ (g.basisPair q c).2 ∈ W := by
  cases g with
  | identity => exact ⟨hq, hc⟩
  | swap => exact ⟨hc, hq⟩
  | rotateRight => exact ⟨hq, W.add_mem hq hc⟩
  | rotateLeft => exact ⟨W.add_mem hq hc, hc⟩
  | cycleRight => exact ⟨hc, W.add_mem hq hc⟩
  | cycleLeft => exact ⟨W.add_mem hq hc, hq⟩

/-- A one-rotation normal form cannot have its total Boolean quadratic
shadow in the affine missing target coset. -/
theorem rationalLocalOneRotation_normalForm_shadow_not_missingCoset
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
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
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
    have := hgc.2
    rw [hg] at this
    exact this
  have ht : t ∈ firstOrderEnvelopeTwoSpace := by
    have hlocal := h.basisPair_mem_submodule firstOrderEnvelopeTwoSpace
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
      (ExceptionalIndependentPlane.left_mem_firstOrderEnvelope _)
      (ExceptionalIndependentPlane.right_mem_firstOrderEnvelope _)
    have := hlocal.2
    rw [hh] at this
    exact this
  have hd : d ∈ firstOrderEnvelopeTwoSpace :=
    firstOrderEnvelopeTwoSpace.add_mem hq₀ ht
  rcases hd with ⟨dc, hdc, hdcEq⟩
  have hrewireCubic : factorPlaneCubic L M p t =
      factorPlaneCubic X Y 0 (targetTwo dc) := by
    have h := oneRotation_local_eq_dependent_cubic_of_high_eq
      g k ell m ell' m' q c q' c' p q₀ t hg hk hhigh
    change factorPlaneCubic L M p t = factorPlaneCubic X Y 0 d at h
    change factorPlaneCubic L M p t =
      factorPlaneCubic X Y 0 (targetTwoLinear dc)
    rw [hdcEq]
    exact h
  have hcanonicalCubic :
      factorPlaneCubic LM.1 LM.2
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
        factorPlaneCubic X Y 0 (targetTwo dc) := by
    have hchanged := congrArg Prod.snd
      (changedLowProductHighPart_inverse h L M
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right)
    have hcanonical := exceptionalPlane_basisChange_cubic
      (.rationalJet place) h LM.1 LM.2
    calc
      factorPlaneCubic LM.1 LM.2
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
          (changedLowProductHighPart h LM.1 LM.2
            (ExceptionalIndependentPlane.rationalJet place).left
            (ExceptionalIndependentPlane.rationalJet place).right).2 :=
        hcanonical.symm
      _ = (lowProductHighPart L M
          (h.basisPair
            (ExceptionalIndependentPlane.rationalJet place).left
            (ExceptionalIndependentPlane.rationalJet place).right).1
          (h.basisPair
            (ExceptionalIndependentPlane.rationalJet place).left
            (ExceptionalIndependentPlane.rationalJet place).right).2).2 := by
        simpa only [LM] using hchanged
      _ = factorPlaneCubic L M p t := by
        simp only [hh, lowProductHighPart]
      _ = factorPlaneCubic X Y 0 (targetTwo dc) := hrewireCubic
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
          (changedLocal + dependent) + (canonicalLocal + dependent) =
              (changedLocal + canonicalLocal) +
                (dependent + dependent) := by module
          _ = changedLocal + canonicalLocal := by
            have hzero : dependent + dependent = 0 := by
              funext s
              exact CharTwo.add_self_eq_zero (dependent s)
            rw [hzero, add_zero]
      rw [hreassoc]
      exact hlocalCorrection
    · intro v hv
      exact rationalJet_actual_local_dependent_shadow_not_missingCoset
        place AB.1 AB.2 A' B' LM.1 LM.2 X Y dc hdc
          hcanonicalCubic v hv
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
        _ = lowProductQuadraticShadow A B L M p t +
            lowProductQuadraticShadow A' B' X Y 0 (targetTwo dc) := by
          rw [hdcEq']
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

/-- The actual one-local Pluecker-difference branch, with the normal-form
data and all basis changes discharged internally. -/
theorem oneLocalKernelDifference_shadow_not_missingCoset
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
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
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
  exact rationalLocalOneRotation_normalForm_shadow_not_missingCoset
    place g h k a b a' b' ell m ell' m' q c q' c' p q₀ t
      hq hc hq' hc' hg hh' hk hhigh u hu

end

end N5
end UnrestrictedBooleanMul
