import UnrestrictedBooleanMul.N5.EnvelopeDistinctRationalExact
import UnrestrictedBooleanMul.N5.EnvelopeTwoRotationShadow

/-!
# Exact Boolean shadows for two rational rotations

This file lifts the algebraic two-rotation normal forms from the homogeneous
cubic quotient to the literal Boolean high quotient.  The bilinear product
rewire preserves the complete quotient, so the terminal separation theorem
is the exact distinct-rational result.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The direct exact two-rotation rewire for the four middle ordered-basis
changes which do not preserve their first line. -/
theorem rationalTwoRotation_exact_normalForm_shadow_not_missingCoset
    (place other : Fin 3) (hne : place ≠ other)
    (h k e : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (p v t r s z : TwoForm)
    (hplace : h.basisPair
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = (p, t))
    (hother : k.basisPair
      (ExceptionalIndependentPlane.rationalJet other).left
      (ExceptionalIndependentPlane.rationalJet other).right = (r, z))
    (hmiddle : e.basisPair p v = (r, s))
    (he : e = .swap ∨ e = .rotateLeft ∨
      e = .cycleRight ∨ e = .cycleLeft)
    (hhigh : lowProductHighClass ell m p (v + t) =
      lowProductHighClass ell' m' (s + z) r)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m p (v + t) +
        lowProductQuadraticShadow a' b' ell' m' (s + z) r ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hrewiredHigh := lowProductHighClass_twoProduct_rewire_of_eq
    ell m ell' m' p (v + t) (s + z) r hhigh
  have hrewiredShadow := lowProductQuadraticShadow_twoProduct_rewire
    a b a' b' ell m ell' m' p (v + t) (s + z) r
  rcases he with rfl | rfl | rfl | rfl
  · simp only [PlaneBasisChange.basisPair] at hmiddle
    have hr := congrArg Prod.fst hmiddle
    have hs := congrArg Prod.snd hmiddle
    simp only at hr hs
    subst r
    subst s
    have hpairPlace :
        (p, (v + t) + v) = PlaneBasisChange.identity.basisPair p t := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpairOther :
        (p + (p + z), v) = PlaneBasisChange.swap.basisPair v z := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpresentation := isRationalJetPresentation_of_iterated_basisPair
      place h .identity p t p ((v + t) + v) hplace hpairPlace
    have hpresentation' := isRationalJetPresentation_of_iterated_basisPair
      other k .swap v z (p + (p + z)) v hother hpairOther
    rw [hrewiredShadow]
    exact distinctRationalJetPresentations_exact_shadow_not_missingCoset
      place other hne a (b + b') (a + a') b'
        ell (m + m') (ell + ell') m'
        p ((v + t) + v) (p + (p + z)) v
        hpresentation hpresentation' hrewiredHigh u hu
  · simp only [PlaneBasisChange.basisPair] at hmiddle
    have hr := congrArg Prod.fst hmiddle
    have hs := congrArg Prod.snd hmiddle
    simp only at hr hs
    subst r
    subst s
    have hpairPlace :
        (p, (v + t) + (p + v)) =
          PlaneBasisChange.rotateRight.basisPair p t := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpairOther :
        (p + (v + z), p + v) =
          PlaneBasisChange.cycleLeft.basisPair (p + v) z := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpresentation := isRationalJetPresentation_of_iterated_basisPair
      place h .rotateRight p t p ((v + t) + (p + v)) hplace hpairPlace
    have hpresentation' := isRationalJetPresentation_of_iterated_basisPair
      other k .cycleLeft (p + v) z (p + (v + z)) (p + v)
        hother hpairOther
    rw [hrewiredShadow]
    exact distinctRationalJetPresentations_exact_shadow_not_missingCoset
      place other hne a (b + b') (a + a') b'
        ell (m + m') (ell + ell') m'
        p ((v + t) + (p + v)) (p + (v + z)) (p + v)
        hpresentation hpresentation' hrewiredHigh u hu
  · simp only [PlaneBasisChange.basisPair] at hmiddle
    have hr := congrArg Prod.fst hmiddle
    have hs := congrArg Prod.snd hmiddle
    simp only at hr hs
    subst r
    subst s
    have hpairPlace :
        (p, (v + t) + v) = PlaneBasisChange.identity.basisPair p t := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpairOther :
        (p + ((p + v) + z), v) =
          PlaneBasisChange.cycleLeft.basisPair v z := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpresentation := isRationalJetPresentation_of_iterated_basisPair
      place h .identity p t p ((v + t) + v) hplace hpairPlace
    have hpresentation' := isRationalJetPresentation_of_iterated_basisPair
      other k .cycleLeft v z (p + ((p + v) + z)) v hother hpairOther
    rw [hrewiredShadow]
    exact distinctRationalJetPresentations_exact_shadow_not_missingCoset
      place other hne a (b + b') (a + a') b'
        ell (m + m') (ell + ell') m'
        p ((v + t) + v) (p + ((p + v) + z)) v
        hpresentation hpresentation' hrewiredHigh u hu
  · simp only [PlaneBasisChange.basisPair] at hmiddle
    have hr := congrArg Prod.fst hmiddle
    have hs := congrArg Prod.snd hmiddle
    simp only at hr hs
    subst r
    subst s
    have hpairPlace :
        (p, (v + t) + (p + v)) =
          PlaneBasisChange.rotateRight.basisPair p t := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpairOther :
        (p + (p + z), p + v) =
          PlaneBasisChange.swap.basisPair (p + v) z := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpresentation := isRationalJetPresentation_of_iterated_basisPair
      place h .rotateRight p t p ((v + t) + (p + v)) hplace hpairPlace
    have hpresentation' := isRationalJetPresentation_of_iterated_basisPair
      other k .swap (p + v) z (p + (p + z)) (p + v) hother hpairOther
    rw [hrewiredShadow]
    exact distinctRationalJetPresentations_exact_shadow_not_missingCoset
      place other hne a (b + b') (a + a') b'
        ell (m + m') (ell + ell') m'
        p ((v + t) + (p + v)) (p + (p + z)) (p + v)
        hpresentation hpresentation' hrewiredHigh u hu

/-- Presentation-free exact exclusion once the two-rotation normal-form
ledger has been constructed. -/
theorem twoRotationNormalFormData_exact_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (place other : Fin 3) (hne : place ≠ other)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hdata : TwoRotationNormalFormData q c q' c' place other)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases hdata with
    ⟨p, v, t, r, s, d, hPlace, hOther, kFirst, kSecond, e,
      hkFirst, hkSecond, hhPlace, hhOther, hmiddle, hadmissible⟩
  let ab := kFirst.basisPair a b
  let lm := kFirst.basisPair ell m
  let ab' := kSecond.basisPair a' b'
  let lm' := kSecond.basisPair ell' m'
  have hchangedHigh :
      lowProductHighClass
          (kFirst.basisPair ell m).1 (kFirst.basisPair ell m).2
          (kFirst.basisPair q c).1 (kFirst.basisPair q c).2 =
        lowProductHighClass
          (kSecond.basisPair ell' m').1 (kSecond.basisPair ell' m').2
          (kSecond.basisPair q' c').1 (kSecond.basisPair q' c').2 := by
    calc
      _ = lowProductHighClass ell m q c :=
        kFirst.lowProductHighClass_basisPair ell m q c
      _ = lowProductHighClass ell' m' q' c' := hhigh
      _ = _ :=
        (kSecond.lowProductHighClass_basisPair ell' m' q' c').symm
  have hnormalizedHigh :
      lowProductHighClass lm.1 lm.2 p (v + t) =
        lowProductHighClass lm'.2 lm'.1 (s + d) r := by
    have hchangedHigh' := hchangedHigh
    rw [hkFirst, hkSecond] at hchangedHigh'
    change lowProductHighClass lm.1 lm.2 p (v + t) =
      lowProductHighClass lm'.1 lm'.2 r (s + d) at hchangedHigh'
    exact hchangedHigh'.trans
      (lowProductHighClass_swap lm'.1 lm'.2 r (s + d))
  have hchangedExcluded : ∀ (vCoeff : TargetCoeff),
      vCoeff ∈ firstOrderEnvelopeCoeffSpace →
        changedLowProductQuadraticShadow kFirst a b ell m q c +
            changedLowProductQuadraticShadow kSecond a' b' ell' m' q' c' ≠
          targetTwo (firstOrderMissingCoeff + vCoeff) := by
    intro vCoeff hvCoeff
    have hnormalizedExcluded :=
      rationalTwoRotation_exact_normalForm_shadow_not_missingCoset
        place other hne hPlace hOther e
        ab.1 ab.2 ab'.2 ab'.1 lm.1 lm.2 lm'.2 lm'.1
        p v t r s d hhPlace hhOther hmiddle hadmissible
        hnormalizedHigh vCoeff hvCoeff
    simp only [changedLowProductQuadraticShadow]
    rw [hkFirst, hkSecond]
    change
      lowProductQuadraticShadow ab.1 ab.2 lm.1 lm.2 p (v + t) +
          lowProductQuadraticShadow ab'.1 ab'.2 lm'.1 lm'.2 r (s + d) ≠
        targetTwo (firstOrderMissingCoeff + vCoeff)
    rw [lowProductQuadraticShadow_swap ab'.1 ab'.2 lm'.1 lm'.2 r (s + d)]
    exact hnormalizedExcluded
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (lowProductQuadraticShadow a b ell m q c +
      lowProductQuadraticShadow a' b' ell' m' q' c')
    (changedLowProductQuadraticShadow kFirst a b ell m q c +
      changedLowProductQuadraticShadow kSecond a' b' ell' m' q' c')
  · have hcorrection := twoPlaneBasisChanges_shadow_sum_add_original_mem
      firstOrderEnvelopeTwoSpace kFirst kSecond
        a b a' b' ell m ell' m' q c q' c' hq hc hq' hc'
    simpa only [add_comm] using hcorrection
  · exact hchangedExcluded
  · exact hu

/-- The independent-midpoint two-local chain inherits the exact exclusion
from its algebraic normal form. -/
theorem twoLocalKernelDifference_chain_exact_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (x y z w rCoord sCoord : Fin 8 → F₂)
    (place other : Fin 3) (hne : place ≠ other)
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
    (hrsCoord : LinearIndependent F₂ ![rCoord, sCoord])
    (hfirst : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff rCoord sCoord =
        firstOrderLocalKernelDirections place)
    (hsecond : firstOrderPlaneCoeff rCoord sCoord +
      firstOrderPlaneCoeff z w =
        firstOrderLocalKernelDirections other)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hdata := twoLocalKernelDifference_chain_normalForms
      q c q' c' x y z w rCoord sCoord place other hne
      hx hy hz hw hind hind' hrsCoord hfirst hsecond
  exact twoRotationNormalFormData_exact_shadow_not_missingCoset
    a b a' b' ell m ell' m' q c q' c' place other hne
      hq hc hq' hc' hdata hhigh u hu

/-- Complete exact weight-two local-difference shadow exclusion.  Both
collapsed rational endpoints and the independent-midpoint chain are handled
without replacing the literal Boolean high quotient by a homogeneous proxy. -/
theorem twoLocalKernelDifference_exact_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂)
    (place other : Fin 3)
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
    (hne : place ≠ other)
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections place +
        firstOrderLocalKernelDirections other)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases twoLocalKernelDifference_chain x y z w place other hne hdiff with
    hplace | hother | ⟨rCoord, sCoord, hrs, hchain⟩
  · have hpresentation := isRationalJetPresentation_of_planeCoeff_eq_local
      q c x y place hx hy hind hplace
    have hsecond := other_planeCoeff_of_twoLocal_total
      x y z w place other hdiff hplace
    have hpresentation' := isRationalJetPresentation_of_planeCoeff_eq_local
      q' c' z w other hz hw hind' hsecond
    exact distinctRationalJetPresentations_exact_shadow_not_missingCoset
      place other hne a b a' b' ell m ell' m' q c q' c'
        hpresentation hpresentation' hhigh u hu
  · have hpresentation := isRationalJetPresentation_of_planeCoeff_eq_local
      q c x y other hx hy hind hother
    have hdiff' : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
        firstOrderLocalKernelDirections other +
          firstOrderLocalKernelDirections place := by
      simpa only [add_comm] using hdiff
    have hsecond := other_planeCoeff_of_twoLocal_total
      x y z w other place hdiff' hother
    have hpresentation' := isRationalJetPresentation_of_planeCoeff_eq_local
      q' c' z w place hz hw hind' hsecond
    exact distinctRationalJetPresentations_exact_shadow_not_missingCoset
      other place hne.symm a b a' b' ell m ell' m' q c q' c'
        hpresentation hpresentation' hhigh u hu
  · rcases hchain with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact twoLocalKernelDifference_chain_exact_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c' x y z w rCoord sCoord
        place other hne hq hc hq' hc' hx hy hz hw hind hind' hrs
        hfirst hsecond hhigh u hu
    · exact twoLocalKernelDifference_chain_exact_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c' x y z w rCoord sCoord
        other place hne.symm hq hc hq' hc' hx hy hz hw hind hind' hrs
        hfirst hsecond hhigh u hu

end
end N5
end UnrestrictedBooleanMul
