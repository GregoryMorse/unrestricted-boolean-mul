import UnrestrictedBooleanMul.N5.QuarticSemantic
import UnrestrictedBooleanMul.N5.EnvelopeDependentComplete
import UnrestrictedBooleanMul.N5.CubicOverlapBasis

/-!
# Circuit-facing first-order envelope semantics

This module connects literal ANF products to the normalized quartic, cubic,
and quadratic shadows used by the complete first-order envelope exclusion.
The quadratic--quadratic cubic overlap remains explicit; it is cancelled only
when equality of that literal overlap has been established.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Literal high-class equality supplies the normalized quartic and cubic
equations once the explicit Boolean cubic overlaps agree. -/
theorem lowProductHighPart_eq_of_highClass_eq_of_overlap_eq
    (ell m ell' m' : LinearForm) (q c q' c' : TwoForm)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (hoverlap : quadraticOverlapCubic q c =
      quadraticOverlapCubic q' c') :
    lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c' := by
  apply Prod.ext
  · exact ambientWedgeTwo_eq_of_highClass_eq
      ell m ell' m' q c q' c' hhigh
  · have hcubic := exactLowProductCubic_eq_of_highClass_eq
      ell m ell' m' q c q' c' hhigh
    simp only [exactLowProductCubic] at hcubic
    rw [hoverlap] at hcubic
    exact add_left_cancel hcubic

/-- Circuit-facing form of the complete envelope shadow theorem. -/
theorem semanticEnvelope_shadow
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (hoverlap : quadraticOverlapCubic q c =
      quadraticOverlapCubic q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  apply envelope_shadow a b a' b' ell m ell' m' q c q' c'
    hq hc hq' hc'
  · exact lowProductHighPart_eq_of_highClass_eq_of_overlap_eq
      ell m ell' m' q c q' c' hhigh hoverlap
  · exact hu

private theorem highQuotient_eq_of_add_eq_zero
    {x y : HighQuotientTen} (h : x + y = 0) : x = y := by
  have hself (z : HighQuotientTen) : z + z = 0 := by
    calc
      z + z = ((1 : F₂) + 1) • z := by rw [add_smul, one_smul]
      _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  calc
    x = x + 0 := by rw [add_zero]
    _ = x + (y + y) := by rw [hself]
    _ = (x + y) + y := by ac_rfl
    _ = y := by rw [h, zero_add]

/-- If the sum of two actual degree-two products is quadratic, their literal
high quotient classes agree. -/
theorem lowProductHighClass_eq_of_product_sum_mem_quadratic
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hsum :
      quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q' *
            quadraticCoordinateANF b' m' c' ∈
        N4.quadraticANFSpace 10) :
    lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c' := by
  have hzero := highProjectionTen_eq_zero_of_quadratic hsum
  rw [map_add, highProjectionTen_quadraticCoordinateANF_mul,
    highProjectionTen_quadraticCoordinateANF_mul] at hzero
  exact highQuotient_eq_of_add_eq_zero hzero

/-- Two actual degree-two products with the same quadratic factor plane
cannot add to the missing first-order target coset.  This is the first direct
ANF-level collision theorem backed by the complete envelope classifier. -/
theorem samePlane_actualLowProducts_ne_missingTargetANF
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
        quadraticCoordinateANF a' ell' q * quadraticCoordinateANF b' m' c ≠
      targetANF (firstOrderMissingCoeff + u) := by
  intro htarget
  have htargetQuadratic :
      targetANF (firstOrderMissingCoeff + u) ∈ N4.quadraticANFSpace 10 :=
    pureQuadraticANFSpace_le_quadraticANFSpace
      (targetANF_mem_pure (firstOrderMissingCoeff + u))
  have hsumQuadratic :
      quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' q *
            quadraticCoordinateANF b' m' c ∈
        N4.quadraticANFSpace 10 := by
    rw [htarget]
    exact htargetQuadratic
  have hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q c :=
    lowProductHighClass_eq_of_product_sum_mem_quadratic
      a b a' b' ell m ell' m' q c q c hsumQuadratic
  have hshadow := semanticEnvelope_shadow
    a b a' b' ell m ell' m' q c q c
      hq hc hq hc hhigh rfl u hu
  apply hshadow
  have hprojection := congrArg (quadraticProjection 10) htarget
  simpa only [map_add, quadraticProjection_quadraticCoordinateANF_mul,
    quadraticProjection_targetANF] using hprojection

/-- The direct ANF collision exclusion is independent of the ordered basis
used to present the common quadratic factor plane. -/
theorem basisChange_actualLowProducts_ne_missingTargetANF
    (g : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
        quadraticCoordinateANF a' ell' (g.basisPair q c).1 *
          quadraticCoordinateANF b' m' (g.basisPair q c).2 ≠
      targetANF (firstOrderMissingCoeff + u) := by
  intro htarget
  have hpair := g.basisPair_mem_submodule firstOrderEnvelopeTwoSpace
    q c hq hc
  have htargetQuadratic :
      targetANF (firstOrderMissingCoeff + u) ∈ N4.quadraticANFSpace 10 :=
    pureQuadraticANFSpace_le_quadraticANFSpace
      (targetANF_mem_pure (firstOrderMissingCoeff + u))
  have hsumQuadratic :
      quadraticCoordinateANF a ell q * quadraticCoordinateANF b m c +
          quadraticCoordinateANF a' ell' (g.basisPair q c).1 *
            quadraticCoordinateANF b' m' (g.basisPair q c).2 ∈
        N4.quadraticANFSpace 10 := by
    rw [htarget]
    exact htargetQuadratic
  have hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' (g.basisPair q c).1
        (g.basisPair q c).2 :=
    lowProductHighClass_eq_of_product_sum_mem_quadratic
      a b a' b' ell m ell' m' q c
        (g.basisPair q c).1 (g.basisPair q c).2 hsumQuadratic
  have hshadow := semanticEnvelope_shadow
    a b a' b' ell m ell' m' q c
      (g.basisPair q c).1 (g.basisPair q c).2
      hq hc hpair.1 hpair.2 hhigh
      (quadraticOverlapCubic_basisPair g q c).symm u hu
  apply hshadow
  have hprojection := congrArg (quadraticProjection 10) htarget
  simpa only [map_add, quadraticProjection_quadraticCoordinateANF_mul,
    quadraticProjection_targetANF] using hprojection

end
end N5
end UnrestrictedBooleanMul
