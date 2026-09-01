import UnrestrictedBooleanMul.N5.DecomposableAnchor

/-!
# Sparse anchor generators of the relation-gift image

For a defect space of dimension at most three, Fano lines and quadrilaterals
generate the relation kernel.  In the coefficient model their gifts are just
the corresponding sums of populated anchor words, modulo the active
displacement coefficients.  This module states that reduction directly in
the nine-coordinate quotient used by the displacement pivots.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Anchor summation on all coefficient vectors, followed by the intrinsic
displacement quotient. -/
def populatedAnchorQuotientMap
    (Q : Submodule F₂ QuadraticQuotient) :
    (PopulatedPoint Q → F₂) →ₗ[F₂]
      (TargetCoeff ⧸ localDisplacementCoeffSpace Q) :=
  (Submodule.mkQ (localDisplacementCoeffSpace Q)).comp
    (coefficientSum (populatedAnchor (Q := Q)))

/-- The coefficient relation map is the restriction of anchor summation to
the relation kernel. -/
theorem defectRelationCoeffMap_eq_anchorQuotient_domRestrict
    (Q : Submodule F₂ QuadraticQuotient) :
    defectRelationCoeffMap Q =
      (populatedAnchorQuotientMap Q).domRestrict
        (relationKernel (populatedQuotientPoint (Q := Q))) := by
  rw [defectRelationCoeffMap, relationGiftCoefficientMap_eq_anchorSum]
  rfl

/-- A sparse coefficient gift is the quotient class of its anchor sum. -/
theorem populatedAnchorQuotientMap_sparse_apply
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) :
    populatedAnchorQuotientMap Q r.coefficients =
      (Submodule.mkQ (localDisplacementCoeffSpace Q))
        (∑ x ∈ r.support, populatedAnchor x) := by
  change (Submodule.mkQ (localDisplacementCoeffSpace Q))
    (coefficientSum populatedAnchor (relationIndicator r.support)) = _
  rw [coefficientSum_relationIndicator]

/-- Sparse line and quadrilateral anchor sums in the coefficient quotient. -/
def smallAnchorGiftVectors
    (Q : Submodule F₂ QuadraticQuotient) :
    Set (TargetCoeff ⧸ localDisplacementCoeffSpace Q) :=
  populatedAnchorQuotientMap Q '' smallSparseRelationVectors Q

/-- The coefficient gift range is generated exactly by sparse line and
quadrilateral anchor sums. -/
theorem defectRelationCoeffMap_range_eq_span_smallAnchorGifts
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    LinearMap.range (defectRelationCoeffMap Q) =
      Submodule.span F₂ (smallAnchorGiftVectors Q) := by
  rw [defectRelationCoeffMap_eq_anchorQuotient_domRestrict,
    LinearMap.range_domRestrict,
    relationKernel_eq_fanoRelationSpan Q hQ,
    fanoRelationSpan, Submodule.map_span]
  rfl

/-- The sparse anchor-span dimension is exactly the relation-gift rank. -/
theorem relationGiftRank_eq_smallAnchorGiftSpan
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    relationGiftRank Q =
      Module.finrank F₂
        (Submodule.span F₂ (smallAnchorGiftVectors Q)) := by
  rw [relationGiftRank_eq_coefficients,
    defectRelationCoeffMap_range_eq_span_smallAnchorGifts Q hQ]

end

end N5
end UnrestrictedBooleanMul
