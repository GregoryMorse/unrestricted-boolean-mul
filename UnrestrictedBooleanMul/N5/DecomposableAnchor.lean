import UnrestrictedBooleanMul.N5.FourPlaceExclusion

/-!
# Decomposable lifts as a graph over the quotient

The private target anchors split every two-form into its canonical quotient
remainder and a unique target coefficient word.  For the chosen populated
lifts this identifies the relation-gift map with ordinary coefficient summation
of their anchor words.  Later displacement pivots can therefore work in nine
coordinates while retaining the full decomposability hypothesis.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Canonical linear section of the quadratic quotient obtained by clearing
all private target anchors. -/
def quadraticQuotientRemainder : QuadraticQuotient →ₗ[F₂] TwoForm :=
  targetTwoSpace.liftQ quotientRemainder (by
    intro p hp
    exact (LinearMap.mem_ker).2
      ((quotientRemainder_eq_zero_iff p).2 hp))

@[simp] theorem quadraticQuotientRemainder_mk
    (p : TwoForm) :
    quadraticQuotientRemainder (quadraticQuotientProjection p) =
      quotientRemainder p := by
  rfl

/-- The canonical quotient section is injective. -/
theorem quadraticQuotientRemainder_injective :
    Function.Injective quadraticQuotientRemainder := by
  rw [← LinearMap.ker_eq_bot]
  ext q
  constructor
  · intro hq
    change quadraticQuotientRemainder q = 0 at hq
    induction q using Quotient.inductionOn with
    | _ p =>
      change quotientRemainder p = 0 at hq
      change Submodule.Quotient.mk p = 0
      exact (Submodule.Quotient.mk_eq_zero targetTwoSpace).2
        ((quotientRemainder_eq_zero_iff p).1 hq)
  · intro hq
    have hqzero : q = 0 := by simpa using hq
    subst q
    exact LinearMap.map_zero quadraticQuotientRemainder

/-- Clearing anchors and then restoring them reconstructs the original
two-form. -/
theorem quotientRemainder_add_targetTwo_anchorRestriction
    (p : TwoForm) :
    quotientRemainder p + targetTwo (anchorRestriction p) = p := by
  rw [quotientRemainder_apply, add_assoc,
    ZModModule.add_self, add_zero]

/-- Anchor coefficient word of the chosen decomposable lift of a populated
quotient point. -/
def populatedAnchor
    {Q : Submodule F₂ QuadraticQuotient}
    (q : PopulatedPoint Q) : TargetCoeff :=
  anchorRestriction (populatedLift q)

/-- Exact graph decomposition of a chosen populated lift. -/
theorem populatedLift_eq_quotientRemainder_add_anchor
    {Q : Submodule F₂ QuadraticQuotient}
    (q : PopulatedPoint Q) :
    populatedLift q =
      quadraticQuotientRemainder (populatedQuotientPoint q) +
        targetTwo (populatedAnchor q) := by
  rw [← populatedLift_projection q,
    quadraticQuotientRemainder_mk]
  exact (quotientRemainder_add_targetTwo_anchorRestriction
    (populatedLift q)).symm

/-- The graph point determined by each populated anchor is decomposable. -/
theorem quotientRemainder_add_populatedAnchor_decomposable
    {Q : Submodule F₂ QuadraticQuotient}
    (q : PopulatedPoint Q) :
    IsDecomposableTwo
      (quadraticQuotientRemainder (populatedQuotientPoint q) +
        targetTwo (populatedAnchor q)) := by
  rw [← populatedLift_eq_quotientRemainder_add_anchor]
  exact (populatedLift_mem_fiber q).1

/-- The linear relation-gift coefficient map is exactly summation of the
populated anchor words. -/
theorem relationGiftCoefficientMap_eq_anchorSum
    (Q : Submodule F₂ QuadraticQuotient) :
    relationGiftCoefficientMap Q =
      (coefficientSum (populatedAnchor (Q := Q))).domRestrict
        (relationKernel (populatedQuotientPoint (Q := Q))) := by
  ext a i
  simp [relationGiftCoefficientMap, populatedAnchor, coefficientSum]

/-- Sparse form of the anchor-sum identity. -/
theorem sparseRelationGiftCoeff_eq_sum_populatedAnchor
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) :
    sparseRelationGiftCoeff Q r =
      ∑ x ∈ r.support, populatedAnchor x := by
  rw [← relationGiftCoefficientMap_sparse Q r,
    relationGiftCoefficientMap_eq_anchorSum]
  change coefficientSum populatedAnchor (relationIndicator r.support) = _
  exact coefficientSum_relationIndicator populatedAnchor r.support

end

end N5
end UnrestrictedBooleanMul
