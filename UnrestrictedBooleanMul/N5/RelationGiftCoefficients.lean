import UnrestrictedBooleanMul.N5.RelationIncidence

/-!
# Coefficient representatives of relation gifts

Every additive relation among populated quotient points has a chosen-lift sum
in the nine-dimensional Hankel target.  The private target anchors therefore
give a unique coefficient representative for each relation gift.  This module
sets up that coefficient model and proves that quotienting it by the intrinsic
displacement coefficients embeds into the original two-form quotient.

The construction is purely linear algebra.  In particular, it replaces later
45-coordinate arguments by statements in `TargetCoeff`.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Chosen-lift sum attached to a sparse relation. -/
def sparseLiftSum
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) : TwoForm :=
  ∑ x ∈ r.support, populatedLift x

/-- A sparse relation has a target-valued chosen-lift sum. -/
theorem sparseLiftSum_mem_targetTwoSpace
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) :
    sparseLiftSum Q r ∈ targetTwoSpace := by
  apply (quadraticQuotientProjection_eq_zero_iff _).1
  calc
    quadraticQuotientProjection (sparseLiftSum Q r) =
        ∑ x ∈ r.support,
          quadraticQuotientProjection (populatedLift x) := by
      simp [sparseLiftSum]
    _ = ∑ x ∈ r.support, populatedQuotientPoint x := by
      simp only [populatedLift_projection]
    _ = 0 := r.sum_eq_zero

/-- The unique target coefficient word represented by a sparse relation's
chosen-lift sum. -/
def sparseRelationGiftCoeff
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) : TargetCoeff :=
  anchorRestriction (sparseLiftSum Q r)

/-- The coefficient representative reconstructs the sparse lift sum exactly. -/
theorem targetTwo_sparseRelationGiftCoeff
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) :
    targetTwo (sparseRelationGiftCoeff Q r) = sparseLiftSum Q r := by
  rcases sparseLiftSum_mem_targetTwoSpace Q r with ⟨c, hc⟩
  change targetTwo (anchorRestriction (sparseLiftSum Q r)) = _
  rw [← hc]
  exact congrArg targetTwo (anchorRestriction_targetTwo c)

/-- Coefficient representative of the chosen-lift sum of an arbitrary
relation vector. -/
def relationGiftCoefficientMap
    (Q : Submodule F₂ QuadraticQuotient) :
    relationKernel (populatedQuotientPoint (Q := Q)) →ₗ[F₂] TargetCoeff :=
  anchorRestriction.comp
    ((coefficientSum (populatedLift (Q := Q))).domRestrict
      (relationKernel (populatedQuotientPoint (Q := Q))))

/-- The chosen-lift sum of any relation is target-valued. -/
theorem coefficientSum_populatedLift_mem_targetTwoSpace
    (Q : Submodule F₂ QuadraticQuotient)
    (a : relationKernel (populatedQuotientPoint (Q := Q))) :
    coefficientSum (populatedLift (Q := Q)) a.1 ∈ targetTwoSpace := by
  apply (quadraticQuotientProjection_eq_zero_iff _).1
  rw [coefficientSum_projection
    (populatedLift (Q := Q))
    (populatedQuotientPoint (Q := Q))
    populatedLift_projection]
  exact (LinearMap.mem_ker).1 a.2

/-- The coefficient map reconstructs the chosen-lift sum exactly. -/
theorem targetTwo_relationGiftCoefficientMap
    (Q : Submodule F₂ QuadraticQuotient)
    (a : relationKernel (populatedQuotientPoint (Q := Q))) :
    targetTwo (relationGiftCoefficientMap Q a) =
      coefficientSum (populatedLift (Q := Q)) a.1 := by
  rcases coefficientSum_populatedLift_mem_targetTwoSpace Q a with ⟨c, hc⟩
  change targetTwo
      (anchorRestriction
        (coefficientSum (populatedLift (Q := Q)) a.1)) = _
  rw [← hc]
  exact congrArg targetTwo (anchorRestriction_targetTwo c)

/-- On an indicator relation, the linear coefficient map agrees with the
sparse coefficient representative. -/
theorem relationGiftCoefficientMap_sparse
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) :
    relationGiftCoefficientMap Q
        ⟨r.coefficients, r.coefficients_mem_relationKernel⟩ =
      sparseRelationGiftCoeff Q r := by
  change anchorRestriction
      (coefficientSum populatedLift (relationIndicator r.support)) =
    anchorRestriction (sparseLiftSum Q r)
  rw [coefficientSum_relationIndicator]
  rfl

/-- Coefficients whose target embeddings are intrinsic displacements. -/
def localDisplacementCoeffSpace
    (Q : Submodule F₂ QuadraticQuotient) : Submodule F₂ TargetCoeff :=
  (localDisplacementSpace Q).comap targetTwoLinear

@[simp] theorem mem_localDisplacementCoeffSpace
    (Q : Submodule F₂ QuadraticQuotient) (c : TargetCoeff) :
    c ∈ localDisplacementCoeffSpace Q ↔
      targetTwo c ∈ localDisplacementSpace Q := by
  rfl

/-- Embed the coefficient quotient by intrinsic displacements into the
original two-form quotient. -/
def targetCoeffQuotientEmbedding
    (Q : Submodule F₂ QuadraticQuotient) :
    (TargetCoeff ⧸ localDisplacementCoeffSpace Q) →ₗ[F₂]
      (TwoForm ⧸ localDisplacementSpace Q) :=
  (localDisplacementCoeffSpace Q).mapQ
    (localDisplacementSpace Q) targetTwoLinear (by
      intro c hc
      exact hc)

@[simp] theorem targetCoeffQuotientEmbedding_mk
    (Q : Submodule F₂ QuadraticQuotient) (c : TargetCoeff) :
    targetCoeffQuotientEmbedding Q
        ((Submodule.mkQ (localDisplacementCoeffSpace Q)) c) =
      (Submodule.mkQ (localDisplacementSpace Q)) (targetTwo c) := by
  rfl

/-- The coefficient quotient really is a subspace of the original gift
quotient; no target coefficient is lost by changing models. -/
theorem targetCoeffQuotientEmbedding_injective
    (Q : Submodule F₂ QuadraticQuotient) :
    Function.Injective (targetCoeffQuotientEmbedding Q) := by
  rw [← LinearMap.ker_eq_bot]
  rw [targetCoeffQuotientEmbedding, Submodule.ker_mapQ]
  change (localDisplacementCoeffSpace Q).map
      (Submodule.mkQ (localDisplacementCoeffSpace Q)) = ⊥
  exact Submodule.mkQ_map_self _

/-- Relation gifts expressed directly in the coefficient quotient. -/
def defectRelationCoeffMap
    (Q : Submodule F₂ QuadraticQuotient) :
    relationKernel (populatedQuotientPoint (Q := Q)) →ₗ[F₂]
      (TargetCoeff ⧸ localDisplacementCoeffSpace Q) :=
  (Submodule.mkQ (localDisplacementCoeffSpace Q)).comp
    (relationGiftCoefficientMap Q)

/-- The original relation map factors through its smaller coefficient model. -/
theorem defectRelationMap_factor_coefficients
    (Q : Submodule F₂ QuadraticQuotient) :
    defectRelationMap Q =
      (targetCoeffQuotientEmbedding Q).comp
        (defectRelationCoeffMap Q) := by
  ext a
  change (Submodule.mkQ (localDisplacementSpace Q))
      (coefficientSum populatedLift a.1) =
    (Submodule.mkQ (localDisplacementSpace Q))
      (targetTwo (relationGiftCoefficientMap Q a))
  rw [targetTwo_relationGiftCoefficientMap]

/-- Passing to target coefficients preserves the exact relation-gift rank. -/
theorem relationGiftRank_eq_coefficients
    (Q : Submodule F₂ QuadraticQuotient) :
    relationGiftRank Q =
      Module.finrank F₂ ↑(LinearMap.range (defectRelationCoeffMap Q)) := by
  unfold relationGiftRank
  rw [defectRelationMap_factor_coefficients]
  have hker : LinearMap.ker
      ((targetCoeffQuotientEmbedding Q).comp
        (defectRelationCoeffMap Q)) =
      LinearMap.ker (defectRelationCoeffMap Q) := by
    exact LinearMap.ker_comp_of_ker_eq_bot _
      ((LinearMap.ker_eq_bot).2
        (targetCoeffQuotientEmbedding_injective Q))
  have hleft := ((targetCoeffQuotientEmbedding Q).comp
    (defectRelationCoeffMap Q)).finrank_range_add_finrank_ker
  have hright := (defectRelationCoeffMap Q).finrank_range_add_finrank_ker
  rw [hker] at hleft
  omega

end

end N5
end UnrestrictedBooleanMul
