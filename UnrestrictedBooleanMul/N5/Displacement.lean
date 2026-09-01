import UnrestrictedBooleanMul.N5.MixedPlaceDegreeInfinity

/-!
# Defect capacity and relation gifts

This module specializes the exact relation-map construction to a defect
subspace in the five-term quadratic quotient.  It defines the populated
nonzero fibers, chooses one decomposable lift in each fiber, and separates
the rational/local displacement space from the remaining relation gifts.

The resulting formula is the algebraic interface used by the manuscript's
displacement bound; no circuit enumeration or imported coordinate scan is
used here.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem twoForm_sub_eq_add (p q : TwoForm) : p - q = p + q := by
  rw [sub_eq_add_neg]
  congr 1
  funext i
  rw [← neg_one_mul]
  norm_num [N3Certificate.two_eq_zero_f2]

/-- Target two-forms coming from the three rational evaluation directions. -/
def rationalTwoSpace : Submodule F₂ TwoForm :=
  rationalCoeffSpace.map targetTwoLinear

/-- Linear target-plane coordinates inside a closed-place local exterior
square. -/
def closedPlaceTargetCoordLinear (place : Fin 4) :
    LocalTargetParam →ₗ[F₂] LocalKleinCoord where
  toFun := closedPlaceTargetCoord place
  map_add' z w := by
    funext i
    fin_cases place <;> fin_cases i <;>
      simp [closedPlaceTargetCoord] <;> module
  map_smul' a z := by
    funext i
    fin_cases place <;> fin_cases i <;>
      simp [closedPlaceTargetCoord, mul_add]

/-- The corresponding target two-form map. -/
def closedPlaceTargetTwoLinear (place : Fin 4) :
    LocalTargetParam →ₗ[F₂] TwoForm :=
  (localTwoFormLinear place).comp (closedPlaceTargetCoordLinear place)

@[simp] theorem closedPlaceTargetTwoLinear_apply (place : Fin 4)
    (z : LocalTargetParam) :
    closedPlaceTargetTwoLinear place z =
      targetTwo (closedPlaceTargetCoeff place z) :=
  (targetTwo_closedPlaceTargetCoeff place z).symm

/-- Two-form target plane associated with one of the four closed places. -/
def closedPlaceTargetTwoSpace (place : Fin 4) : Submodule F₂ TwoForm :=
  LinearMap.range (closedPlaceTargetTwoLinear place)

theorem closedPlaceTargetCoord_injective (place : Fin 4) :
    Function.Injective (closedPlaceTargetCoord place) := by
  intro z w hzw
  funext i
  fin_cases i
  · have h := congrFun hzw (1 : Fin 6)
    fin_cases place <;> simpa [closedPlaceTargetCoord] using h
  · have h := congrFun hzw (2 : Fin 6)
    fin_cases place <;> simpa [closedPlaceTargetCoord] using h

theorem closedPlaceTargetTwoLinear_injective (place : Fin 4) :
    Function.Injective (closedPlaceTargetTwoLinear place) := by
  intro z w hzw
  apply closedPlaceTargetCoord_injective place
  apply localTwoForm_injective place
  exact hzw

theorem closedPlaceTargetTwoSpace_finrank (place : Fin 4) :
    Module.finrank F₂ (closedPlaceTargetTwoSpace place) = 2 := by
  rw [closedPlaceTargetTwoSpace,
    LinearMap.finrank_range_of_inj
      (closedPlaceTargetTwoLinear_injective place)]
  simp

theorem rationalTwoSpace_le_targetTwoSpace :
    rationalTwoSpace ≤ targetTwoSpace := by
  rintro p ⟨c, hc, rfl⟩
  exact ⟨c, rfl⟩

/-- The rational two-form space has dimension three. -/
theorem rationalTwoSpace_finrank :
    Module.finrank F₂ rationalTwoSpace = 3 := by
  let f : rationalCoeffSpace →ₗ[F₂] TwoForm :=
    targetTwoLinear.domRestrict rationalCoeffSpace
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact targetTwo_injective hxy
  have hrange : LinearMap.range f = rationalTwoSpace := by
    ext p
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hf,
    rationalCoeffSpace_finrank]

theorem outsideHankelWord_eq_closedPlaceTargetCoeff (k : Fin 9) :
    outsideHankelWord k =
      closedPlaceTargetCoeff (outsideHankelPlace k)
        (outsideHankelTargetParam k) := by
  apply targetTwo_injective
  rw [targetTwo_outsideHankelWord,
    targetTwo_closedPlaceTargetCoeff,
    outsideHankelLocalCoord_eq_targetCoord]

theorem targetTwo_outsideHankelWord_mem_closedPlaceTargetTwoSpace
    (k : Fin 9) :
    targetTwo (outsideHankelWord k) ∈
      closedPlaceTargetTwoSpace (outsideHankelPlace k) := by
  rw [outsideHankelWord_eq_closedPlaceTargetCoeff]
  exact ⟨outsideHankelTargetParam k,
    closedPlaceTargetTwoLinear_apply _ _⟩

/-- A non-rational difference between two lifts of an effective closed-place
point has the same closed-place type as that point. -/
theorem outsideHankelPlace_eq_of_closedPlace_fiber
    (x : ClosedPlaceEffectiveParam) (k : Fin 9) (p p' : TwoForm)
    (hp : p ∈ decomposableFiber (closedPlaceEffectivePoint x))
    (hp' : p' ∈ decomposableFiber (closedPlaceEffectivePoint x))
    (hsum : targetTwo (outsideHankelWord k) = p + p') :
    outsideHankelPlace k = x.1 := by
  rcases hp.1 with ⟨u, v, huv⟩
  rcases hp'.1 with ⟨u', v', hu'v'⟩
  have hsecant : targetTwo (outsideHankelWord k) =
      squarefreeWedge u v + squarefreeWedge u' v' := by
    simpa [← huv, ← hu'v'] using hsum
  rcases outsideHankel_secant_localizes k u v u' v' hsecant with
    ⟨a, b, ha, hb, hab, hpa, hpb⟩
  have heffective := outsideHankel_localEffectiveParam k a b ha hb hab
  let y : ClosedPlaceEffectiveParam :=
    ⟨outsideHankelPlace k,
      ⟨closedPlaceQuotientParam (outsideHankelPlace k) a, heffective⟩⟩
  have hyx : closedPlaceEffectivePoint y = closedPlaceEffectivePoint x := by
    change closedPlaceQuotientPoint (outsideHankelPlace k)
        (closedPlaceQuotientParam (outsideHankelPlace k) a) =
      closedPlaceEffectivePoint x
    calc
      closedPlaceQuotientPoint (outsideHankelPlace k)
          (closedPlaceQuotientParam (outsideHankelPlace k) a) =
          quadraticQuotientProjection
            (localTwoForm (outsideHankelPlace k) a) :=
        (quadraticQuotientProjection_localTwoForm _ _).symm
      _ = quadraticQuotientProjection p := by
        apply congrArg quadraticQuotientProjection
        exact hpa.trans huv.symm
      _ = closedPlaceEffectivePoint x := hp.2
  have hy := closedPlaceEffectivePoint_injective hyx
  exact congrArg (fun z : ClosedPlaceEffectiveParam => z.1) hy

/-- A quotient point has a populated fiber if it admits a decomposable lift. -/
def IsPopulatedFiber (q : QuadraticQuotient) : Prop :=
  (decomposableFiber q).Nonempty

/-- Populated nonzero quotient points lying in a fixed defect subspace. -/
abbrev PopulatedPoint (Q : Submodule F₂ QuadraticQuotient) :=
  {q : Q // q.1 ≠ 0 ∧ IsPopulatedFiber q.1}

noncomputable instance populatedPointFintype
    (Q : Submodule F₂ QuadraticQuotient) : Fintype (PopulatedPoint Q) :=
  Fintype.ofFinite _

/-- The underlying quotient point of a populated point in `Q`. -/
def populatedQuotientPoint {Q : Submodule F₂ QuadraticQuotient}
    (q : PopulatedPoint Q) : QuadraticQuotient := q.1.1

/-- A canonical (choice-based) decomposable lift of a populated quotient
point.  All statements below are invariant under this choice because every
other lift differs by the corresponding fiber-difference space. -/
def populatedLift {Q : Submodule F₂ QuadraticQuotient}
    (q : PopulatedPoint Q) : TwoForm :=
  Classical.choose q.2.2

theorem populatedLift_mem_fiber {Q : Submodule F₂ QuadraticQuotient}
    (q : PopulatedPoint Q) :
    populatedLift q ∈ decomposableFiber (populatedQuotientPoint q) :=
  Classical.choose_spec q.2.2

@[simp] theorem populatedLift_projection
    {Q : Submodule F₂ QuadraticQuotient} (q : PopulatedPoint Q) :
    quadraticQuotientProjection (populatedLift q) =
      populatedQuotientPoint q :=
  (populatedLift_mem_fiber q).2

/-- Differences inside one populated fiber are target two-forms. -/
theorem fiberDifferenceSpace_le_targetTwoSpace
    {q : QuadraticQuotient} {base : TwoForm}
    (hbase : base ∈ decomposableFiber q) :
    fiberDifferenceSpace q base ≤ targetTwoSpace := by
  apply Submodule.span_le.mpr
  rintro d ⟨p, hp, rfl⟩
  apply (quadraticQuotientProjection_eq_zero_iff _).1
  rw [map_sub, hp.2, hbase.2, sub_self]

/-- The intrinsic difference space does not depend on the chosen base point
of a populated fiber. -/
theorem fiberDifferenceSpace_eq_of_bases
    {q : QuadraticQuotient} {base base' : TwoForm}
    (hbase : base ∈ decomposableFiber q)
    (hbase' : base' ∈ decomposableFiber q) :
    fiberDifferenceSpace q base = fiberDifferenceSpace q base' := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro d ⟨p, hp, rfl⟩
    have hp' : p - base' ∈ fiberDifferenceSpace q base' :=
      Submodule.subset_span ⟨p, hp, rfl⟩
    have hb' : base - base' ∈ fiberDifferenceSpace q base' :=
      Submodule.subset_span ⟨base, hbase, rfl⟩
    rw [show p - base = (p - base') - (base - base') by module]
    exact (fiberDifferenceSpace q base').sub_mem hp' hb'
  · apply Submodule.span_le.mpr
    rintro d ⟨p, hp, rfl⟩
    have hp' : p - base ∈ fiberDifferenceSpace q base :=
      Submodule.subset_span ⟨p, hp, rfl⟩
    have hb' : base' - base ∈ fiberDifferenceSpace q base :=
      Submodule.subset_span ⟨base', hbase', rfl⟩
    rw [show p - base' = (p - base) - (base' - base) by module]
    exact (fiberDifferenceSpace q base).sub_mem hp' hb'

/-- Every intrinsic difference of an effective closed-place fiber lies in the
rational space plus that place's local target plane. -/
theorem fiberDifferenceSpace_closedPlace_le
    (x : ClosedPlaceEffectiveParam) {base : TwoForm}
    (hbase : base ∈ decomposableFiber (closedPlaceEffectivePoint x)) :
    fiberDifferenceSpace (closedPlaceEffectivePoint x) base ≤
      rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1 := by
  apply Submodule.span_le.mpr
  rintro d ⟨p, hp, rfl⟩
  have hdT : p - base ∈ targetTwoSpace :=
    fiberDifferenceSpace_le_targetTwoSpace hbase
      (Submodule.subset_span ⟨p, hp, rfl⟩)
  rcases hdT with ⟨c, hc⟩
  change targetTwo c = p - base at hc
  by_cases hcR : c ∈ rationalCoeffSpace
  · apply (le_sup_left : rationalTwoSpace ≤
      rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1)
    exact ⟨c, hcR, hc⟩
  · have hrank : HankelRankLETwo c := by
      rcases hp.1 with ⟨u, v, huv⟩
      rcases hbase.1 with ⟨u', v', hu'v'⟩
      apply target_sum_two_decomposable_rankTwo
      calc
        targetTwo c = p - base := hc
        _ = p + base := twoForm_sub_eq_add p base
        _ = squarefreeWedge u v + squarefreeWedge u' v' := by
          rw [huv, hu'v']
    rcases exists_outsideHankelWord_of_rankTwo hrank hcR with ⟨k, hck⟩
    subst c
    have hsum : targetTwo (outsideHankelWord k) = p + base := by
      calc
        targetTwo (outsideHankelWord k) = p - base := hc
        _ = p + base := twoForm_sub_eq_add p base
    have hkplace := outsideHankelPlace_eq_of_closedPlace_fiber
      x k p base hp hbase hsum
    apply (le_sup_right : closedPlaceTargetTwoSpace x.1 ≤
      rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1)
    rw [← hc]
    simpa only [hkplace] using
      targetTwo_outsideHankelWord_mem_closedPlaceTargetTwoSpace k

/-- The rational space together with all intrinsic differences of populated
fibers in `Q`.  This is the manuscript space `D`. -/
def localDisplacementSpace (Q : Submodule F₂ QuadraticQuotient) :
    Submodule F₂ TwoForm :=
  rationalTwoSpace ⊔
    ⨆ q : PopulatedPoint Q,
      fiberDifferenceSpace (populatedQuotientPoint q) (populatedLift q)

theorem rationalTwoSpace_le_localDisplacementSpace
    (Q : Submodule F₂ QuadraticQuotient) :
    rationalTwoSpace ≤ localDisplacementSpace Q :=
  le_sup_left

theorem localDisplacementSpace_le_targetTwoSpace
    (Q : Submodule F₂ QuadraticQuotient) :
    localDisplacementSpace Q ≤ targetTwoSpace := by
  apply sup_le rationalTwoSpace_le_targetTwoSpace
  apply iSup_le
  intro q
  exact fiberDifferenceSpace_le_targetTwoSpace
    (populatedLift_mem_fiber q)

/-- The full decomposable span attached to a defect subspace. -/
def defectCapacitySpan (Q : Submodule F₂ QuadraticQuotient) :
    Submodule F₂ TwoForm :=
  localDisplacementSpace Q ⊔
    Submodule.span F₂ (Set.range (populatedLift (Q := Q)))

/-- Union of all populated nonzero fibers in a defect subspace. -/
def populatedFiberUnion (Q : Submodule F₂ QuadraticQuotient) : Set TwoForm :=
  {p | ∃ q : PopulatedPoint Q,
    p ∈ decomposableFiber (populatedQuotientPoint q)}

/-- Geometric form of the capacity span used in the manuscript definition. -/
def geometricCapacitySpan (Q : Submodule F₂ QuadraticQuotient) :
    Submodule F₂ TwoForm :=
  rationalTwoSpace ⊔ Submodule.span F₂ (populatedFiberUnion Q)

theorem fiberDifferenceSpace_le_populatedFiberSpan
    (Q : Submodule F₂ QuadraticQuotient) (q : PopulatedPoint Q) :
    fiberDifferenceSpace (populatedQuotientPoint q) (populatedLift q) ≤
      Submodule.span F₂ (populatedFiberUnion Q) := by
  apply Submodule.span_le.mpr
  rintro d ⟨p, hp, rfl⟩
  apply Submodule.sub_mem _
  · apply Submodule.subset_span
    exact ⟨q, hp⟩
  · apply Submodule.subset_span
    exact ⟨q, populatedLift_mem_fiber q⟩

theorem populatedLift_mem_populatedFiberSpan
    (Q : Submodule F₂ QuadraticQuotient) (q : PopulatedPoint Q) :
    populatedLift q ∈ Submodule.span F₂ (populatedFiberUnion Q) := by
  apply Submodule.subset_span
  exact ⟨q, populatedLift_mem_fiber q⟩

/-- The chosen-lift presentation is exactly the span of all populated fibers;
in particular the capacity construction is independent of every choice. -/
theorem defectCapacitySpan_eq_geometricCapacitySpan
    (Q : Submodule F₂ QuadraticQuotient) :
    defectCapacitySpan Q = geometricCapacitySpan Q := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact le_sup_left
      · apply iSup_le
        intro q
        exact (fiberDifferenceSpace_le_populatedFiberSpan Q q).trans
          le_sup_right
    · apply Submodule.span_le.mpr
      rintro p ⟨q, rfl⟩
      exact (le_sup_right :
        Submodule.span F₂ (populatedFiberUnion Q) ≤ geometricCapacitySpan Q)
        (populatedLift_mem_populatedFiberSpan Q q)
  · apply sup_le
    · exact le_sup_left.trans le_sup_left
    · apply Submodule.span_le.mpr
      rintro p ⟨q, hp⟩
      have hd : p - populatedLift q ∈
          fiberDifferenceSpace (populatedQuotientPoint q)
            (populatedLift q) :=
        Submodule.subset_span ⟨p, hp, rfl⟩
      have hdD : p - populatedLift q ∈ localDisplacementSpace Q :=
        ((le_iSup
            (fun q : PopulatedPoint Q =>
              fiberDifferenceSpace (populatedQuotientPoint q)
                (populatedLift q)) q).trans le_sup_right) hd
      have hlift : populatedLift q ∈
          Submodule.span F₂ (Set.range (populatedLift (Q := Q))) :=
        Submodule.subset_span ⟨q, rfl⟩
      have := (defectCapacitySpan Q).add_mem
        ((le_sup_left : localDisplacementSpace Q ≤ defectCapacitySpan Q) hdD)
        ((le_sup_right :
          Submodule.span F₂ (Set.range (populatedLift (Q := Q))) ≤
            defectCapacitySpan Q) hlift)
      rw [show p = (p - populatedLift q) + populatedLift q by module]
      exact this

/-- Target capacity of a defect subspace. -/
def targetCapacity (Q : Submodule F₂ QuadraticQuotient) : Nat :=
  Module.finrank F₂ ↑(targetTwoSpace ⊓ defectCapacitySpan Q)

/-- The exact relation map for the populated fibers of `Q`. -/
def defectRelationMap (Q : Submodule F₂ QuadraticQuotient) :
    relationKernel (populatedQuotientPoint (Q := Q)) →ₗ[F₂]
      (TwoForm ⧸ localDisplacementSpace Q) :=
  relationMap (localDisplacementSpace Q) (populatedLift (Q := Q))
    (populatedQuotientPoint (Q := Q))

/-- Intrinsic displacement beyond the three rational directions. -/
def displacementRank (Q : Submodule F₂ QuadraticQuotient) : Nat :=
  Module.finrank F₂ (localDisplacementSpace Q) - 3

/-- Target directions supplied by additive relations among populated fibers. -/
def relationGiftRank (Q : Submodule F₂ QuadraticQuotient) : Nat :=
  Module.finrank F₂ ↑(LinearMap.range (defectRelationMap Q))

theorem three_le_localDisplacement_finrank
    (Q : Submodule F₂ QuadraticQuotient) :
    3 ≤ Module.finrank F₂ (localDisplacementSpace Q) := by
  rw [← rationalTwoSpace_finrank]
  exact Submodule.finrank_mono
    (rationalTwoSpace_le_localDisplacementSpace Q)

theorem localDisplacement_finrank_eq (Q : Submodule F₂ QuadraticQuotient) :
    Module.finrank F₂ (localDisplacementSpace Q) =
      3 + displacementRank Q := by
  unfold displacementRank
  have h := three_le_localDisplacement_finrank Q
  omega

/-- Manuscript Theorem 3.2 specialized to the canonical populated-fiber data
of a defect subspace. -/
theorem targetCapacity_relationMap_formula
    (Q : Submodule F₂ QuadraticQuotient) :
    targetCapacity Q =
      Module.finrank F₂ (localDisplacementSpace Q) + relationGiftRank Q := by
  unfold targetCapacity relationGiftRank defectRelationMap
  exact relationMap_finrank
    (localDisplacementSpace Q) (defectCapacitySpan Q)
    (populatedLift (Q := Q)) (populatedQuotientPoint (Q := Q))
    (localDisplacementSpace_le_targetTwoSpace Q)
    populatedLift_projection rfl

/-- Exact capacity ledger in the manuscript notation
`rho(Q) = 3 + d + rank(lambda)`. -/
theorem targetCapacity_eq_three_add_displacement_add_gifts
    (Q : Submodule F₂ QuadraticQuotient) :
    targetCapacity Q = 3 + displacementRank Q + relationGiftRank Q := by
  rw [targetCapacity_relationMap_formula,
    localDisplacement_finrank_eq]

/-- Relation gifts cannot exceed the dimension of the additive relation
kernel.  This is the algebraic projection-kernel bound used before the sharper
closed-place displacement pivots. -/
theorem relationGiftRank_le_relationKernel
    (Q : Submodule F₂ QuadraticQuotient) :
    relationGiftRank Q ≤
      Module.finrank F₂
        ↑(relationKernel (populatedQuotientPoint (Q := Q))) := by
  exact (defectRelationMap Q).finrank_range_le

/-- Rank-nullity for the additive relation kernel, in the finite-family form
used by the capacity argument. -/
theorem relationKernel_finrank_add_span
    {X : Type*} [Fintype X] (q : X → QuadraticQuotient) :
    Module.finrank F₂ ↑(relationKernel q) +
        Module.finrank F₂ (Submodule.span F₂ (Set.range q)) =
      Fintype.card X := by
  have h := (coefficientSum q).finrank_range_add_finrank_ker
  rw [coefficientSum_range] at h
  calc
    Module.finrank F₂ ↑(relationKernel q) +
          Module.finrank F₂ (Submodule.span F₂ (Set.range q)) =
        Module.finrank F₂ (Submodule.span F₂ (Set.range q)) +
          Module.finrank F₂ ↑(relationKernel q) := by omega
    _ = Module.finrank F₂ (X → F₂) := h
    _ = Fintype.card X := by simp

theorem populatedQuotientPoint_injective
    (Q : Submodule F₂ QuadraticQuotient) :
    Function.Injective (populatedQuotientPoint (Q := Q)) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

/-- Independent populated quotient points have no relation gift. -/
theorem relationGiftRank_eq_zero_of_linearIndependent
    (Q : Submodule F₂ QuadraticQuotient)
    (hlin : LinearIndependent F₂
      (populatedQuotientPoint (Q := Q))) :
    relationGiftRank Q = 0 := by
  have hspan : Module.finrank F₂
      (Submodule.span F₂
        (Set.range (populatedQuotientPoint (Q := Q)))) =
      Fintype.card (PopulatedPoint Q) :=
    finrank_span_eq_card hlin
  have hkernel := relationKernel_finrank_add_span
    (populatedQuotientPoint (Q := Q))
  have hkzero : Module.finrank F₂
      ↑(relationKernel (populatedQuotientPoint (Q := Q))) = 0 := by
    omega
  have hgift := relationGiftRank_le_relationKernel Q
  omega

end

end N5
end UnrestrictedBooleanMul
