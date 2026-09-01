import UnrestrictedBooleanMul.N5.PointedFanoRelations
import UnrestrictedBooleanMul.N5.RationalSecantSymmetry

/-!
# Symmetry-complete degree-two secant pivots

Translation fixes the degree-two closed place.  Applying it to the local
rank-four secant equation supplies a fourth independent coefficient pivot.
Together with the original three norm-block pivots, this leaves exactly the
five intrinsic degree-two local directions.  Consequently all pointed line
gifts vanish after quotienting by intrinsic displacement.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def strongDegreeTwoSecantConstraint :
    TargetCoeff →ₗ[F₂] (Fin 4 → F₂) where
  toFun c := ![
    c 1 + c 2 + c 4 + c 5,
    c 1 + c 3 + c 4 + c 6,
    c 1 + c 7,
    c 2 + c 5]
  map_add' c d := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a c := by ext i; fin_cases i <;> simp [mul_add]

def strongDegreeTwoSecantCoeffSpace : Submodule F₂ TargetCoeff :=
  LinearMap.ker strongDegreeTwoSecantConstraint

def strongDegreeTwoSecantConstraintSection :
    (Fin 4 → F₂) →ₗ[F₂] TargetCoeff where
  toFun t := ![0, t 2, t 3, t 0 + t 1 + t 3,
    t 0 + t 2 + t 3, 0, 0, 0, 0]
  map_add' t u := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a t := by ext i; fin_cases i <;> simp [mul_add]

theorem strongDegreeTwoSecantConstraint_section (t : Fin 4 → F₂) :
    strongDegreeTwoSecantConstraint
        (strongDegreeTwoSecantConstraintSection t) = t := by
  ext i
  fin_cases i <;>
    simp [strongDegreeTwoSecantConstraint,
      strongDegreeTwoSecantConstraintSection] <;>
    ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.three_eq_one_f2,
      N3Certificate.four_eq_zero_f2]

theorem strongDegreeTwoSecantConstraint_surjective :
    Function.Surjective strongDegreeTwoSecantConstraint := by
  intro t
  exact ⟨strongDegreeTwoSecantConstraintSection t,
    strongDegreeTwoSecantConstraint_section t⟩

theorem strongDegreeTwoSecantCoeffSpace_finrank :
    Module.finrank F₂ strongDegreeTwoSecantCoeffSpace = 5 := by
  have h := strongDegreeTwoSecantConstraint.finrank_range_add_finrank_ker
  have hrange : LinearMap.range strongDegreeTwoSecantConstraint = ⊤ :=
    LinearMap.range_eq_top.mpr strongDegreeTwoSecantConstraint_surjective
  rw [hrange] at h
  have h' : 4 + Module.finrank F₂
      (LinearMap.ker strongDegreeTwoSecantConstraint) = 9 := by
    simpa [TargetCoeff] using h
  change Module.finrank F₂
    (LinearMap.ker strongDegreeTwoSecantConstraint) = 5
  omega

theorem degreeTwoLocalCoeffSpace_le_strongSecant :
    degreeTwoLocalCoeffSpace ≤ strongDegreeTwoSecantCoeffSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change strongDegreeTwoSecantConstraint
      (degreeTwoLocalCoeffDirection i) = 0
  fin_cases i <;> ext k <;> fin_cases k <;> decide

/-- Transport a normalized degree-two secant.  The canonical degree-two
section acquires the displayed intrinsic target correction. -/
theorem transport_normalizedDegreeTwoSecant
    (θ : Fin 2) (q : LocalKleinParam) (c : TargetCoeff)
    (hsecant : ∃ u v y z : LinearForm,
      closedPlaceLift 3 q + targetTwo c =
        squarefreeWedge u v + squarefreeWedge y z) :
    ∃ u v y z : LinearForm,
      closedPlaceLift 3 (degreeTwoSymmetryParam q) +
          targetTwo (closedPlaceTargetCoeff 3
              (degreeTwoSymmetryTarget θ q) +
            rationalTargetCoeffChange θ c) =
        squarefreeWedge u v + squarefreeWedge y z := by
  rcases hsecant with ⟨u, v, y, z, hsecant⟩
  have htransport := congrArg (rationalPlaceTwoFormLinear θ) hsecant
  refine ⟨rationalPlaceLinear θ u, rationalPlaceLinear θ v,
    rationalPlaceLinear θ y, rationalPlaceLinear θ z, ?_⟩
  change closedPlaceLift 3 (degreeTwoSymmetryParam q) +
      targetTwoLinear (closedPlaceTargetCoeff 3
        (degreeTwoSymmetryTarget θ q) + rationalTargetCoeffChange θ c) = _
  rw [targetTwoLinear.map_add, ← add_assoc]
  simp only [map_add, rationalPlaceTwoFormLinear_degreeTwoLift,
    rationalPlaceTwoFormLinear_targetTwo,
    rationalPlaceTwoFormLinear_squarefreeWedge'] at htransport
  change (closedPlaceLift 3 (degreeTwoSymmetryParam q) +
      targetTwoLinear (closedPlaceTargetCoeff 3
        (degreeTwoSymmetryTarget θ q))) +
      targetTwoLinear (rationalTargetCoeffChange θ c) = _ at htransport
  exact htransport

theorem transformed_normalizedDegreeTwoSecant_mem
    (θ : Fin 2) (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    (c : TargetCoeff)
    (hsecant : ∃ u v y z : LinearForm,
      closedPlaceLift 3 q + targetTwo c =
        squarefreeWedge u v + squarefreeWedge y z) :
    closedPlaceTargetCoeff 3 (degreeTwoSymmetryTarget θ q) +
        rationalTargetCoeffChange θ c ∈ degreeTwoSecantCoeffSpace := by
  have hq' := degreeTwoSymmetryParam_effective q hq
  exact degreeTwo_normalizedLocalSecant_mem
    (degreeTwoSymmetryParam q) hq'
    (closedPlaceTargetCoeff 3 (degreeTwoSymmetryTarget θ q) +
      rationalTargetCoeffChange θ c)
    (transport_normalizedDegreeTwoSecant θ q c hsecant)

/-- The translated fourth pivot for a degree-two pointed line gift. -/
theorem rationalTranslation_fanoLine_degreeTwo_gift_mem
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support)
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    (hxPoint : populatedQuotientPoint x = closedPlaceQuotientPoint 3 q) :
    rationalTargetCoeffChange 0 (sparseRelationGiftCoeff Q r.1) ∈
      degreeTwoSecantCoeffSpace := by
  let g := sparseRelationGiftCoeff Q r.1
  let d := closedPlaceTargetCoeff 3 (degreeTwoSymmetryTarget 0 q)
  have hxProjection : quadraticQuotientProjection (populatedLift x) =
      closedPlaceQuotientPoint 3 q :=
    (populatedLift_projection x).trans hxPoint
  rcases exists_closedPlaceLift_add_target_of_projection_eq
      3 q (populatedLift x) hxProjection with ⟨a, ha⟩
  have haSecant : ∃ u v y z : LinearForm,
      closedPlaceLift 3 q + targetTwo a =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases (populatedLift_mem_fiber x).1 with ⟨u, v, huv⟩
    refine ⟨u, v, 0, 0, ?_⟩
    rw [← ha, huv]
    simp
  have haMem : d + rationalTargetCoeffChange 0 a ∈
      degreeTwoSecantCoeffSpace :=
    transformed_normalizedDegreeTwoSecant_mem 0 q hq a haSecant
  have hagSecant : ∃ u v y z : LinearForm,
      closedPlaceLift 3 q + targetTwo (a + g) =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases fanoLine_gift_has_two_wedge_secant Q r x hx with
      ⟨u, v, y, z, hline⟩
    refine ⟨u, v, y, z, ?_⟩
    change closedPlaceLift 3 q + targetTwoLinear (a + g) = _
    rw [targetTwoLinear.map_add, ← add_assoc]
    change populatedLift x = closedPlaceLift 3 q + targetTwoLinear a at ha
    rw [← ha]
    change populatedLift x +
      targetTwoLinear (sparseRelationGiftCoeff Q r.1) = _ at hline
    simpa only [g] using hline
  have hagMem : d + rationalTargetCoeffChange 0 (a + g) ∈
      degreeTwoSecantCoeffSpace :=
    transformed_normalizedDegreeTwoSecant_mem 0 q hq (a + g) hagSecant
  have hsum := degreeTwoSecantCoeffSpace.add_mem hagMem haMem
  have hcancel :
      (d + rationalTargetCoeffChange 0 (a + g)) +
          (d + rationalTargetCoeffChange 0 a) =
        rationalTargetCoeffChange 0 g := by
    rw [show rationalTargetCoeffChange 0 (a + g) =
        rationalTargetCoeffChange 0 a + rationalTargetCoeffChange 0 g by
      exact (rationalTargetCoeffLinear 0).map_add a g]
    funext i
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2]
  rw [hcancel] at hsum
  exact hsum

theorem fanoLine_strongDegreeTwo_gift_mem
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support)
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    (hxPoint : populatedQuotientPoint x = closedPlaceQuotientPoint 3 q) :
    sparseRelationGiftCoeff Q r.1 ∈ strongDegreeTwoSecantCoeffSpace := by
  have hb := fanoLine_degreeTwo_gift_mem Q r x hx q hq hxPoint
  have he := rationalTranslation_fanoLine_degreeTwo_gift_mem
    Q r x hx q hq hxPoint
  change degreeTwoSecantConstraint (sparseRelationGiftCoeff Q r.1) = 0 at hb
  change degreeTwoSecantConstraint
    (rationalTargetCoeffChange 0 (sparseRelationGiftCoeff Q r.1)) = 0 at he
  change strongDegreeTwoSecantConstraint
    (sparseRelationGiftCoeff Q r.1) = 0
  ext i
  fin_cases i
  · simpa [strongDegreeTwoSecantConstraint,
      degreeTwoSecantConstraint] using congrFun hb 0
  · simpa [strongDegreeTwoSecantConstraint,
      degreeTwoSecantConstraint] using congrFun hb 1
  · simpa [strongDegreeTwoSecantConstraint,
      degreeTwoSecantConstraint] using congrFun hb 2
  · have h := congrFun he 0
    simp [degreeTwoSecantConstraint, rationalTargetCoeffChange] at h
    change sparseRelationGiftCoeff Q r.1 2 +
      sparseRelationGiftCoeff Q r.1 5 = 0
    ring_nf at h ⊢
    simpa [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2] using h

theorem fanoLineGiftCoeffSpaceThrough_strongDegreeTwo_le
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q)
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    (hxPoint : populatedQuotientPoint x = closedPlaceQuotientPoint 3 q) :
    fanoLineGiftCoeffSpaceThrough Q x ≤ strongDegreeTwoSecantCoeffSpace := by
  apply Submodule.span_le.mpr
  rintro c ⟨r, hx, rfl⟩
  exact fanoLine_strongDegreeTwo_gift_mem Q r x hx q hq hxPoint

/-- All degree-two pointed line gifts are intrinsic displacement. -/
theorem fanoLineGiftCoeffSpaceThrough_strongDegreeTwo_quotientRank_eq_zero
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q)
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    (hxPoint : populatedQuotientPoint x = closedPlaceQuotientPoint 3 q)
    (hdegree : IsRepresentedPlace Q 3) :
    Module.finrank F₂ (LinearMap.range
        ((Submodule.mkQ (localDisplacementCoeffSpace Q)).domRestrict
          (fanoLineGiftCoeffSpaceThrough Q x))) = 0 := by
  have hle : strongDegreeTwoSecantCoeffSpace ≤
      localDisplacementCoeffSpace Q := by
    have hlocal := degreeTwoLocalCoeffSpace_le_localDisplacementCoeffSpace
      Q hdegree
    have heq : degreeTwoLocalCoeffSpace =
        strongDegreeTwoSecantCoeffSpace :=
      Submodule.eq_of_le_of_finrank_eq degreeTwoLocalCoeffSpace_le_strongSecant
        (by rw [degreeTwoLocalCoeffSpace_finrank,
          strongDegreeTwoSecantCoeffSpace_finrank])
    rw [← heq]
    exact hlocal
  have hline : fanoLineGiftCoeffSpaceThrough Q x ≤
      localDisplacementCoeffSpace Q :=
    (fanoLineGiftCoeffSpaceThrough_strongDegreeTwo_le
      Q x q hq hxPoint).trans hle
  let f := (Submodule.mkQ (localDisplacementCoeffSpace Q)).domRestrict
    (fanoLineGiftCoeffSpaceThrough Q x)
  have hf : f = 0 := by
    ext c
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact hline c.2
  have hrange : LinearMap.range f = ⊥ := by
    rw [LinearMap.range_eq_bot]
    exact hf
  change Module.finrank F₂ (LinearMap.range f) = 0
  rw [hrange]
  simp

/-- A represented degree-two place forces total relation-gift rank at most
one. -/
theorem relationGiftRank_le_one_of_represented_degreeTwo
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hdegree : IsRepresentedPlace Q 3) :
    relationGiftRank Q ≤ 1 := by
  let p := representedClosedPlaceParam Q 3 hdegree
  let q : LocalKleinParam := p.2.1
  have hq : DegreeTwoLocalEffective q := by
    have hm := p.2.2
    change q ∈ effectiveParamsAt 3 at hm
    rw [effectiveParamsAt, if_pos rfl] at hm
    simpa [degreeTwoEffectiveParams] using hm
  let x := representedPopulatedPoint Q 3 hdegree
  have hgift :=
    relationGiftRank_le_lineQuotientRank_add_one_of_finrank_le_three
      Q hQ x
  have hline :=
    fanoLineGiftCoeffSpaceThrough_strongDegreeTwo_quotientRank_eq_zero
      Q x q hq (by rfl) hdegree
  change Module.finrank F₂
      (fanoLineGiftQuotientSpaceThrough Q x) = 0 at hline
  omega

end

end N5
end UnrestrictedBooleanMul
