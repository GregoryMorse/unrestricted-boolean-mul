import UnrestrictedBooleanMul.N5.Displacement

/-!
# Closed-place displacement profiles

This module proves the local lower bounds complementary to the localization
theorem in `N5.Displacement`.  An effective doubled-rational fiber supplies
its one jet direction modulo the rational evaluation space, while an
effective degree-two fiber supplies its full two-dimensional target plane.

The proofs use the two-variable local Klein equations.  In particular, the
degree-two argument writes down the three points of the factored affine
binary conic; it performs no enumeration of ambient quadratic forms.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The span of all pairwise differences in a finite affine local fiber. -/
def localTargetDifferenceSpace (fiber : Finset LocalTargetParam) :
    Submodule F₂ LocalTargetParam :=
  Submodule.span F₂
    {d | ∃ z ∈ fiber, ∃ w ∈ fiber, d = z - w}

/-- The rational evaluation coordinate in a local target plane. -/
def localEvaluationParam : LocalTargetParam := ![1, 0]

/-- The first-jet coordinate in a local target plane. -/
def localJetParam : LocalTargetParam := ![0, 1]

/-- Effectiveness of a doubled-rational local fiber supplies the missing jet
direction, so its differences together with evaluation span the target
plane. -/
theorem rational_localTargetDifferenceSpace_sup_eq_top
    (q : LocalKleinParam) (hq : RationalLocalEffective q) :
    Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) ⊔
        localTargetDifferenceSpace (rationalKleinFiber q) = ⊤ := by
  rcases (rationalHasJetDifference_iff q).2 hq with
    ⟨z, hz, w, hw, hzw⟩
  let d : LocalTargetParam := z - w
  have hdmem : d ∈ localTargetDifferenceSpace (rationalKleinFiber q) :=
    Submodule.subset_span ⟨z, hz, w, hw, rfl⟩
  have hdne : d 1 ≠ 0 := by
    intro hd0
    apply hzw
    exact sub_eq_zero.mp (by simpa [d] using hd0)
  have hd1 : d 1 = 1 := by
    rcases f2_eq_zero_or_one (d 1) with hzero | hone
    · exact (hdne hzero).elim
    · exact hone
  apply top_unique
  intro t _
  have heval : localEvaluationParam ∈
      Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) :=
    Submodule.subset_span (by simp)
  have hevalSup : localEvaluationParam ∈
      Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) ⊔
        localTargetDifferenceSpace (rationalKleinFiber q) :=
    (le_sup_left :
      Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) ≤
        Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) ⊔
          localTargetDifferenceSpace (rationalKleinFiber q)) heval
  have hdSup : d ∈
      Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) ⊔
        localTargetDifferenceSpace (rationalKleinFiber q) :=
    (le_sup_right : localTargetDifferenceSpace (rationalKleinFiber q) ≤
      Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) ⊔
        localTargetDifferenceSpace (rationalKleinFiber q)) hdmem
  have hjetSup : d + d 0 • localEvaluationParam ∈
      Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) ⊔
        localTargetDifferenceSpace (rationalKleinFiber q) :=
    (Submodule.add_mem _ hdSup (Submodule.smul_mem _ _ hevalSup))
  have hjetEq : d + d 0 • localEvaluationParam = localJetParam := by
    funext i
    fin_cases i <;>
      simp [localEvaluationParam, localJetParam, hd1,
        CharTwo.add_self_eq_zero]
  have ht :
      t = t 0 • localEvaluationParam +
        t 1 • (d + d 0 • localEvaluationParam) := by
    rw [hjetEq]
    funext i
    fin_cases i <;> simp [localEvaluationParam, localJetParam]
  rw [ht]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ hevalSup)
    (Submodule.smul_mem _ _ hjetSup)

/-- The three points of an effective degree-two affine Klein fiber have
pairwise differences spanning its full two-dimensional target plane. -/
theorem degreeTwo_localTargetDifferenceSpace_eq_top
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q) :
    localTargetDifferenceSpace (degreeTwoKleinFiber q) = ⊤ := by
  unfold DegreeTwoLocalEffective at hq
  let z : LocalTargetParam := ![q 1 + 1, q 2 + 1]
  let zx : LocalTargetParam := ![q 1, q 2 + 1]
  let zy : LocalTargetParam := ![q 1 + 1, q 2]
  have hz : z ∈ degreeTwoKleinFiber q := by
    simp [degreeTwoKleinFiber, degreeTwoLocalPoint_klein_iff, z,
      hq]
    ring_nf
    simp only [N3Certificate.three_eq_one_f2, mul_one]
  have hzx : zx ∈ degreeTwoKleinFiber q := by
    simp [degreeTwoKleinFiber, degreeTwoLocalPoint_klein_iff, zx,
      hq]
    ring_nf
    simp only [N3Certificate.three_eq_one_f2, mul_one]
  have hzy : zy ∈ degreeTwoKleinFiber q := by
    simp [degreeTwoKleinFiber, degreeTwoLocalPoint_klein_iff, zy,
      hq]
    ring_nf
    simp only [N3Certificate.three_eq_one_f2, mul_one]
  have hxmem : zx - z ∈
      localTargetDifferenceSpace (degreeTwoKleinFiber q) :=
    Submodule.subset_span ⟨zx, hzx, z, hz, rfl⟩
  have hymem : zy - z ∈
      localTargetDifferenceSpace (degreeTwoKleinFiber q) :=
    Submodule.subset_span ⟨zy, hzy, z, hz, rfl⟩
  have hx : zx - z = localEvaluationParam := by
    funext i
    fin_cases i <;>
      simp [zx, z, localEvaluationParam]
  have hy : zy - z = localJetParam := by
    funext i
    fin_cases i <;>
      simp [zy, z, localJetParam]
  apply top_unique
  intro t _
  have heval : localEvaluationParam ∈
      localTargetDifferenceSpace (degreeTwoKleinFiber q) := by
    rwa [← hx]
  have hjet : localJetParam ∈
      localTargetDifferenceSpace (degreeTwoKleinFiber q) := by
    rwa [← hy]
  have ht : t = t 0 • localEvaluationParam + t 1 • localJetParam := by
    funext i
    fin_cases i <;> simp [localEvaluationParam, localJetParam]
  rw [ht]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ heval)
    (Submodule.smul_mem _ _ hjet)

/-! ## Transport from local Klein coordinates to ambient two-forms -/

/-- A pairwise local target difference is an intrinsic difference in the
corresponding global decomposable fiber, independently of the chosen base. -/
theorem closedPlaceTargetTwoLinear_sub_mem_fiberDifference
    (place : Fin 4) (q : LocalKleinParam) (z w : LocalTargetParam)
    (hz : SatisfiesKlein (closedPlaceLocalPoint place q z))
    (hw : SatisfiesKlein (closedPlaceLocalPoint place q w))
    {base : TwoForm}
    (hbase : base ∈ decomposableFiber (closedPlaceQuotientPoint place q)) :
    closedPlaceTargetTwoLinear place (z - w) ∈
      fiberDifferenceSpace (closedPlaceQuotientPoint place q) base := by
  let pz : TwoForm := localTwoForm place (closedPlaceLocalPoint place q z)
  let pw : TwoForm := localTwoForm place (closedPlaceLocalPoint place q w)
  have hpz : pz ∈ decomposableFiber (closedPlaceQuotientPoint place q) := by
    refine ⟨localTwoForm_decomposable_of_satisfiesKlein _ _ hz, ?_⟩
    dsimp [pz]
    rw [quadraticQuotientProjection_localTwoForm,
      closedPlaceQuotientParam_localPoint]
  have hpw : pw ∈ decomposableFiber (closedPlaceQuotientPoint place q) := by
    refine ⟨localTwoForm_decomposable_of_satisfiesKlein _ _ hw, ?_⟩
    dsimp [pw]
    rw [quadraticQuotientProjection_localTwoForm,
      closedPlaceQuotientParam_localPoint]
  rw [fiberDifferenceSpace_eq_of_bases hbase hpw]
  apply Submodule.subset_span
  refine ⟨pz, hpz, ?_⟩
  dsimp [pz, pw]
  have htargetSub : z - w = z + w := by
    funext i
    exact CharTwo.sub_eq_add (z i) (w i)
  have hlocalSub :
      closedPlaceLocalPoint place q z - closedPlaceLocalPoint place q w =
        closedPlaceLocalPoint place q z + closedPlaceLocalPoint place q w := by
    funext i
    exact CharTwo.sub_eq_add
      ((closedPlaceLocalPoint place q z) i)
      ((closedPlaceLocalPoint place q w) i)
  calc
    closedPlaceTargetTwoLinear place (z - w) =
        localTwoForm place (closedPlaceTargetCoord place (z - w)) := by
      rw [closedPlaceTargetTwoLinear_apply,
        targetTwo_closedPlaceTargetCoeff]
    _ = localTwoForm place
        (closedPlaceLocalPoint place q z -
          closedPlaceLocalPoint place q w) := by
      apply congrArg (localTwoForm place)
      rw [htargetSub, hlocalSub, closedPlaceLocalPoint_add]
    _ = localTwoForm place (closedPlaceLocalPoint place q z) -
        localTwoForm place (closedPlaceLocalPoint place q w) :=
      (localTwoFormLinear place).map_sub _ _

/-- Mapping all local pairwise differences into ambient two-forms lands in
the intrinsic global fiber-difference space. -/
theorem closedPlaceTargetTwoLinear_map_localDifference_le
    (place : Fin 4) (q : LocalKleinParam) (fiber : Finset LocalTargetParam)
    (hfiber : ∀ z ∈ fiber,
      SatisfiesKlein (closedPlaceLocalPoint place q z))
    {base : TwoForm}
    (hbase : base ∈ decomposableFiber (closedPlaceQuotientPoint place q)) :
    (localTargetDifferenceSpace fiber).map
        (closedPlaceTargetTwoLinear place) ≤
      fiberDifferenceSpace (closedPlaceQuotientPoint place q) base := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro d ⟨z, hz, w, hw, rfl⟩
  exact closedPlaceTargetTwoLinear_sub_mem_fiberDifference place q z w
    (hfiber z hz) (hfiber w hw) hbase

/-- At a rational closed place, the local evaluation coordinate is one of
the three global rational evaluation directions. -/
theorem rational_closedPlaceTargetTwoLinear_evaluation_mem
    (place : Fin 3) :
    closedPlaceTargetTwoLinear place.castSucc localEvaluationParam ∈
      rationalTwoSpace := by
  fin_cases place
  · refine ⟨rZeroCoeff,
      Submodule.subset_span (Set.mem_insert _ _), ?_⟩
    simp [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
      localEvaluationParam]
    rfl
  · refine ⟨rOneCoeff,
      Submodule.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), ?_⟩
    simp [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
      localEvaluationParam]
    rfl
  · refine ⟨rInfinityCoeff,
      Submodule.subset_span
        (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_⟩
    simp [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
      localEvaluationParam]
    rfl

/-- Exact ambient profile of one effective doubled-rational fiber: modulo
the rational evaluation space it supplies precisely its one jet line. -/
theorem rational_fiberDifference_profile
    (place : Fin 3) (q : LocalKleinParam)
    (hq : RationalLocalEffective q) {base : TwoForm}
    (hbase : base ∈
      decomposableFiber (closedPlaceQuotientPoint place.castSucc q)) :
    rationalTwoSpace ⊔
        fiberDifferenceSpace
          (closedPlaceQuotientPoint place.castSucc q) base =
      rationalTwoSpace ⊔ closedPlaceTargetTwoSpace place.castSucc := by
  apply le_antisymm
  · exact sup_le le_sup_left
      ((fiberDifferenceSpace_closedPlace_le
        ⟨place.castSucc,
          ⟨q, (mem_effectiveParamsAt_rational place.castSucc
            (by
              intro h
              have hv := congrArg Fin.val h
              have hp := place.isLt
              simp at hv
              omega) q).2 hq⟩⟩ hbase).trans
        (sup_le le_sup_left le_sup_right))
  · apply sup_le le_sup_left
    rintro p ⟨t, rfl⟩
    have hlocal := rational_localTargetDifferenceSpace_sup_eq_top q hq
    have ht : t ∈
        Submodule.span F₂ ({localEvaluationParam} : Set LocalTargetParam) ⊔
          localTargetDifferenceSpace (rationalKleinFiber q) := by
      rw [hlocal]
      trivial
    rcases Submodule.mem_sup.mp ht with ⟨e, he, d, hd, rfl⟩
    rw [(closedPlaceTargetTwoLinear place.castSucc).map_add]
    apply Submodule.add_mem _
    · apply (le_sup_left : rationalTwoSpace ≤
        rationalTwoSpace ⊔ fiberDifferenceSpace
          (closedPlaceQuotientPoint place.castSucc q) base)
      refine Submodule.span_induction (p := fun e _ =>
        closedPlaceTargetTwoLinear place.castSucc e ∈ rationalTwoSpace)
        ?_ ?_ ?_ ?_ he
      · intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact rational_closedPlaceTargetTwoLinear_evaluation_mem place
      · exact (closedPlaceTargetTwoLinear place.castSucc).map_zero ▸
          Submodule.zero_mem _
      · intro x y _ _ hx hy
        rw [(closedPlaceTargetTwoLinear place.castSucc).map_add]
        exact Submodule.add_mem _ hx hy
      · intro a x _ hx
        rw [(closedPlaceTargetTwoLinear place.castSucc).map_smul]
        exact Submodule.smul_mem _ _ hx
    · apply (le_sup_right :
        fiberDifferenceSpace
          (closedPlaceQuotientPoint place.castSucc q) base ≤
        rationalTwoSpace ⊔ fiberDifferenceSpace
          (closedPlaceQuotientPoint place.castSucc q) base)
      have hmap := closedPlaceTargetTwoLinear_map_localDifference_le
        place.castSucc q (rationalKleinFiber q) (fun z hz => by
          fin_cases place <;>
            simpa [closedPlaceLocalPoint, rationalKleinFiber] using hz) hbase
      exact hmap ⟨d, hd, rfl⟩

/-- Exact ambient profile of one effective degree-two fiber: its intrinsic
differences supply the full two-dimensional degree-two target plane. -/
theorem degreeTwo_fiberDifference_profile
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    {base : TwoForm}
    (hbase : base ∈ decomposableFiber (closedPlaceQuotientPoint 3 q)) :
    rationalTwoSpace ⊔
        fiberDifferenceSpace (closedPlaceQuotientPoint 3 q) base =
      rationalTwoSpace ⊔ closedPlaceTargetTwoSpace 3 := by
  apply le_antisymm
  · exact sup_le le_sup_left
      ((fiberDifferenceSpace_closedPlace_le
        ⟨3, ⟨q, (mem_effectiveParamsAt_degreeTwo q).2 hq⟩⟩ hbase).trans
        (sup_le le_sup_left le_sup_right))
  · apply sup_le le_sup_left
    rintro p ⟨t, rfl⟩
    apply (le_sup_right :
      fiberDifferenceSpace (closedPlaceQuotientPoint 3 q) base ≤
        rationalTwoSpace ⊔
          fiberDifferenceSpace (closedPlaceQuotientPoint 3 q) base)
    have hmap := closedPlaceTargetTwoLinear_map_localDifference_le
      3 q (degreeTwoKleinFiber q) (fun z hz => by
        simpa [closedPlaceLocalPoint, degreeTwoKleinFiber] using hz) hbase
    apply hmap
    refine ⟨t, ?_, rfl⟩
    rw [degreeTwo_localTargetDifferenceSpace_eq_top q hq]
    trivial

/-! ## The global represented-place profile -/

theorem closedPlaceQuotientPoint_injective (place : Fin 4) :
    Function.Injective (closedPlaceQuotientPoint place) := by
  intro q r hqr
  have hcoeff :=
    (closedPlaceQuotientPoint_eq_iff_atlasCoefficient_eq
      place place q r).1 hqr
  funext i
  have hi := congrFun hcoeff (place, i)
  simpa [atlasCoefficient] using hi

theorem closedPlaceQuotientPoint_ne_zero (place : Fin 4)
    {q : LocalKleinParam} (hq : q ≠ 0) :
    closedPlaceQuotientPoint place q ≠ 0 := by
  intro hzero
  have hzeroPoint : closedPlaceQuotientPoint place
      (0 : LocalKleinParam) = 0 := by
    unfold closedPlaceQuotientPoint
    rw [closedPlaceLift_basis_sum]
    simp
  apply hq
  exact closedPlaceQuotientPoint_injective place
    (hzero.trans hzeroPoint.symm)

theorem closedPlaceEffectivePoint_effective
    (x : ClosedPlaceEffectiveParam) :
    IsEffectiveFiber (closedPlaceEffectivePoint x) := by
  classical
  apply effectiveFiber_of_mem_atlas
  rw [effectiveFiberAtlas, Finset.mem_image]
  exact ⟨x, Finset.mem_univ _, rfl⟩

theorem closedPlaceEffectivePoint_populated
    (x : ClosedPlaceEffectiveParam) :
    IsPopulatedFiber (closedPlaceEffectivePoint x) := by
  rcases closedPlaceEffectivePoint_effective x with
    ⟨p, p', hp, hp', c, hc, hsum⟩
  exact ⟨p, hp⟩

/-- If a populated fiber is not effective, all of its intrinsic differences
are rational evaluation directions. -/
theorem fiberDifferenceSpace_le_rational_of_not_effective
    {q : QuadraticQuotient} {base : TwoForm}
    (hbase : base ∈ decomposableFiber q)
    (hneff : ¬ IsEffectiveFiber q) :
    fiberDifferenceSpace q base ≤ rationalTwoSpace := by
  apply Submodule.span_le.mpr
  rintro d ⟨p, hp, rfl⟩
  have hdT := fiberDifferenceSpace_le_targetTwoSpace hbase
    (Submodule.subset_span ⟨p, hp, rfl⟩)
  rcases hdT with ⟨c, hc⟩
  have hcR : c ∈ rationalCoeffSpace := by
    by_contra hcout
    apply hneff
    refine ⟨p, base, hp, hbase, c, hcout, ?_⟩
    calc
      targetTwo c = p - base := hc
      _ = p + base := by
        funext i
        exact CharTwo.sub_eq_add (p i) (base i)
  exact ⟨c, hcR, hc⟩

/-- A closed place is represented in `Q` when one of its effective quotient
points lies in `Q`. -/
def IsRepresentedPlace (Q : Submodule F₂ QuadraticQuotient)
    (place : Fin 4) : Prop :=
  ∃ q : EffectiveParamAt place,
    closedPlaceQuotientPoint place q.1 ∈ Q

/-- Sum of the target planes of all effective place types represented in
`Q`. -/
def representedPlaceTargetSpace
    (Q : Submodule F₂ QuadraticQuotient) : Submodule F₂ TwoForm :=
  ⨆ place : Fin 4, ⨆ _h : IsRepresentedPlace Q place,
    closedPlaceTargetTwoSpace place

theorem representedPlaceTargetSpace_le_targetTwoSpace
    (Q : Submodule F₂ QuadraticQuotient) :
    representedPlaceTargetSpace Q ≤ targetTwoSpace := by
  apply iSup_le
  intro place
  apply iSup_le
  intro h
  rintro p ⟨z, rfl⟩
  rw [closedPlaceTargetTwoLinear_apply]
  exact targetTwo_mem_targetTwoSpace
    (closedPlaceTargetCoeff place z)

/-- Uniform exact profile for any of the 43 effective closed-place fibers. -/
theorem closedPlaceEffective_fiberDifference_profile
    (x : ClosedPlaceEffectiveParam) {base : TwoForm}
    (hbase : base ∈ decomposableFiber (closedPlaceEffectivePoint x)) :
    rationalTwoSpace ⊔
        fiberDifferenceSpace (closedPlaceEffectivePoint x) base =
      rationalTwoSpace ⊔ closedPlaceTargetTwoSpace x.1 := by
  rcases x with ⟨place, ⟨q, hq⟩⟩
  fin_cases place
  · exact rational_fiberDifference_profile 0 q
      ((mem_effectiveParamsAt_rational 0 (by decide) q).1 hq) hbase
  · exact rational_fiberDifference_profile 1 q
      ((mem_effectiveParamsAt_rational 1 (by decide) q).1 hq) hbase
  · exact rational_fiberDifference_profile 2 q
      ((mem_effectiveParamsAt_rational 2 (by decide) q).1 hq) hbase
  · exact degreeTwo_fiberDifference_profile q
      ((mem_effectiveParamsAt_degreeTwo q).1 hq) hbase

/-- The intrinsic displacement space is exactly the rational evaluation
space plus the target planes of the effective closed places represented in
`Q`.  Thus ineffective populated fibers contribute no displacement, and
multiple effective points of the same place contribute only once. -/
theorem localDisplacementSpace_eq_representedPlaceProfile
    (Q : Submodule F₂ QuadraticQuotient) :
    localDisplacementSpace Q =
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q := by
  classical
  apply le_antisymm
  · apply sup_le le_sup_left
    apply iSup_le
    intro q
    by_cases heff : IsEffectiveFiber (populatedQuotientPoint q)
    · have hmem := effectiveFiber_mem_atlas heff
      rw [effectiveFiberAtlas, Finset.mem_image] at hmem
      rcases hmem with ⟨x, _hxuniv, hx⟩
      have hxQ : closedPlaceEffectivePoint x ∈ Q := by
        rw [hx]
        exact q.1.2
      have hrepresented : IsRepresentedPlace Q x.1 :=
        ⟨x.2, hxQ⟩
      have hbase : populatedLift q ∈
          decomposableFiber (closedPlaceEffectivePoint x) := by
        rw [hx]
        exact populatedLift_mem_fiber q
      have hfiber := fiberDifferenceSpace_closedPlace_le x hbase
      rw [← hx]
      apply hfiber.trans
      apply sup_le le_sup_left
      exact (((le_iSup
        (fun _h : IsRepresentedPlace Q x.1 =>
          closedPlaceTargetTwoSpace x.1) hrepresented).trans
        (le_iSup
          (fun place : Fin 4 =>
            ⨆ _h : IsRepresentedPlace Q place,
              closedPlaceTargetTwoSpace place) x.1)).trans le_sup_right)
    · exact (fiberDifferenceSpace_le_rational_of_not_effective
        (populatedLift_mem_fiber q) heff).trans le_sup_left
  · apply sup_le (rationalTwoSpace_le_localDisplacementSpace Q)
    apply iSup_le
    intro place
    apply iSup_le
    intro hrepresented
    rcases hrepresented with ⟨q, hqQ⟩
    let x : ClosedPlaceEffectiveParam := ⟨place, q⟩
    have hxne : closedPlaceEffectivePoint x ≠ 0 := by
      exact closedPlaceQuotientPoint_ne_zero place
        (effectiveParamsAt_ne_zero place q.2)
    have hxpop : IsPopulatedFiber (closedPlaceEffectivePoint x) :=
      closedPlaceEffectivePoint_populated x
    let pq : PopulatedPoint Q :=
      ⟨⟨closedPlaceEffectivePoint x, hqQ⟩, hxne, hxpop⟩
    have hpqbase : populatedLift pq ∈
        decomposableFiber (closedPlaceEffectivePoint x) := by
      exact populatedLift_mem_fiber pq
    have hprofile :=
      closedPlaceEffective_fiberDifference_profile x hpqbase
    have hfiberD :
        fiberDifferenceSpace (closedPlaceEffectivePoint x)
            (populatedLift pq) ≤ localDisplacementSpace Q := by
      exact ((le_iSup
        (fun q : PopulatedPoint Q =>
          fiberDifferenceSpace (populatedQuotientPoint q)
            (populatedLift q)) pq).trans le_sup_right)
    have hplane : closedPlaceTargetTwoSpace place ≤
        rationalTwoSpace ⊔
          fiberDifferenceSpace (closedPlaceEffectivePoint x)
            (populatedLift pq) := by
      rw [hprofile]
      exact le_sup_right
    exact hplane.trans
      (sup_le (rationalTwoSpace_le_localDisplacementSpace Q) hfiberD)

end

end N5
end UnrestrictedBooleanMul
