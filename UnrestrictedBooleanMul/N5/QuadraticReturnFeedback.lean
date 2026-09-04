import UnrestrictedBooleanMul.N5.QuadraticReturnOrbit
import UnrestrictedBooleanMul.N5.QuadraticFlattening
import UnrestrictedBooleanMul.N5.RankOneEnvelopeCorrection

/-!
# Rank-one feedback against a quadratic return section

The old rank-one absorption theorem was stated for a target-clean space plus
one decomposable anchor.  A post-high quadratic return need not have a
decomposable representative.  What the absorption proof actually consumes is
the target-intersection identity: the quadratic section contains no new
Hankel target direction.  This module records that stronger and correctly
scoped interface.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem twoForm_add_self (p : TwoForm) : p + p = 0 := by
  funext s
  exact CharTwo.add_self_eq_zero (p s)

private theorem ambientWedgeTwo_add_left_local (p q r : TwoForm) :
    ambientWedgeTwo (p + q) r =
      ambientWedgeTwo p r + ambientWedgeTwo q r := by
  funext i j k l
  simp only [ambientWedgeTwo, ambientTwoCoeff_add, Pi.add_apply]
  ring

private theorem ambientWedgeTwo_comm_local (p q : TwoForm) :
    ambientWedgeTwo p q = ambientWedgeTwo q p := by
  funext i j k l
  simp only [ambientWedgeTwo]
  ring

private theorem exists_unit_pivot_of_twoForm_ne_zero
    {p : TwoForm} (hp : p ≠ 0) :
    ∃ i j : Fin 10, ambientTwoCoeff p i j = 1 := by
  have hex : ∃ s : QuadraticIndex 10, p s ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    exact hp (funext hnone)
  rcases hex with ⟨s, hs⟩
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  have hsOne : p (quadraticPair i j hij) = 1 :=
    (f2_eq_zero_or_one (p (quadraticPair i j hij))).resolve_left hs
  refine ⟨i, j, ?_⟩
  simpa [ambientTwoCoeff, hij] using hsOne

/-- A quadratic space whose target intersection is exactly the first-order
envelope cannot contain a member of the missing target coset. -/
theorem section_ne_missingCoset_of_targetIntersection
    (W : Submodule F₂ TwoForm)
    (hintersection : targetTwoSpace ⊓ W = firstOrderEnvelopeTwoSpace)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (C : TwoForm) (hC : C ∈ W) :
    C ≠ targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  have htarget : targetTwo (firstOrderMissingCoeff + u) ∈ targetTwoSpace :=
    ⟨firstOrderMissingCoeff + u, rfl⟩
  have hsection : targetTwo (firstOrderMissingCoeff + u) ∈ W := by
    rw [← hmissing]
    exact hC
  have hinf : targetTwo (firstOrderMissingCoeff + u) ∈
      targetTwoSpace ⊓ W := ⟨htarget, hsection⟩
  rw [hintersection] at hinf
  exact missingCoset_targetTwo_not_mem_firstOrderEnvelope u hu hinf

/-- Two quadratic wires supported in a section with exact first-order target
intersection cannot have product equal to the missing target, even when the
section generator itself is nondecomposable.  The scalar quadratic-product
alternative leaves only an inherited quadratic form, which stays in the
section, or a decomposable form, which cannot lie in the missing coset. -/
theorem quadraticSection_product_ne_missingTarget
    (W : Submodule F₂ TwoForm)
    (hintersection : targetTwoSpace ⊓ W = firstOrderEnvelopeTwoSpace)
    (X Y : ANF 10)
    (hX : X ∈ E2.quadraticEnvelopeState W)
    (hY : Y ∈ E2.quadraticEnvelopeState W)
    (a : F₂) (ell : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    X * Y ≠ quadraticCoordinateANF a ell
      (targetTwo (firstOrderMissingCoeff + u)) := by
  intro hproduct
  have hXData := (E2.mem_quadraticEnvelopeState_iff W X).1 hX
  have hYData := (E2.mem_quadraticEnvelopeState_iff W Y).1 hY
  have hproductQuad : X * Y ∈ N4.quadraticANFSpace 10 := by
    rw [hproduct]
    exact quadraticCoordinateANF_mem_quadraticANFSpace a ell
      (targetTwo (firstOrderMissingCoeff + u))
  have hprojection : quadraticProjection 10 (X * Y) =
      targetTwo (firstOrderMissingCoeff + u) := by
    rw [hproduct, quadraticProjection_quadraticCoordinateANF]
  rcases quadratic_product_projection_alternative_ten
      (p := X) (q := Y) (g := X * Y) rfl
      hXData.1 hYData.1 hproductQuad with hinherited | hdecomposable
  · have hprojectionSection : quadraticProjection 10 (X * Y) ∈ W := by
      apply (Submodule.span_le.mpr ?_) hinherited
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hXData.2
      · exact hYData.2
    exact (section_ne_missingCoset_of_targetIntersection
      W hintersection u hu (quadraticProjection 10 (X * Y))
      hprojectionSection) hprojection
  · apply missingCoset_not_decomposable u hu
    rw [← hprojection]
    exact hdecomposable

/-- A genuinely unpopulated quadratic section has no decomposable form in
its target translate.  This is the algebraic condition detected by the
rank-four return branch, stated without any finite classification. -/
def UnpopulatedQuadraticSection (z : TwoForm) : Prop :=
  ∀ d : TwoForm, IsDecomposableTwo d → d + z ∉ targetTwoSpace

/-- Intrinsic quotient formulation of an unpopulated section.  This removes
the representative from subsequent case splits: a section is unpopulated
exactly when its quotient point has no decomposable lift. -/
theorem unpopulatedQuadraticSection_iff_not_populatedFiber
    (z : TwoForm) :
    UnpopulatedQuadraticSection z ↔
      ¬ IsPopulatedFiber (quadraticQuotientProjection z) := by
  constructor
  · intro hunpopulated hpopulated
    rcases hpopulated with ⟨d, hd, hprojection⟩
    apply hunpopulated d hd
    apply (quadraticQuotientProjection_eq_zero_iff (d + z)).1
    rw [map_add, hprojection, CharTwo.add_self_eq_zero]
  · intro hnotPopulated d hd htarget
    apply hnotPopulated
    refine ⟨d, hd, ?_⟩
    have hzero : quadraticQuotientProjection (d + z) = 0 :=
      (quadraticQuotientProjection_eq_zero_iff (d + z)).2 htarget
    rw [map_add] at hzero
    exact CharTwo.add_eq_zero.mp hzero

/-- A target annihilating a member of the affine missing coset translated by
an unpopulated section must have Hankel rank at most two.  Above rank two the
target form is not a two-wedge secant, so the pivot kernel theorem makes its
exterior kernel its own target line; that would put the section back in the
zero quotient fiber, contradicting unpopulatedness. -/
theorem unpopulatedSection_annihilator_hankelRankLETwo
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (u c : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hzero : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + u) + z)
      (targetTwo c) = 0) :
    HankelRankLETwo c := by
  by_cases hc : c = 0
  · subst c
    intro i k m j l n
    simp [hankelMinorThree, hankelMatrix]
  · by_contra hnotRankTwo
    have htargetNe : targetTwo c ≠ 0 := by
      intro htargetZero
      apply hc
      apply targetTwo_injective
      exact htargetZero.trans (map_zero targetTwoLinear).symm
    rcases exists_unit_pivot_of_twoForm_ne_zero htargetNe with
      ⟨i, j, hpivot⟩
    have hnotSecant : ¬ ∃ x y v w : LinearForm,
        targetTwo c = squarefreeWedge x y + squarefreeWedge v w := by
      rintro ⟨x, y, v, w, hsecant⟩
      exact hnotRankTwo (target_sum_two_decomposable_rankTwo hsecant)
    have hcommuted : ambientWedgeTwo (targetTwo c)
        (targetTwo (firstOrderMissingCoeff + u) + z) = 0 := by
      rw [ambientWedgeTwo_comm_local]
      exact hzero
    rcases (ambientWedgeTwo_eq_zero_iff_smul_of_not_sum_two_decomposable
        (targetTwo c)
        (targetTwo (firstOrderMissingCoeff + u) + z)
        i j hpivot hnotSecant).1 hcommuted with ⟨a, ha⟩
    have hkernelTarget :
        targetTwo (firstOrderMissingCoeff + u) + z ∈ targetTwoSpace := by
      rw [ha]
      exact targetTwoSpace.smul_mem a (targetTwo_mem_targetTwoSpace c)
    have hmissingTarget :
        targetTwo (firstOrderMissingCoeff + u) ∈ targetTwoSpace :=
      targetTwo_mem_targetTwoSpace _
    have hzTarget : z ∈ targetTwoSpace := by
      have hadd := targetTwoSpace.add_mem hkernelTarget hmissingTarget
      convert hadd using 1
      funext s
      simp only [Pi.add_apply]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    exact (hunpopulated 0 decomposableTwo_zero) (by simpa using hzTarget)

/-- Every member of the first-order envelope enlarged by one section either
stays in the old envelope or uses that section with coefficient one. -/
theorem mem_firstOrderEnvelope_sup_section_cases
    (z q : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace ⊔
      Submodule.span F₂ ({z} : Set TwoForm)) :
    q ∈ firstOrderEnvelopeTwoSpace ∨
      ∃ u : TargetCoeff, u ∈ firstOrderEnvelopeCoeffSpace ∧
        q = targetTwo u + z := by
  rcases Submodule.mem_sup.mp hq with ⟨w, hw, s, hs, hsum⟩
  rcases Submodule.mem_span_singleton.mp hs with ⟨a, rfl⟩
  rcases f2_eq_zero_or_one a with ha | ha
  · left
    rw [ha, zero_smul, add_zero] at hsum
    rw [← hsum]
    exact hw
  · right
    rw [ha, one_smul] at hsum
    rcases hw with ⟨u, hu, huw⟩
    refine ⟨u, hu, ?_⟩
    calc
      q = w + z := hsum.symm
      _ = targetTwo u + z := by
        rw [← huw]
        rfl

/-- The decomposable alternative remains excluded after adding an arbitrary
old vector from an unpopulated first-order section. -/
theorem unpopulatedSection_decomposable_add_ne_missingCoset
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (d : TwoForm) (hd : IsDecomposableTwo d)
    (w : TwoForm)
    (hw : w ∈ firstOrderEnvelopeTwoSpace ⊔
      Submodule.span F₂ ({z} : Set TwoForm))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    d + w ≠ targetTwo (firstOrderMissingCoeff + u) := by
  rcases Submodule.mem_sup.mp hw with ⟨w₀, hw₀, s, hs, hsum⟩
  rcases Submodule.mem_span_singleton.mp hs with ⟨a, rfl⟩
  rcases f2_eq_zero_or_one a with ha | ha
  · rw [ha, zero_smul, add_zero] at hsum
    rcases hw₀ with ⟨c, hc, hcw₀⟩
    intro hmissing
    apply missingCoset_not_decomposable (u + c)
      (firstOrderEnvelopeCoeffSpace.add_mem hu hc)
    have hdTarget : d =
        targetTwo (firstOrderMissingCoeff + (u + c)) := by
      calc
        d = (d + w) + w := by
          symm
          rw [add_assoc, twoForm_add_self, add_zero]
        _ = targetTwo (firstOrderMissingCoeff + u) + w := by rw [hmissing]
        _ = targetTwo (firstOrderMissingCoeff + u) + targetTwo c := by
          rw [← hsum, ← hcw₀]
          rfl
        _ = targetTwo (firstOrderMissingCoeff + (u + c)) := by
          change targetTwoLinear (firstOrderMissingCoeff + u) +
              targetTwoLinear c =
            targetTwoLinear (firstOrderMissingCoeff + (u + c))
          rw [← targetTwoLinear.map_add]
          congr 1
          ac_rfl
    rw [← hdTarget]
    exact hd
  · rw [ha, one_smul] at hsum
    intro hmissing
    apply hunpopulated d hd
    have hw₀Target : w₀ ∈ targetTwoSpace :=
      firstOrderEnvelopeTwoSpace_le_targetTwoSpace hw₀
    have hmissingTarget : d + w ∈ targetTwoSpace := by
      rw [hmissing]
      exact ⟨firstOrderMissingCoeff + u, rfl⟩
    have hdz : d + z = (d + w) + w₀ := by
      rw [← hsum]
      calc
        d + z = d + ((w₀ + w₀) + z) := by
          rw [twoForm_add_self, zero_add]
        _ = (d + (w₀ + z)) + w₀ := by abel
    rw [hdz]
    exact targetTwoSpace.add_mem hmissingTarget hw₀Target

/-- Zero-colour feedback is sterile over an unpopulated return section,
including an arbitrary old correction from that same quadratic section. -/
theorem quadraticSection_correctedProduct_ne_missingTarget
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (X Y V : ANF 10)
    (hX : X ∈ E2.quadraticEnvelopeState
      (firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂ ({z} : Set TwoForm)))
    (hY : Y ∈ E2.quadraticEnvelopeState
      (firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂ ({z} : Set TwoForm)))
    (hV : V ∈ E2.quadraticEnvelopeState
      (firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂ ({z} : Set TwoForm)))
    (a : F₂) (ell : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    X * Y ≠ quadraticCoordinateANF a ell
      (targetTwo (firstOrderMissingCoeff + u)) + V := by
  let W := firstOrderEnvelopeTwoSpace ⊔
    Submodule.span F₂ ({z} : Set TwoForm)
  intro hproduct
  have hXData := (E2.mem_quadraticEnvelopeState_iff W X).1 hX
  have hYData := (E2.mem_quadraticEnvelopeState_iff W Y).1 hY
  have hVData := (E2.mem_quadraticEnvelopeState_iff W V).1 hV
  have htargetQuad : quadraticCoordinateANF a ell
      (targetTwo (firstOrderMissingCoeff + u)) ∈
        N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace a ell
      (targetTwo (firstOrderMissingCoeff + u))
  have hproductQuad : X * Y ∈ N4.quadraticANFSpace 10 := by
    rw [hproduct]
    exact (N4.quadraticANFSpace 10).add_mem htargetQuad hVData.1
  have hprojection : quadraticProjection 10 (X * Y) =
      targetTwo (firstOrderMissingCoeff + u) +
        quadraticProjection 10 V := by
    calc
      quadraticProjection 10 (X * Y) =
          quadraticProjection 10
            (quadraticCoordinateANF a ell
              (targetTwo (firstOrderMissingCoeff + u)) + V) := by
                rw [hproduct]
      _ = targetTwo (firstOrderMissingCoeff + u) +
          quadraticProjection 10 V := by
            rw [map_add, quadraticProjection_quadraticCoordinateANF]
  have hsumProjection : quadraticProjection 10 (X * Y) +
      quadraticProjection 10 V =
        targetTwo (firstOrderMissingCoeff + u) := by
    rw [hprojection, add_assoc, twoForm_add_self, add_zero]
  rcases quadratic_product_projection_alternative_ten
      (p := X) (q := Y) (g := X * Y) rfl
      hXData.1 hYData.1 hproductQuad with hinherited | hdecomposable
  · have hproductSection : quadraticProjection 10 (X * Y) ∈ W := by
      apply (Submodule.span_le.mpr ?_) hinherited
      intro d hd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl
      · exact hXData.2
      · exact hYData.2
    have hmissingSection : targetTwo (firstOrderMissingCoeff + u) ∈ W := by
      rw [← hsumProjection]
      exact W.add_mem hproductSection hVData.2
    have htarget : targetTwo (firstOrderMissingCoeff + u) ∈
        targetTwoSpace := ⟨firstOrderMissingCoeff + u, rfl⟩
    have hinf : targetTwo (firstOrderMissingCoeff + u) ∈
        targetTwoSpace ⊓ W := ⟨htarget, hmissingSection⟩
    rw [targetTwoSpace_inf_firstOrderEnvelope_sup_of_missingCoset_exclusion
      z (fun c hc => by
        intro hz
        apply hunpopulated 0 ⟨0, 0, by simp⟩
        rw [zero_add, hz]
        exact ⟨firstOrderMissingCoeff + c, rfl⟩)] at hinf
    exact missingCoset_targetTwo_not_mem_firstOrderEnvelope u hu hinf
  · exact unpopulatedSection_decomposable_add_ne_missingCoset
      z hunpopulated (quadraticProjection 10 (X * Y)) hdecomposable
      (quadraticProjection 10 V) hVData.2 u hu hsumProjection

/-- The exterior-kernel part of the rank-one argument only needs the exact
target intersection of the quadratic section.  It does not need a
decomposable anchor or a target-clean presentation. -/
theorem rankOne_section_lower_parts_zero
    (W : Submodule F₂ TwoForm)
    (hintersection : targetTwoSpace ⊓ W = firstOrderEnvelopeTwoSpace)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (C : TwoForm) (ell : LinearForm) (hC : C ∈ W)
    (hfour : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + u)) C = 0)
    (hthree : ambientVectorWedgeTwo ell
      (targetTwo (firstOrderMissingCoeff + u)) = 0) :
    C = 0 ∧ ell = 0 :=
  missingCoset_lower_parts_zero u hu C ell hfour
    (section_ne_missingCoset_of_targetIntersection
      W hintersection u hu C hC)
    hthree

/-- A genuinely high wire cannot feed back through a quadratic factor in a
section with no new target intersection and produce the missing target. -/
theorem rankOne_section_absorption_impossible
    (W : Submodule F₂ TwoForm)
    (hintersection : targetTwoSpace ⊓ W = firstOrderEnvelopeTwoSpace)
    (U : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (fConst cConst : F₂) (fLinear cLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (C : TwoForm) (hC : C ∈ W)
    (hproduct :
      U * quadraticCoordinateANF cConst cLinear C =
        quadraticCoordinateANF fConst fLinear
          (targetTwo (firstOrderMissingCoeff + u)))
    (habsorb :
      quadraticCoordinateANF fConst fLinear
          (targetTwo (firstOrderMissingCoeff + u)) *
        quadraticCoordinateANF cConst cLinear C =
      quadraticCoordinateANF fConst fLinear
        (targetTwo (firstOrderMissingCoeff + u))) : False := by
  let Ftwo := targetTwo (firstOrderMissingCoeff + u)
  let F := quadraticCoordinateANF fConst fLinear Ftwo
  let c := quadraticCoordinateANF cConst cLinear C
  change U * c = F at hproduct
  change F * c = F at habsorb
  have hFquad : F ∈ N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace fConst fLinear Ftwo
  have hfour : ambientWedgeTwo Ftwo C = 0 := by
    calc
      ambientWedgeTwo Ftwo C = anfFourProjectionTen (F * c) := by
        symm
        exact anfFourProjectionTen_quadraticCoordinateANF_mul
          fConst cConst fLinear cLinear Ftwo C
      _ = anfFourProjectionTen F := congrArg anfFourProjectionTen habsorb
      _ = 0 := anfFourProjectionTen_eq_zero_of_degreeLE_three
        (hFquad.mono (by omega))
  have hthree : ambientVectorWedgeTwo cLinear Ftwo = 0 := by
    have hCzero : C = 0 := by
      rcases (missingCoset_wedge_eq_zero_iff u hu C).1 hfour with
        ⟨a, ha⟩
      rcases f2_eq_zero_or_one a with ha0 | ha1
      · rw [ha, ha0, zero_smul]
      · exfalso
        apply section_ne_missingCoset_of_targetIntersection
          W hintersection u hu C hC
        simpa [ha1] using ha
    calc
      ambientVectorWedgeTwo cLinear Ftwo =
          factorPlaneCubic fLinear cLinear Ftwo 0 := by
            symm
            exact factorPlaneCubic_zero_right fLinear cLinear Ftwo
      _ = exactLowProductCubic fLinear cLinear Ftwo 0 := by
        simp [exactLowProductCubic]
      _ = anfThreeProjectionTen (F * c) := by
        change exactLowProductCubic fLinear cLinear Ftwo 0 =
          anfThreeProjectionTen
            (quadraticCoordinateANF fConst fLinear Ftwo *
              quadraticCoordinateANF cConst cLinear C)
        rw [hCzero]
        symm
        exact anfThreeProjectionTen_quadraticCoordinateANF_mul
          fConst cConst fLinear cLinear Ftwo 0
      _ = anfThreeProjectionTen F := congrArg anfThreeProjectionTen habsorb
      _ = 0 := anfThreeProjectionTen_eq_zero_of_quadratic hFquad
  have hlower := rankOne_section_lower_parts_zero
    W hintersection u hu C cLinear hC hfour hthree
  have hcConstant : c = cConst • (1 : ANF 10) := by
    simp [c, quadraticCoordinateANF, hlower.1, hlower.2,
      show quadraticANFOfForm (0 : TwoForm) = 0 by
        exact map_zero quadraticANFOfFormLinear]
  have hFtwoNotZero : Ftwo ≠ 0 := by
    intro hzero
    apply missingCoset_targetTwo_not_mem_firstOrderEnvelope u hu
    rw [show targetTwo (firstOrderMissingCoeff + u) = 0 by exact hzero]
    exact firstOrderEnvelopeTwoSpace.zero_mem
  rcases f2_eq_zero_or_one cConst with hc0 | hc1
  · have hFzero : F = 0 := by
      have h := habsorb
      rw [hcConstant, hc0, zero_smul, mul_zero] at h
      exact h.symm
    apply hFtwoNotZero
    have hprojection := congrArg (quadraticProjection 10) hFzero
    simpa [F] using hprojection
  · apply hUhigh
    have h := hproduct
    rw [hcConstant, hc1, one_smul, mul_one] at h
    rw [h]
    exact hFquad

/-- If both the quadratic factor and the old correction use the returned
section, their section coefficients cancel.  The quartic absorption equation
then lies in the original missing Hankel coset, whose exterior kernel is one
dimensional.  Unpopulatedness excludes the zero quadratic product needed by
the nonzero kernel branch.  Thus this part of returned-section rank-one
feedback is algebraically impossible without a finite circuit search. -/
theorem rankOne_unpopulatedSection_bothUseSection_impossible
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (U : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (fConst cConst : F₂) (fLinear cLinear : LinearForm)
    (u cCoeff vCoeff : TargetCoeff)
    (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hcCoeff : cCoeff ∈ firstOrderEnvelopeCoeffSpace)
    (hvCoeff : vCoeff ∈ firstOrderEnvelopeCoeffSpace)
    (C Vtwo : TwoForm)
    (hC : C = targetTwo cCoeff + z)
    (hV : Vtwo = targetTwo vCoeff + z)
    (hproduct :
      U * quadraticCoordinateANF cConst cLinear C =
        quadraticCoordinateANF fConst fLinear
          (targetTwo (firstOrderMissingCoeff + u) + Vtwo))
    (habsorb :
      (U * quadraticCoordinateANF cConst cLinear C) *
          quadraticCoordinateANF cConst cLinear C =
        U * quadraticCoordinateANF cConst cLinear C) : False := by
  let Ftwo := targetTwo (firstOrderMissingCoeff + u) + Vtwo
  let F := quadraticCoordinateANF fConst fLinear Ftwo
  let c := quadraticCoordinateANF cConst cLinear C
  change U * c = F at hproduct
  change (U * c) * c = U * c at habsorb
  have habsorbF : F * c = F := by
    calc
      F * c = (U * c) * c := by rw [hproduct]
      _ = U * c := habsorb
      _ = F := hproduct
  have hFquad : F ∈ N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace fConst fLinear Ftwo
  have hFtwoAddZ : Ftwo + z =
      targetTwo (firstOrderMissingCoeff + (u + vCoeff)) := by
    dsimp only [Ftwo]
    rw [hV]
    calc
      (targetTwo (firstOrderMissingCoeff + u) +
          (targetTwo vCoeff + z)) + z =
          (targetTwo (firstOrderMissingCoeff + u) +
            targetTwo vCoeff) + (z + z) := by abel
      _ = targetTwo (firstOrderMissingCoeff + u) +
          targetTwo vCoeff := by rw [twoForm_add_self, add_zero]
      _ = targetTwo (firstOrderMissingCoeff + (u + vCoeff)) := by
        change targetTwoLinear (firstOrderMissingCoeff + u) +
            targetTwoLinear vCoeff =
          targetTwoLinear (firstOrderMissingCoeff + (u + vCoeff))
        rw [← targetTwoLinear.map_add]
        apply congrArg targetTwoLinear
        ac_rfl
  have hFtwoNotDecomposable : ¬ IsDecomposableTwo Ftwo := by
    intro hdec
    apply hunpopulated Ftwo hdec
    rw [hFtwoAddZ]
    exact targetTwo_mem_targetTwoSpace _
  have hmissingForm : Ftwo + C =
      targetTwo (firstOrderMissingCoeff + (u + vCoeff + cCoeff)) := by
    dsimp only [Ftwo]
    rw [hV, hC]
    calc
      (targetTwo (firstOrderMissingCoeff + u) +
          (targetTwo vCoeff + z)) + (targetTwo cCoeff + z) =
          ((targetTwo (firstOrderMissingCoeff + u) +
            targetTwo vCoeff) + targetTwo cCoeff) + (z + z) := by abel
      _ = (targetTwo (firstOrderMissingCoeff + u) +
          targetTwo vCoeff) + targetTwo cCoeff := by
            rw [twoForm_add_self, add_zero]
      _ = targetTwo
          (firstOrderMissingCoeff + (u + vCoeff + cCoeff)) := by
        change (targetTwoLinear (firstOrderMissingCoeff + u) +
            targetTwoLinear vCoeff) + targetTwoLinear cCoeff =
          targetTwoLinear
            (firstOrderMissingCoeff + (u + vCoeff + cCoeff))
        rw [← targetTwoLinear.map_add, ← targetTwoLinear.map_add]
        apply congrArg targetTwoLinear
        ac_rfl
  have hfour : ambientWedgeTwo Ftwo C = 0 := by
    calc
      ambientWedgeTwo Ftwo C = anfFourProjectionTen (F * c) := by
        symm
        exact anfFourProjectionTen_quadraticCoordinateANF_mul
          fConst cConst fLinear cLinear Ftwo C
      _ = anfFourProjectionTen F := congrArg anfFourProjectionTen habsorbF
      _ = 0 := anfFourProjectionTen_eq_zero_of_degreeLE_three
        (hFquad.mono (by omega))
  have hmissingWedge : ambientWedgeTwo
      (targetTwo
        (firstOrderMissingCoeff + (u + vCoeff + cCoeff))) C = 0 := by
    rw [← hmissingForm, ambientWedgeTwo_add_left_local, hfour,
      ambientWedgeTwo_self, add_zero]
  have hcombinedCoeff : u + vCoeff + cCoeff ∈
      firstOrderEnvelopeCoeffSpace :=
    firstOrderEnvelopeCoeffSpace.add_mem
      (firstOrderEnvelopeCoeffSpace.add_mem hu hvCoeff) hcCoeff
  have hCzero : C = 0 := by
    rcases (missingCoset_wedge_eq_zero_iff
        (u + vCoeff + cCoeff) hcombinedCoeff C).1 hmissingWedge with
      ⟨a, ha⟩
    have ha' : C = a • (Ftwo + C) := by
      rw [hmissingForm]
      exact ha
    rcases f2_eq_zero_or_one a with ha0 | ha1
    · simpa [ha0] using ha'
    · exfalso
      apply hFtwoNotDecomposable
      have hFtwoZero : Ftwo = 0 := by
        rw [ha1, one_smul] at ha'
        have hcancel : Ftwo + C = 0 + C := by simpa using ha'.symm
        exact add_right_cancel hcancel
      rw [hFtwoZero]
      exact decomposableTwo_zero
  have hthree : ambientVectorWedgeTwo cLinear Ftwo = 0 := by
    calc
      ambientVectorWedgeTwo cLinear Ftwo =
          factorPlaneCubic fLinear cLinear Ftwo 0 := by
            symm
            exact factorPlaneCubic_zero_right fLinear cLinear Ftwo
      _ = exactLowProductCubic fLinear cLinear Ftwo 0 := by
        simp [exactLowProductCubic]
      _ = anfThreeProjectionTen (F * c) := by
        change exactLowProductCubic fLinear cLinear Ftwo 0 =
          anfThreeProjectionTen
            (quadraticCoordinateANF fConst fLinear Ftwo *
              quadraticCoordinateANF cConst cLinear C)
        rw [hCzero]
        symm
        exact anfThreeProjectionTen_quadraticCoordinateANF_mul
          fConst cConst fLinear cLinear Ftwo 0
      _ = anfThreeProjectionTen F := congrArg anfThreeProjectionTen habsorbF
      _ = 0 := anfThreeProjectionTen_eq_zero_of_quadratic hFquad
  have hcLinearZero : cLinear = 0 := by
    by_contra hcLinearNe
    rcases eq_squarefreeWedge_of_ambientVectorWedgeTwo_eq_zero
        Ftwo cLinear hcLinearNe hthree with ⟨v, hv⟩
    exact hFtwoNotDecomposable ⟨cLinear, v, hv⟩
  have hcConstant : c = cConst • (1 : ANF 10) := by
    simp [c, quadraticCoordinateANF, hCzero, hcLinearZero,
      show quadraticANFOfForm (0 : TwoForm) = 0 by
        exact map_zero quadraticANFOfFormLinear]
  have hFtwoNeZero : Ftwo ≠ 0 := by
    intro hzero
    apply hFtwoNotDecomposable
    rw [hzero]
    exact decomposableTwo_zero
  rcases f2_eq_zero_or_one cConst with hc0 | hc1
  · have hFzero : F = 0 := by
      have h := habsorbF
      rw [hcConstant, hc0, zero_smul, mul_zero] at h
      exact h.symm
    apply hFtwoNeZero
    have hprojection := congrArg (quadraticProjection 10) hFzero
    simpa [F] using hprojection
  · apply hUhigh
    have h := hproduct
    rw [hcConstant, hc1, one_smul, mul_one] at h
    rw [h]
    exact hFquad

/-- The remaining asymmetric rank-one return branch is sterile whenever the
returned section has trivial target exterior kernel.  Here the correction
uses the returned section but the quadratic factor stays in the old Hankel
envelope.  The quartic idempotence equation then kills that factor directly;
the cubic and constant equations finish exactly as in the symmetric branch.
-/
theorem rankOne_unpopulatedSection_asymmetric_impossible
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (hkernel : ∀ (u₀ c₀ : TargetCoeff),
      u₀ ∈ firstOrderEnvelopeCoeffSpace →
      ambientWedgeTwo
          (targetTwo (firstOrderMissingCoeff + u₀) + z)
          (targetTwo c₀) = 0 →
      c₀ = 0)
    (U : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (fConst cConst : F₂) (fLinear cLinear : LinearForm)
    (u cCoeff vCoeff : TargetCoeff)
    (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hcCoeff : cCoeff ∈ firstOrderEnvelopeCoeffSpace)
    (hvCoeff : vCoeff ∈ firstOrderEnvelopeCoeffSpace)
    (C Vtwo : TwoForm)
    (hC : C = targetTwo cCoeff)
    (hV : Vtwo = targetTwo vCoeff + z)
    (hproduct :
      U * quadraticCoordinateANF cConst cLinear C =
        quadraticCoordinateANF fConst fLinear
          (targetTwo (firstOrderMissingCoeff + u) + Vtwo))
    (habsorb :
      (U * quadraticCoordinateANF cConst cLinear C) *
          quadraticCoordinateANF cConst cLinear C =
        U * quadraticCoordinateANF cConst cLinear C) : False := by
  let Ftwo := targetTwo (firstOrderMissingCoeff + u) + Vtwo
  let F := quadraticCoordinateANF fConst fLinear Ftwo
  let c := quadraticCoordinateANF cConst cLinear C
  change U * c = F at hproduct
  change (U * c) * c = U * c at habsorb
  have habsorbF : F * c = F := by
    calc
      F * c = (U * c) * c := by rw [hproduct]
      _ = U * c := habsorb
      _ = F := hproduct
  have hFquad : F ∈ N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace fConst fLinear Ftwo
  have hFtwoNormal : Ftwo =
      targetTwo (firstOrderMissingCoeff + (u + vCoeff)) + z := by
    dsimp only [Ftwo]
    rw [hV]
    calc
      targetTwo (firstOrderMissingCoeff + u) +
          (targetTwo vCoeff + z) =
          (targetTwo (firstOrderMissingCoeff + u) +
            targetTwo vCoeff) + z := by abel
      _ = targetTwo (firstOrderMissingCoeff + (u + vCoeff)) + z := by
        change (targetTwoLinear (firstOrderMissingCoeff + u) +
            targetTwoLinear vCoeff) + z =
          targetTwoLinear (firstOrderMissingCoeff + (u + vCoeff)) + z
        rw [← targetTwoLinear.map_add]
        exact congrArg (fun d : TargetCoeff => targetTwoLinear d + z)
          (by ac_rfl)
  have hFtwoAddZ : Ftwo + z =
      targetTwo (firstOrderMissingCoeff + (u + vCoeff)) := by
    rw [hFtwoNormal]
    calc
      (targetTwo (firstOrderMissingCoeff + (u + vCoeff)) + z) + z =
          targetTwo (firstOrderMissingCoeff + (u + vCoeff)) +
            (z + z) := by abel
      _ = targetTwo (firstOrderMissingCoeff + (u + vCoeff)) := by
        rw [twoForm_add_self, add_zero]
  have hFtwoNotDecomposable : ¬ IsDecomposableTwo Ftwo := by
    intro hdec
    apply hunpopulated Ftwo hdec
    rw [hFtwoAddZ]
    exact targetTwo_mem_targetTwoSpace _
  have hfour : ambientWedgeTwo Ftwo C = 0 := by
    calc
      ambientWedgeTwo Ftwo C = anfFourProjectionTen (F * c) := by
        symm
        exact anfFourProjectionTen_quadraticCoordinateANF_mul
          fConst cConst fLinear cLinear Ftwo C
      _ = anfFourProjectionTen F := congrArg anfFourProjectionTen habsorbF
      _ = 0 := anfFourProjectionTen_eq_zero_of_degreeLE_three
        (hFquad.mono (by omega))
  have hcombinedCoeff : u + vCoeff ∈ firstOrderEnvelopeCoeffSpace :=
    firstOrderEnvelopeCoeffSpace.add_mem hu hvCoeff
  have htargetWedge : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + (u + vCoeff)) + z)
      (targetTwo cCoeff) = 0 := by
    rw [← hFtwoNormal, ← hC]
    exact hfour
  have hcCoeffZero : cCoeff = 0 :=
    hkernel (u + vCoeff) cCoeff hcombinedCoeff htargetWedge
  have hCzero : C = 0 := by
    calc
      C = targetTwo 0 := by simpa only [hcCoeffZero] using hC
      _ = 0 := map_zero targetTwoLinear
  have hthree : ambientVectorWedgeTwo cLinear Ftwo = 0 := by
    calc
      ambientVectorWedgeTwo cLinear Ftwo =
          factorPlaneCubic fLinear cLinear Ftwo 0 := by
            symm
            exact factorPlaneCubic_zero_right fLinear cLinear Ftwo
      _ = exactLowProductCubic fLinear cLinear Ftwo 0 := by
        simp [exactLowProductCubic]
      _ = anfThreeProjectionTen (F * c) := by
        change exactLowProductCubic fLinear cLinear Ftwo 0 =
          anfThreeProjectionTen
            (quadraticCoordinateANF fConst fLinear Ftwo *
              quadraticCoordinateANF cConst cLinear C)
        rw [hCzero]
        symm
        exact anfThreeProjectionTen_quadraticCoordinateANF_mul
          fConst cConst fLinear cLinear Ftwo 0
      _ = anfThreeProjectionTen F := congrArg anfThreeProjectionTen habsorbF
      _ = 0 := anfThreeProjectionTen_eq_zero_of_quadratic hFquad
  have hcLinearZero : cLinear = 0 := by
    by_contra hcLinearNe
    rcases eq_squarefreeWedge_of_ambientVectorWedgeTwo_eq_zero
        Ftwo cLinear hcLinearNe hthree with ⟨v, hv⟩
    exact hFtwoNotDecomposable ⟨cLinear, v, hv⟩
  have hcConstant : c = cConst • (1 : ANF 10) := by
    simp [c, quadraticCoordinateANF, hCzero, hcLinearZero,
      show quadraticANFOfForm (0 : TwoForm) = 0 by
        exact map_zero quadraticANFOfFormLinear]
  have hFtwoNeZero : Ftwo ≠ 0 := by
    intro hzero
    apply hFtwoNotDecomposable
    rw [hzero]
    exact decomposableTwo_zero
  rcases f2_eq_zero_or_one cConst with hc0 | hc1
  · have hFzero : F = 0 := by
      have h := habsorbF
      rw [hcConstant, hc0, zero_smul, mul_zero] at h
      exact h.symm
    apply hFtwoNeZero
    have hprojection := congrArg (quadraticProjection 10) hFzero
    simpa [F] using hprojection
  · apply hUhigh
    have h := hproduct
    rw [hcConstant, hc1, one_smul, mul_one] at h
    rw [h]
    exact hFquad

/-- Arbitrary old first-order corrections can be absorbed into the missing
target coefficient exactly as in the decomposable-anchor proof. -/
theorem rankOne_section_envelopeCorrection_impossible
    (W : Submodule F₂ TwoForm)
    (hintersection : targetTwoSpace ⊓ W = firstOrderEnvelopeTwoSpace)
    (U : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (fConst cConst : F₂) (fLinear cLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (C : TwoForm) (hC : C ∈ W)
    (v : ANF 10) (hv : v ∈ firstOrderEnvelopeState)
    (hproduct :
      U * quadraticCoordinateANF cConst cLinear C =
        quadraticCoordinateANF fConst fLinear
          (targetTwo (firstOrderMissingCoeff + u)) + v)
    (habsorb :
      (U * quadraticCoordinateANF cConst cLinear C) *
          quadraticCoordinateANF cConst cLinear C =
        U * quadraticCoordinateANF cConst cLinear C) : False := by
  rcases exists_firstOrderCoeff_of_mem_envelopeState hv with
    ⟨uv, huv, hprojectionV⟩
  have hvquad : v ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      firstOrderEnvelopeTwoSpace hv
  rcases exists_quadraticCoordinates hvquad with
    ⟨vConst, vLinear, vTwo, hvCoordinates⟩
  have hvTwo : vTwo = targetTwo uv := by
    calc
      vTwo = quadraticProjection 10 v := by
        rw [hvCoordinates, quadraticProjection_quadraticCoordinateANF]
      _ = targetTwo uv := hprojectionV
  subst vTwo
  let F := quadraticCoordinateANF (fConst + vConst) (fLinear + vLinear)
    (targetTwo (firstOrderMissingCoeff + (u + uv)))
  have htargetAdd :
      targetTwo (firstOrderMissingCoeff + u) + targetTwo uv =
        targetTwo (firstOrderMissingCoeff + (u + uv)) := by
    change targetTwoLinear (firstOrderMissingCoeff + u) +
        targetTwoLinear uv =
      targetTwoLinear (firstOrderMissingCoeff + (u + uv))
    rw [← targetTwoLinear.map_add]
    congr 1
    ac_rfl
  have hproductF :
      U * quadraticCoordinateANF cConst cLinear C = F := by
    rw [hproduct, hvCoordinates, quadraticCoordinateANF_add, htargetAdd]
  have habsorbF :
      F * quadraticCoordinateANF cConst cLinear C = F := by
    calc
      F * quadraticCoordinateANF cConst cLinear C =
          (U * quadraticCoordinateANF cConst cLinear C) *
            quadraticCoordinateANF cConst cLinear C := by rw [hproductF]
      _ = U * quadraticCoordinateANF cConst cLinear C := habsorb
      _ = F := hproductF
  exact rankOne_section_absorption_impossible
    W hintersection U hUhigh (fConst + vConst) cConst
      (fLinear + vLinear) cLinear (u + uv)
      (firstOrderEnvelopeCoeffSpace.add_mem hu huv)
      C hC hproductF habsorbF

/-- Coordinate-free interface for rank-one high feedback through an arbitrary
quadratic section with exact first-order target intersection. -/
theorem rankOne_sectionCorrected_escape_impossible
    (W : Submodule F₂ TwoForm)
    (hintersection : targetTwoSpace ⊓ W = firstOrderEnvelopeTwoSpace)
    (U c : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (hcquad : c ∈ N4.quadraticANFSpace 10)
    (fConst : F₂) (fLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hcSection : quadraticProjection 10 c ∈ W)
    (v : ANF 10) (hv : v ∈ firstOrderEnvelopeState)
    (hproduct :
      U * c = quadraticCoordinateANF fConst fLinear
        (targetTwo (firstOrderMissingCoeff + u)) + v)
    (habsorb : (U * c) * c = U * c) : False := by
  rcases exists_quadraticCoordinates hcquad with
    ⟨cConst, cLinear, C, hcCoordinates⟩
  have hC : C ∈ W := by
    rw [hcCoordinates, quadraticProjection_quadraticCoordinateANF]
      at hcSection
    exact hcSection
  rw [hcCoordinates] at hproduct habsorb
  exact rankOne_section_envelopeCorrection_impossible
    W hintersection U hUhigh fConst cConst fLinear cLinear
      u hu C hC v hv hproduct habsorb

/-- A normalized rank-one escape over an unpopulated return section reduces
to one asymmetric residue: the old correction must use the return section,
while the quadratic factor must remain in the old first-order envelope.

The other two possibilities are the old-envelope correction theorem and the
both-use-section cancellation theorem above. -/
theorem rankOne_unpopulatedSection_escape_is_asymmetric
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (U c v : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (hcquad : c ∈ N4.quadraticANFSpace 10)
    (hvquad : v ∈ N4.quadraticANFSpace 10)
    (fConst : F₂) (fLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hcSection : quadraticProjection 10 c ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂ ({z} : Set TwoForm))
    (hvSection : quadraticProjection 10 v ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂ ({z} : Set TwoForm))
    (hproduct :
      U * c = quadraticCoordinateANF fConst fLinear
        (targetTwo (firstOrderMissingCoeff + u)) + v)
    (habsorb : (U * c) * c = U * c) :
    (∃ vCoeff : TargetCoeff,
        vCoeff ∈ firstOrderEnvelopeCoeffSpace ∧
        quadraticProjection 10 v = targetTwo vCoeff + z) ∧
      quadraticProjection 10 c ∈ firstOrderEnvelopeTwoSpace := by
  let W := firstOrderEnvelopeTwoSpace ⊔
    Submodule.span F₂ ({z} : Set TwoForm)
  have hintersection : targetTwoSpace ⊓ W =
      firstOrderEnvelopeTwoSpace := by
    dsimp only [W]
    apply targetTwoSpace_inf_firstOrderEnvelope_sup_of_missingCoset_exclusion
    intro coeff hcoeff hz
    apply hunpopulated 0 decomposableTwo_zero
    rw [zero_add, hz]
    exact targetTwo_mem_targetTwoSpace _
  rcases mem_firstOrderEnvelope_sup_section_cases z
      (quadraticProjection 10 v) hvSection with hvOld | hvUses
  · exfalso
    have hvEnvelope : v ∈ firstOrderEnvelopeState :=
      (E2.mem_quadraticEnvelopeState_iff
        firstOrderEnvelopeTwoSpace v).2 ⟨hvquad, hvOld⟩
    exact rankOne_sectionCorrected_escape_impossible
      W hintersection U c hUhigh hcquad fConst fLinear u hu
        hcSection v hvEnvelope hproduct habsorb
  · refine ⟨hvUses, ?_⟩
    rcases mem_firstOrderEnvelope_sup_section_cases z
        (quadraticProjection 10 c) hcSection with hcOld | hcUses
    · exact hcOld
    · exfalso
      rcases hvUses with ⟨vCoeff, hvCoeff, hVProjection⟩
      rcases hcUses with ⟨cCoeff, hcCoeff, hCProjection⟩
      rcases exists_quadraticCoordinates hcquad with
        ⟨cConst, cLinear, C, hcCoordinates⟩
      rcases exists_quadraticCoordinates hvquad with
        ⟨vConst, vLinear, Vtwo, hvCoordinates⟩
      have hC : C = targetTwo cCoeff + z := by
        calc
          C = quadraticProjection 10 c := by
            rw [hcCoordinates, quadraticProjection_quadraticCoordinateANF]
          _ = targetTwo cCoeff + z := hCProjection
      have hV : Vtwo = targetTwo vCoeff + z := by
        calc
          Vtwo = quadraticProjection 10 v := by
            rw [hvCoordinates, quadraticProjection_quadraticCoordinateANF]
          _ = targetTwo vCoeff + z := hVProjection
      rw [hcCoordinates] at hproduct habsorb
      rw [hvCoordinates, quadraticCoordinateANF_add] at hproduct
      exact rankOne_unpopulatedSection_bothUseSection_impossible
        z hunpopulated U hUhigh (fConst + vConst) cConst
          (fLinear + vLinear) cLinear u cCoeff vCoeff hu hcCoeff hvCoeff
          C Vtwo hC hV hproduct habsorb

/-- A target-kernel certificate closes every normalized rank-one escape over
an unpopulated return section.  This is the circuit-facing fixed-block form:
the old-envelope and symmetric section branches are discharged by
`rankOne_unpopulatedSection_escape_is_asymmetric`, and the remaining branch
is exactly the asymmetric exterior-kernel theorem above. -/
theorem rankOne_unpopulatedSection_escape_impossible_of_kernel
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (hkernel : ∀ (u₀ c₀ : TargetCoeff),
      u₀ ∈ firstOrderEnvelopeCoeffSpace →
      ambientWedgeTwo
          (targetTwo (firstOrderMissingCoeff + u₀) + z)
          (targetTwo c₀) = 0 →
      c₀ = 0)
    (U c v : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (hcquad : c ∈ N4.quadraticANFSpace 10)
    (hvquad : v ∈ N4.quadraticANFSpace 10)
    (fConst : F₂) (fLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hcSection : quadraticProjection 10 c ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂ ({z} : Set TwoForm))
    (hvSection : quadraticProjection 10 v ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂ ({z} : Set TwoForm))
    (hproduct :
      U * c = quadraticCoordinateANF fConst fLinear
        (targetTwo (firstOrderMissingCoeff + u)) + v)
    (habsorb : (U * c) * c = U * c) : False := by
  rcases rankOne_unpopulatedSection_escape_is_asymmetric
      z hunpopulated U c v hUhigh hcquad hvquad fConst fLinear u hu
        hcSection hvSection hproduct habsorb with
    ⟨⟨vCoeff, hvCoeff, hVProjection⟩, hcOld⟩
  rcases hcOld with ⟨cCoeff, hcCoeff, hCProjection⟩
  rcases exists_quadraticCoordinates hcquad with
    ⟨cConst, cLinear, C, hcCoordinates⟩
  rcases exists_quadraticCoordinates hvquad with
    ⟨vConst, vLinear, Vtwo, hvCoordinates⟩
  have hC : C = targetTwo cCoeff := by
    calc
      C = quadraticProjection 10 c := by
        rw [hcCoordinates, quadraticProjection_quadraticCoordinateANF]
      _ = targetTwo cCoeff := hCProjection.symm
  have hV : Vtwo = targetTwo vCoeff + z := by
    calc
      Vtwo = quadraticProjection 10 v := by
        rw [hvCoordinates, quadraticProjection_quadraticCoordinateANF]
      _ = targetTwo vCoeff + z := hVProjection
  rw [hcCoordinates] at hproduct habsorb
  rw [hvCoordinates, quadraticCoordinateANF_add] at hproduct
  exact rankOne_unpopulatedSection_asymmetric_impossible
    z hunpopulated hkernel U hUhigh (fConst + vConst) cConst
      (fLinear + vLinear) cLinear u cCoeff vCoeff hu hcCoeff hvCoeff
      C Vtwo hC hV hproduct habsorb

/-- The canonical rational `(0,1)` quadratic-return orbit has no normalized
rank-one target escape. -/
theorem rankOne_rationalZeroOneReturn_escape_impossible
    (hunpopulated :
      UnpopulatedQuadraticSection rationalZeroOneReturnSection)
    (U c v : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (hcquad : c ∈ N4.quadraticANFSpace 10)
    (hvquad : v ∈ N4.quadraticANFSpace 10)
    (fConst : F₂) (fLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hcSection : quadraticProjection 10 c ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂
          ({rationalZeroOneReturnSection} : Set TwoForm))
    (hvSection : quadraticProjection 10 v ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂
          ({rationalZeroOneReturnSection} : Set TwoForm))
    (hproduct :
      U * c = quadraticCoordinateANF fConst fLinear
        (targetTwo (firstOrderMissingCoeff + u)) + v)
    (habsorb : (U * c) * c = U * c) : False :=
  rankOne_unpopulatedSection_escape_impossible_of_kernel
    rationalZeroOneReturnSection hunpopulated
      rationalZeroOneReturn_wedge_firstOrder_injective
      U c v hUhigh hcquad hvquad fConst fLinear u hu hcSection hvSection
      hproduct habsorb

/-- Every canonical rational-plane return orbit has sterile normalized
rank-one feedback. -/
theorem rankOne_rationalReturnOrbit_escape_impossible
    (orbit : RationalReturnOrbit)
    (hunpopulated :
      UnpopulatedQuadraticSection (rationalReturnOrbitSection orbit))
    (U c v : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (hcquad : c ∈ N4.quadraticANFSpace 10)
    (hvquad : v ∈ N4.quadraticANFSpace 10)
    (fConst : F₂) (fLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hcSection : quadraticProjection 10 c ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂
          ({rationalReturnOrbitSection orbit} : Set TwoForm))
    (hvSection : quadraticProjection 10 v ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂
          ({rationalReturnOrbitSection orbit} : Set TwoForm))
    (hproduct :
      U * c = quadraticCoordinateANF fConst fLinear
        (targetTwo (firstOrderMissingCoeff + u)) + v)
    (habsorb : (U * c) * c = U * c) : False :=
  rankOne_unpopulatedSection_escape_impossible_of_kernel
    (rationalReturnOrbitSection orbit) hunpopulated
      (rationalReturnOrbit_wedge_firstOrder_injective orbit)
      U c v hUhigh hcquad hvquad fConst fLinear u hu hcSection hvSection
      hproduct habsorb

end
end N5
end UnrestrictedBooleanMul
