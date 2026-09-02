import UnrestrictedBooleanMul.N5.EnvelopeExactRewire

/-!
# Exact Boolean semantics at all rational value--jet planes

The quadratic--quadratic cubic overlap of a rational value--jet plane is
linear multiplication of its value direction by the derivative linear
form.  This file proves that identity through ANF algebra and lifts the
normalized Boolean-correction lemma without enumerating forms or circuits.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private def linearANFTenMap : LinearForm →ₗ[F₂] ANF 10 where
  toFun := linearANFTen
  map_add' := linearANFTen_add
  map_smul' := linearANFTen_smul

@[simp] theorem linearANFTen_aLinear (i : Fin 5) :
    linearANFTen (aLinear i) = X (aCoord i) := by
  have ha : aLinear i = coordinateLinearTen (aCoord i) := by
    classical
    ext k
    simp [aLinear, coordinateLinearTen, Pi.basisFun, Pi.single_apply]
  rw [ha, linearANFTen_coordinate]

@[simp] theorem linearANFTen_bLinear (i : Fin 5) :
    linearANFTen (bLinear i) = X (bCoord i) := by
  have hb : bLinear i = coordinateLinearTen (bCoord i) := by
    classical
    ext k
    simp [bLinear, coordinateLinearTen, Pi.basisFun, Pi.single_apply]
  rw [hb, linearANFTen_coordinate]

private theorem linearANFTen_aOneEval :
    linearANFTen aOneEval = ∑ i : Fin 5, aVar 5 i := by
  change linearANFTenMap aOneEval = _
  rw [aOneEval, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change linearANFTen (aLinear i) = aVar 5 i
  rw [linearANFTen_aLinear]
  rfl

private theorem linearANFTen_bOneEval :
    linearANFTen bOneEval = ∑ i : Fin 5, bVar 5 i := by
  change linearANFTenMap bOneEval = _
  rw [bOneEval, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change linearANFTen (bLinear i) = bVar 5 i
  rw [linearANFTen_bLinear]
  rfl

private theorem linearANFTen_aOneJet :
    linearANFTen aOneJet = aVar 5 1 + aVar 5 3 := by
  rw [aOneJet, linearANFTen_add,
    linearANFTen_aLinear, linearANFTen_aLinear]
  rfl

private theorem linearANFTen_bOneJet :
    linearANFTen bOneJet = bVar 5 1 + bVar 5 3 := by
  rw [bOneJet, linearANFTen_add,
    linearANFTen_bLinear, linearANFTen_bLinear]
  rfl

private theorem aOneEval_mul_bOneEval_mem_pure :
    linearANFTen aOneEval * linearANFTen bOneEval ∈
      pureQuadraticANFSpace := by
  rw [linearANFTen_aOneEval, linearANFTen_bOneEval,
    Finset.sum_mul]
  apply Submodule.sum_mem
  intro i _
  rw [Finset.mul_sum]
  exact Submodule.sum_mem _ fun j _ => aVar_mul_bVar_mem_pure i j

private theorem aOneEval_mul_bOneJet_mem_pure :
    linearANFTen aOneEval * linearANFTen bOneJet ∈
      pureQuadraticANFSpace := by
  rw [linearANFTen_aOneEval, linearANFTen_bOneJet,
    Finset.sum_mul]
  apply Submodule.sum_mem
  intro i _
  rw [mul_add]
  exact pureQuadraticANFSpace.add_mem
    (aVar_mul_bVar_mem_pure i 1) (aVar_mul_bVar_mem_pure i 3)

private theorem aOneJet_mul_bOneEval_mem_pure :
    linearANFTen aOneJet * linearANFTen bOneEval ∈
      pureQuadraticANFSpace := by
  rw [linearANFTen_aOneJet, linearANFTen_bOneEval,
    add_mul]
  apply pureQuadraticANFSpace.add_mem
  · rw [Finset.mul_sum]
    exact Submodule.sum_mem _ fun j _ => aVar_mul_bVar_mem_pure 1 j
  · rw [Finset.mul_sum]
    exact Submodule.sum_mem _ fun j _ => aVar_mul_bVar_mem_pure 3 j

private theorem quadraticANFOfForm_squarefreeWedge_eq_of_mul_mem_pure
    (A B : LinearForm)
    (hpure : linearANFTen A * linearANFTen B ∈
      pureQuadraticANFSpace) :
    quadraticANFOfForm (squarefreeWedge A B) =
      linearANFTen A * linearANFTen B := by
  apply quadraticProjection_injective_on_pure
  · exact ⟨squarefreeWedge A B, rfl⟩
  · exact hpure
  · rw [quadraticProjection_quadraticANFOfForm,
      quadraticProjection_linearANFTen_mul_linearANFTen]

private theorem quadraticANFOfForm_rationalOneValue :
    quadraticANFOfForm rationalOneValueTwo =
      linearANFTen aOneEval * linearANFTen bOneEval := by
  rw [rationalOneValueTwo]
  exact quadraticANFOfForm_squarefreeWedge_eq_of_mul_mem_pure
    aOneEval bOneEval aOneEval_mul_bOneEval_mem_pure

private theorem quadraticANFOfForm_rationalOneJet :
    quadraticANFOfForm rationalOneJetTwo =
      linearANFTen aOneEval * linearANFTen bOneJet +
        linearANFTen aOneJet * linearANFTen bOneEval := by
  have hleft := quadraticANFOfForm_squarefreeWedge_eq_of_mul_mem_pure
    aOneEval bOneJet aOneEval_mul_bOneJet_mem_pure
  have hright := quadraticANFOfForm_squarefreeWedge_eq_of_mul_mem_pure
    aOneJet bOneEval aOneJet_mul_bOneEval_mem_pure
  change quadraticANFOfFormLinear
      (squarefreeWedge aOneEval bOneJet +
        squarefreeWedge aOneJet bOneEval) = _
  rw [map_add]
  change quadraticANFOfForm (squarefreeWedge aOneEval bOneJet) +
    quadraticANFOfForm (squarefreeWedge aOneJet bOneEval) = _
  rw [hleft, hright]

/-- ANF-algebra identity for a value--jet frame.  The hypotheses merely
identify the pure quadratic sections with their factored linear ANFs. -/
theorem quadraticOverlapCubic_valueJet_of_anf
    (A A' B B' : LinearForm) (value jet : TwoForm)
    (hvalue : quadraticANFOfForm value =
      linearANFTen A * linearANFTen B)
    (hjet : quadraticANFOfForm jet =
      linearANFTen A * linearANFTen B' +
        linearANFTen A' * linearANFTen B) :
    quadraticOverlapCubic value jet =
      ambientVectorWedgeTwo (A' + B') value := by
  rw [quadraticOverlapCubic,
    ← anfThreeProjectionTen_linear_mul_quadratic]
  congr 1
  rw [linearANFTen_add, hvalue, hjet]
  calc
    (linearANFTen A * linearANFTen B) *
          (linearANFTen A * linearANFTen B' +
            linearANFTen A' * linearANFTen B) =
        (linearANFTen A * linearANFTen A) *
            (linearANFTen B * linearANFTen B') +
          (linearANFTen B * linearANFTen B) *
            (linearANFTen A * linearANFTen A') := by ring
    _ = linearANFTen A * (linearANFTen B * linearANFTen B') +
          linearANFTen B * (linearANFTen A * linearANFTen A') := by
      rw [N4.anf_mul_self, N4.anf_mul_self]
    _ = (linearANFTen A' + linearANFTen B') *
          (linearANFTen A * linearANFTen B) := by ring

/-- Derivative linear form for the rational place one. -/
def rationalOneOverlapLinear : LinearForm := aOneJet + bOneJet

/-- Derivative linear form for the rational place at infinity. -/
def rationalInfinityOverlapLinear : LinearForm := aLinear 3 + bLinear 3

theorem quadraticOverlapCubic_rationalOne_value_jet :
    quadraticOverlapCubic rationalOneValueTwo rationalOneJetTwo =
      ambientVectorWedgeTwo rationalOneOverlapLinear
        rationalOneValueTwo := by
  exact quadraticOverlapCubic_valueJet_of_anf
    aOneEval aOneJet bOneEval bOneJet
    rationalOneValueTwo rationalOneJetTwo
    quadraticANFOfForm_rationalOneValue
    quadraticANFOfForm_rationalOneJet

private theorem quadraticANFOfForm_rationalInfinityValue :
    quadraticANFOfForm rationalInfinityValueTwo =
      linearANFTen (aLinear 4) * linearANFTen (bLinear 4) := by
  rw [rationalInfinityValueTwo,
    quadraticANFOfForm_targetPairTwo,
    linearANFTen_aLinear, linearANFTen_bLinear]

private theorem quadraticANFOfForm_rationalInfinityJet :
    quadraticANFOfForm rationalInfinityJetTwo =
      linearANFTen (aLinear 4) * linearANFTen (bLinear 3) +
        linearANFTen (aLinear 3) * linearANFTen (bLinear 4) := by
  change quadraticANFOfFormLinear
    (targetPairTwo 4 3 + targetPairTwo 3 4) = _
  rw [map_add]
  change quadraticANFOfForm (targetPairTwo 4 3) +
    quadraticANFOfForm (targetPairTwo 3 4) = _
  rw [quadraticANFOfForm_targetPairTwo,
    quadraticANFOfForm_targetPairTwo,
    linearANFTen_aLinear, linearANFTen_bLinear,
    linearANFTen_aLinear, linearANFTen_bLinear]

theorem quadraticOverlapCubic_rationalInfinity_value_jet :
    quadraticOverlapCubic rationalInfinityValueTwo
        rationalInfinityJetTwo =
      ambientVectorWedgeTwo rationalInfinityOverlapLinear
        rationalInfinityValueTwo := by
  exact quadraticOverlapCubic_valueJet_of_anf
    (aLinear 4) (aLinear 3) (bLinear 4) (bLinear 3)
    rationalInfinityValueTwo rationalInfinityJetTwo
    quadraticANFOfForm_rationalInfinityValue
    quadraticANFOfForm_rationalInfinityJet

/-- At place one the diagonal lowering of the derivative correction is
exactly the first-jet direction, hence remains in the old envelope. -/
private theorem aOneEval_aCoord_value (i : Fin 5) :
    aOneEval (aCoord i) = 1 := by
  fin_cases i <;>
    simp [aOneEval, aLinear, Pi.basisFun, Fin.sum_univ_succ, aCoord]

private theorem bOneEval_bCoord_value (i : Fin 5) :
    bOneEval (bCoord i) = 1 := by
  fin_cases i <;>
    simp [bOneEval, bLinear, Pi.basisFun, Fin.sum_univ_succ, bCoord]

private theorem aOneEval_bCoord_value (i : Fin 5) :
    aOneEval (bCoord i) = 0 := by
  fin_cases i <;>
    simp [aOneEval, aLinear, Pi.basisFun, Fin.sum_univ_succ,
      aCoord, bCoord]

private theorem bOneEval_aCoord_value (i : Fin 5) :
    bOneEval (aCoord i) = 0 := by
  fin_cases i <;>
    simp [bOneEval, bLinear, Pi.basisFun, Fin.sum_univ_succ,
      aCoord, bCoord]

private theorem aOneJet_bCoord_value (i : Fin 5) :
    aOneJet (bCoord i) = 0 := by
  fin_cases i <;>
    simp [aOneJet, aLinear, Pi.basisFun, aCoord, bCoord]

private theorem bOneJet_aCoord_value (i : Fin 5) :
    bOneJet (aCoord i) = 0 := by
  fin_cases i <;>
    simp [bOneJet, bLinear, Pi.basisFun, aCoord, bCoord]

theorem ambientBooleanContraction_rationalOneOverlapLinear_value :
    ambientBooleanContraction rationalOneOverlapLinear
      rationalOneValueTwo = rationalOneJetTwo := by
  apply twoForm_ext_blocks
  · intro i j hij
    simp [ambientBooleanContraction_pair, rationalOneOverlapLinear,
      rationalOneValueTwo, rationalOneJetTwo,
      aOneEval_aCoord_value, bOneEval_aCoord_value,
      bOneJet_aCoord_value]
  · intro i j hij
    simp [ambientBooleanContraction_pair, rationalOneOverlapLinear,
      rationalOneValueTwo, rationalOneJetTwo,
      aOneEval_bCoord_value, bOneEval_bCoord_value,
      aOneJet_bCoord_value]
  · intro i j
    simp [ambientBooleanContraction_pair, rationalOneOverlapLinear,
      rationalOneValueTwo, rationalOneJetTwo,
      aOneEval_aCoord_value, bOneEval_bCoord_value,
      aOneEval_bCoord_value, bOneEval_aCoord_value,
      aOneJet_bCoord_value, bOneJet_aCoord_value]
    ring

theorem ambientBooleanContraction_rationalOneOverlapLinear_value_mem :
    ambientBooleanContraction rationalOneOverlapLinear
      rationalOneValueTwo ∈ firstOrderEnvelopeTwoSpace := by
  rw [ambientBooleanContraction_rationalOneOverlapLinear_value]
  simpa [ExceptionalIndependentPlane.right] using
    ExceptionalIndependentPlane.right_mem_firstOrderEnvelope
      (.rationalJet 1)

@[simp] theorem
    ambientBooleanContraction_rationalInfinityOverlapLinear_value :
    ambientBooleanContraction rationalInfinityOverlapLinear
      rationalInfinityValueTwo = 0 := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [ambientBooleanContraction_pair,
      rationalInfinityOverlapLinear, rationalInfinityValueTwo,
      targetPairTwo, aLinear, bLinear, Pi.basisFun, aCoord, bCoord]

/-- Generic exact correction lift for a value--jet plane whose overlap is
the value wedged with a fixed derivative form. -/
theorem exactBooleanCorrection_decomposition_of_overlap
    (value jet : TwoForm) (f : LinearForm)
    (hoverlap : quadraticOverlapCubic value jet =
      ambientVectorWedgeTwo f value)
    (hfcontract : ambientBooleanContraction f value ∈
      firstOrderEnvelopeTwoSpace)
    (hnormalized : ∀ x y : LinearForm,
      factorPlaneCubic x y value jet = 0 →
        ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
          squarefreeWedge x y + ambientBooleanContraction x jet +
              ambientBooleanContraction y value =
            r + squarefreeWedge x z)
    (x y : LinearForm)
    (hcubic : exactLowProductCubic x y value jet = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y + ambientBooleanContraction x jet +
          ambientBooleanContraction y value =
        r + squarefreeWedge x z := by
  have hcubicNormalized :
      factorPlaneCubic x (y + f) value jet = 0 := by
    funext i j k
    have h := congrFun (congrFun (congrFun hcubic i) j) k
    have ho := congrFun (congrFun (congrFun hoverlap i) j) k
    simp only [exactLowProductCubic, factorPlaneCubic,
      ambientVectorWedgeTwo, N4.vectorWedgeTwoN, Pi.add_apply] at h ho ⊢
    rw [ho] at h
    ring_nf at h ⊢
    exact h
  rcases hnormalized x (y + f) hcubicNormalized with
    ⟨r, hr, z, hdecomp⟩
  refine ⟨r + ambientBooleanContraction f value,
    firstOrderEnvelopeTwoSpace.add_mem hr hfcontract, z + f, ?_⟩
  rw [squarefreeWedge_add_right,
    ambientBooleanContraction_add_left] at hdecomp
  rw [squarefreeWedge_add_right]
  let original : TwoForm :=
    squarefreeWedge x y + ambientBooleanContraction x jet +
      ambientBooleanContraction y value
  let extra : TwoForm :=
    squarefreeWedge x f + ambientBooleanContraction f value
  have hdecomp' : original + extra = r + squarefreeWedge x z := by
    calc
      original + extra =
          squarefreeWedge x y + squarefreeWedge x f +
            ambientBooleanContraction x jet +
            (ambientBooleanContraction y value +
              ambientBooleanContraction f value) := by
        simp only [original, extra]
        abel
      _ = r + squarefreeWedge x z := hdecomp
  have hself : extra + extra = 0 := by
    funext s
    exact CharTwo.add_self_eq_zero (extra s)
  change original =
    (r + ambientBooleanContraction f value) +
      (squarefreeWedge x z + squarefreeWedge x f)
  calc
    original = (original + extra) + extra := by
      calc
        original = original + 0 := by rw [add_zero]
        _ = original + (extra + extra) := by rw [hself]
        _ = (original + extra) + extra := by abel
    _ = (r + squarefreeWedge x z) + extra := by rw [hdecomp']
    _ = (r + ambientBooleanContraction f value) +
        (squarefreeWedge x z + squarefreeWedge x f) := by
      simp only [extra]
      abel

theorem rationalOne_exactBooleanCorrection_decomposition
    (x y : LinearForm)
    (hcubic : exactLowProductCubic x y rationalOneValueTwo
      rationalOneJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x rationalOneJetTwo +
          ambientBooleanContraction y rationalOneValueTwo =
        r + squarefreeWedge x z := by
  exact exactBooleanCorrection_decomposition_of_overlap
    rationalOneValueTwo rationalOneJetTwo rationalOneOverlapLinear
    quadraticOverlapCubic_rationalOne_value_jet
    ambientBooleanContraction_rationalOneOverlapLinear_value_mem
    rationalOne_booleanCorrection_decomposition x y hcubic

theorem rationalInfinity_exactBooleanCorrection_decomposition
    (x y : LinearForm)
    (hcubic : exactLowProductCubic x y rationalInfinityValueTwo
      rationalInfinityJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x rationalInfinityJetTwo +
          ambientBooleanContraction y rationalInfinityValueTwo =
        r + squarefreeWedge x z := by
  apply exactBooleanCorrection_decomposition_of_overlap
    rationalInfinityValueTwo rationalInfinityJetTwo
    rationalInfinityOverlapLinear
    quadraticOverlapCubic_rationalInfinity_value_jet
    (by
      rw [ambientBooleanContraction_rationalInfinityOverlapLinear_value]
      exact firstOrderEnvelopeTwoSpace.zero_mem)
    rationalInfinity_booleanCorrection_decomposition x y hcubic

/-- A normalized local/dependent structure theorem lifts to exact Boolean
semantics once its fixed value--jet overlap has been identified. -/
theorem exactLocalDependentStructure_of_overlap
    (value jet : TwoForm) (f : LinearForm)
    (hoverlap : quadraticOverlapCubic value jet =
      ambientVectorWedgeTwo f value)
    (hstructure : ∀ ell m x y : LinearForm, ∀ c : TargetCoeff,
      c ∈ firstOrderEnvelopeCoeffSpace →
      factorPlaneCubic ell m value jet =
          factorPlaneCubic x y 0 (targetTwo c) →
      ∃ α β : F₂, ∃ remote : TwoForm,
        remote ∈ firstOrderEnvelopeTwoSpace ∧
        targetTwo c = α • value + β • jet + remote ∧
        ambientVectorWedgeTwo x remote = 0)
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : exactLowProductCubic ell m value jet =
      exactLowProductCubic x y 0 (targetTwo c)) :
    ∃ α β : F₂, ∃ remote : TwoForm,
      remote ∈ firstOrderEnvelopeTwoSpace ∧
      targetTwo c = α • value + β • jet + remote ∧
      ambientVectorWedgeTwo x remote = 0 := by
  have hnormalized :
      factorPlaneCubic ell (m + f) value jet =
        factorPlaneCubic x y 0 (targetTwo c) := by
    have hbase := hcubic
    rw [exactLowProductCubic, exactLowProductCubic,
      quadraticOverlapCubic_zero_left, zero_add, hoverlap] at hbase
    funext i j k
    have h := congrFun (congrFun (congrFun hbase i) j) k
    simp only [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, Pi.add_apply] at h ⊢
    ring_nf at h ⊢
    exact h
  exact hstructure ell (m + f) x y c hc hnormalized

theorem rationalOne_exact_local_dependent_structure
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : exactLowProductCubic ell m rationalOneValueTwo
      rationalOneJetTwo = exactLowProductCubic x y 0 (targetTwo c)) :
    ∃ α β : F₂, ∃ remote : TwoForm,
      remote ∈ firstOrderEnvelopeTwoSpace ∧
      targetTwo c = α • rationalOneValueTwo +
        β • rationalOneJetTwo + remote ∧
      ambientVectorWedgeTwo x remote = 0 := by
  exact exactLocalDependentStructure_of_overlap
    rationalOneValueTwo rationalOneJetTwo rationalOneOverlapLinear
    quadraticOverlapCubic_rationalOne_value_jet
    rationalOne_local_dependent_structure ell m x y c hc hcubic

theorem rationalInfinity_exact_local_dependent_structure
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : exactLowProductCubic ell m rationalInfinityValueTwo
      rationalInfinityJetTwo = exactLowProductCubic x y 0 (targetTwo c)) :
    ∃ α β : F₂, ∃ remote : TwoForm,
      remote ∈ firstOrderEnvelopeTwoSpace ∧
      targetTwo c = α • rationalInfinityValueTwo +
        β • rationalInfinityJetTwo + remote ∧
      ambientVectorWedgeTwo x remote = 0 := by
  exact exactLocalDependentStructure_of_overlap
    rationalInfinityValueTwo rationalInfinityJetTwo
    rationalInfinityOverlapLinear
    quadraticOverlapCubic_rationalInfinity_value_jet
    rationalInfinity_local_dependent_structure ell m x y c hc hcubic

/-- Uniform exact local/dependent shadow calculation. -/
theorem rationalLocal_exact_dependent_shadow_decomposition
    (value jet : TwoForm)
    (hvalue : value ∈ firstOrderEnvelopeTwoSpace)
    (hjet : jet ∈ firstOrderEnvelopeTwoSpace)
    (hhadamard : ambientTwoHadamard value jet ∈
      firstOrderEnvelopeTwoSpace)
    (hcorrection : ∀ X Y : LinearForm,
      exactLowProductCubic X Y value jet = 0 →
        ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
          squarefreeWedge X Y + ambientBooleanContraction X jet +
              ambientBooleanContraction Y value =
            r + squarefreeWedge X z)
    (a b a' b' α β : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = α • value + β • jet + remote)
    (hcubic : exactLowProductCubic ell m value jet =
      exactLowProductCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m value jet +
          lowProductQuadraticShadow a' b' x y 0 d =
        r + squarefreeWedge u v + squarefreeWedge s t := by
  have hdmem : d ∈ firstOrderEnvelopeTwoSpace := by
    rw [hd]
    exact firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue)
        (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)) hremote
  by_cases hx : x = 0
  · subst x
    have hcubicZero : exactLowProductCubic ell m value jet = 0 := by
      have hcubicWedge : exactLowProductCubic ell m value jet =
          ambientVectorWedgeTwo 0 d := by
        simpa only [exactLowProductCubic,
          quadraticOverlapCubic_zero_left, factorPlaneCubic_zero_left,
          zero_add] using hcubic
      have hzero : ambientVectorWedgeTwo 0 d = 0 := by
        funext i j k
        simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]
      exact hcubicWedge.trans hzero
    rcases hcorrection ell m hcubicZero with ⟨r₀, hr₀, z, hcorr⟩
    let r : TwoForm :=
      a • jet + b • value + a' • d + r₀ + ambientTwoHadamard value jet
    refine ⟨r, ?_, ell, z, 0, 0, ?_⟩
    · exact firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.add_mem
          (firstOrderEnvelopeTwoSpace.add_mem
            (firstOrderEnvelopeTwoSpace.add_mem
              (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)
              (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue))
            (firstOrderEnvelopeTwoSpace.smul_mem _ hdmem)) hr₀) hhadamard
    · rw [show squarefreeWedge (0 : LinearForm) 0 = 0 by simp, add_zero]
      funext q
      rcases QuadraticIndex.exists_pair q with ⟨i, j, hij, rfl⟩
      have hcorr' := congrFun hcorr (quadraticPair i j hij)
      simp only [Pi.add_apply, lowProductQuadraticShadow_pair,
        Pi.zero_apply, mul_zero, add_zero, zero_mul] at hcorr' ⊢
      dsimp only [r]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair, ambientBooleanContraction_pair,
        ambientTwoHadamard] at hcorr' ⊢
      linear_combination hcorr'
  · let X : LinearForm := ell + β • x
    let Y : LinearForm := m + α • x
    have hcubicZero : exactLowProductCubic X Y value jet = 0 := by
      funext i j k
      have hc := congrFun (congrFun (congrFun hcubic i) j) k
      have hr := congrFun (congrFun (congrFun hxremote i) j) k
      simp only [exactLowProductCubic, quadraticOverlapCubic_zero_left,
        factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
        Pi.add_apply, ambientTwoCoeff_zero] at hc hr ⊢
      simp only [X, Y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hd] at hc
      simp only [ambientTwoCoeff_add, ambientTwoCoeff_smul] at hc
      linear_combination
        (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
        hc + hr
    rcases hcorrection X Y hcubicZero with ⟨r₀, hr₀, z, hcorr⟩
    rcases ambientBooleanContraction_of_vectorWedge_zero
        x remote hx hxremote with ⟨w, _hremoteWedge, hremoteContraction⟩
    let r : TwoForm :=
      a • jet + b • value + a' • d + remote + r₀ +
        ambientTwoHadamard value jet
    let t : LinearForm :=
      α • ell + β • m + y + ambientDiagonalProduct x w
    refine ⟨r, ?_, X, z, x, t, ?_⟩
    · exact firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.add_mem
          (firstOrderEnvelopeTwoSpace.add_mem
            (firstOrderEnvelopeTwoSpace.add_mem
              (firstOrderEnvelopeTwoSpace.add_mem
                (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)
                (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue))
              (firstOrderEnvelopeTwoSpace.smul_mem _ hdmem)) hremote) hr₀)
          hhadamard
    · funext q
      rcases QuadraticIndex.exists_pair q with ⟨i, j, hij, rfl⟩
      have hcorr' := congrFun hcorr (quadraticPair i j hij)
      have hcontract := congrFun hremoteContraction
        (quadraticPair i j hij)
      simp only [Pi.add_apply, lowProductQuadraticShadow_pair,
        Pi.zero_apply, mul_zero, add_zero, zero_mul] at hcorr' ⊢
      simp only [ambientBooleanContraction_pair, Pi.add_apply] at hcontract
      dsimp only [r]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair, ambientBooleanContraction_pair,
        ambientTwoHadamard] at hcorr' ⊢
      simp only [X, Y, t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        at hcorr' ⊢
      rw [hd]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination
        (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
        hcorr' + hcontract

/-- Exact local/dependent missing-coset exclusion from structural data. -/
theorem rationalLocal_exact_dependent_shadow_not_missingCoset
    (value jet : TwoForm)
    (hvalue : value ∈ firstOrderEnvelopeTwoSpace)
    (hjet : jet ∈ firstOrderEnvelopeTwoSpace)
    (hhadamard : ambientTwoHadamard value jet ∈
      firstOrderEnvelopeTwoSpace)
    (hcorrection : ∀ X Y : LinearForm,
      exactLowProductCubic X Y value jet = 0 →
        ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
          squarefreeWedge X Y + ambientBooleanContraction X jet +
              ambientBooleanContraction Y value =
            r + squarefreeWedge X z)
    (a b a' b' α β : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = α • value + β • jet + remote)
    (hcubic : exactLowProductCubic ell m value jet =
      exactLowProductCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m value jet +
        lowProductQuadraticShadow a' b' x y 0 d ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  rcases rationalLocal_exact_dependent_shadow_decomposition
      value jet hvalue hjet hhadamard hcorrection
      a b a' b' α β ell m x y d remote hremote hd hcubic hxremote with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  exact hdecomp.symm.trans hmissing

theorem rationalOne_actual_exact_local_dependent_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : exactLowProductCubic ell m rationalOneValueTwo
      rationalOneJetTwo = exactLowProductCubic x y 0 (targetTwo c))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalOneValueTwo
          rationalOneJetTwo +
        lowProductQuadraticShadow a' b' x y 0 (targetTwo c) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases rationalOne_exact_local_dependent_structure
      ell m x y c hc hcubic with ⟨α, β, remote, hremote, hd, hxremote⟩
  have hvalue : rationalOneValueTwo ∈ firstOrderEnvelopeTwoSpace := by
    simpa [ExceptionalIndependentPlane.left] using
      ExceptionalIndependentPlane.left_mem_firstOrderEnvelope
        (.rationalJet 1)
  have hjet : rationalOneJetTwo ∈ firstOrderEnvelopeTwoSpace := by
    simpa [ExceptionalIndependentPlane.right] using
      ExceptionalIndependentPlane.right_mem_firstOrderEnvelope
        (.rationalJet 1)
  have hhadamard : ambientTwoHadamard rationalOneValueTwo
      rationalOneJetTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [ambientTwoHadamard_rationalOneValue_jet]
    exact hjet
  exact rationalLocal_exact_dependent_shadow_not_missingCoset
    rationalOneValueTwo rationalOneJetTwo hvalue hjet hhadamard
    rationalOne_exactBooleanCorrection_decomposition
    a b a' b' α β ell m x y (targetTwo c) remote
    hremote hd hcubic hxremote u hu

theorem rationalInfinity_actual_exact_local_dependent_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : exactLowProductCubic ell m rationalInfinityValueTwo
      rationalInfinityJetTwo = exactLowProductCubic x y 0 (targetTwo c))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalInfinityValueTwo
          rationalInfinityJetTwo +
        lowProductQuadraticShadow a' b' x y 0 (targetTwo c) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases rationalInfinity_exact_local_dependent_structure
      ell m x y c hc hcubic with ⟨α, β, remote, hremote, hd, hxremote⟩
  have hvalue : rationalInfinityValueTwo ∈
      firstOrderEnvelopeTwoSpace := by
    simpa [ExceptionalIndependentPlane.left] using
      ExceptionalIndependentPlane.left_mem_firstOrderEnvelope
        (.rationalJet 2)
  have hjet : rationalInfinityJetTwo ∈ firstOrderEnvelopeTwoSpace := by
    simpa [ExceptionalIndependentPlane.right] using
      ExceptionalIndependentPlane.right_mem_firstOrderEnvelope
        (.rationalJet 2)
  have hhadamard : ambientTwoHadamard rationalInfinityValueTwo
      rationalInfinityJetTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [ambientTwoHadamard_rationalInfinityValue_jet]
    exact firstOrderEnvelopeTwoSpace.zero_mem
  exact rationalLocal_exact_dependent_shadow_not_missingCoset
    rationalInfinityValueTwo rationalInfinityJetTwo hvalue hjet hhadamard
    rationalInfinity_exactBooleanCorrection_decomposition
    a b a' b' α β ell m x y (targetTwo c) remote
    hremote hd hcubic hxremote u hu

/-- Uniform exact local/dependent exclusion at the three rational
value--jet planes. -/
theorem rationalJet_actual_exact_local_dependent_shadow_not_missingCoset
    (place : Fin 3) (a b a' b' : F₂)
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : exactLowProductCubic ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right =
      exactLowProductCubic x y 0 (targetTwo c))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right +
        lowProductQuadraticShadow a' b' x y 0 (targetTwo c) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  fin_cases place
  · simpa [ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      rationalZero_actual_exact_local_dependent_shadow_not_missingCoset
        a b a' b' ell m x y c hc hcubic u hu
  · simpa [ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      rationalOne_actual_exact_local_dependent_shadow_not_missingCoset
        a b a' b' ell m x y c hc hcubic u hu
  · simpa [ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      rationalInfinity_actual_exact_local_dependent_shadow_not_missingCoset
        a b a' b' ell m x y c hc hcubic u hu

end
end N5
end UnrestrictedBooleanMul
