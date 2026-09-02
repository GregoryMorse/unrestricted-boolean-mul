import UnrestrictedBooleanMul.N5.EnvelopeLocalDependent
import UnrestrictedBooleanMul.N5.CubicSemantic
import UnrestrictedBooleanMul.N5.CubicOverlapBasis

/-!
# Exact Boolean semantics for a rational local/dependent comparison

The exterior cubic used by the envelope classifier omits the cubic term
created when two quadratic Boolean monomials overlap in one variable.  On the
rational-zero value--jet plane that term is itself exterior multiplication by
the fixed linear form `a₁ + b₁`.  Absorbing it into the second linear part
preserves the one-decomposable Boolean correction used by the local shadow
argument.

This is the exact-ANF repair needed before the normalized envelope theorem can
be used at a circuit boundary.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The fixed linear correction whose product with the rational-zero value
is the Boolean cubic overlap of the value--jet plane. -/
def rationalZeroOverlapLinear : LinearForm :=
  aLinear 1 + bLinear 1

/-- The canonical pure-quadratic section sends a target pair back to its
two-variable Boolean monomial. -/
private theorem quadraticANFOfForm_targetPairTwo (i j : Fin 5) :
    quadraticANFOfForm (targetPairTwo i j) =
      X (aCoord i) * X (bCoord j) := by
  have hij : aCoord i ≠ bCoord j := aCoord_ne_bCoord i j
  have ha : aLinear i = coordinateLinearTen (aCoord i) := by
    classical
    ext k
    simp [aLinear, coordinateLinearTen, Pi.basisFun, Pi.single_apply]
  have hb : bLinear j = coordinateLinearTen (bCoord j) := by
    classical
    ext k
    simp [bLinear, coordinateLinearTen, Pi.basisFun, Pi.single_apply]
  rw [targetPairTwo, ha, hb,
    ← quadraticBasisPair_eq_wedge (aCoord i) (bCoord j) hij,
    quadraticANFOfForm_basis]
  simp [quadraticPair, X]

/-- Exact coordinate identity for the Boolean cubic overlap at zero. -/
theorem quadraticOverlapCubic_rationalZero_value_jet :
    quadraticOverlapCubic rationalZeroValueTwo rationalZeroJetTwo =
      ambientVectorWedgeTwo rationalZeroOverlapLinear
        rationalZeroValueTwo := by
  have ha : aLinear 1 = coordinateLinearTen (aCoord 1) := by
    classical
    ext k
    simp [aLinear, coordinateLinearTen, Pi.basisFun, Pi.single_apply]
  have hb : bLinear 1 = coordinateLinearTen (bCoord 1) := by
    classical
    ext k
    simp [bLinear, coordinateLinearTen, Pi.basisFun, Pi.single_apply]
  have hlinear : linearANFTen rationalZeroOverlapLinear =
      X (aCoord 1) + X (bCoord 1) := by
    rw [rationalZeroOverlapLinear, linearANFTen_add, ha, hb,
      linearANFTen_coordinate, linearANFTen_coordinate]
  have hvalue : quadraticANFOfForm rationalZeroValueTwo =
      X (aCoord 0) * X (bCoord 0) := by
    exact quadraticANFOfForm_targetPairTwo 0 0
  have hjet : quadraticANFOfForm rationalZeroJetTwo =
      X (aCoord 0) * X (bCoord 1) +
        X (aCoord 1) * X (bCoord 0) := by
    change quadraticANFOfFormLinear rationalZeroJetTwo = _
    rw [rationalZeroJetTwo, map_add]
    change quadraticANFOfForm (targetPairTwo 0 1) +
      quadraticANFOfForm (targetPairTwo 1 0) = _
    rw [
      quadraticANFOfForm_targetPairTwo,
      quadraticANFOfForm_targetPairTwo]
  rw [quadraticOverlapCubic,
    ← anfThreeProjectionTen_linear_mul_quadratic]
  congr 1
  rw [hlinear, hvalue, hjet]
  simp only [add_mul, mul_add]
  calc
    X (aCoord 0) * X (bCoord 0) *
          (X (aCoord 0) * X (bCoord 1)) +
        X (aCoord 0) * X (bCoord 0) *
          (X (aCoord 1) * X (bCoord 0)) =
        (X (aCoord 0) * X (aCoord 0)) *
            (X (bCoord 0) * X (bCoord 1)) +
          (X (bCoord 0) * X (bCoord 0)) *
            (X (aCoord 0) * X (aCoord 1)) := by ring
    _ = X (aCoord 0) * (X (bCoord 0) * X (bCoord 1)) +
          X (bCoord 0) * (X (aCoord 0) * X (aCoord 1)) := by
      rw [N4.anf_mul_self, N4.anf_mul_self]
    _ = X (aCoord 1) * (X (aCoord 0) * X (bCoord 0)) +
          X (bCoord 1) * (X (aCoord 0) * X (bCoord 0)) := by ring

/-- The overlap correction does not itself create a Boolean quadratic
contraction against the rational-zero value form. -/
@[simp] theorem ambientBooleanContraction_rationalZeroOverlapLinear_value :
    ambientBooleanContraction rationalZeroOverlapLinear
      rationalZeroValueTwo = 0 := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [ambientBooleanContraction_pair,
      rationalZeroOverlapLinear, rationalZeroValueTwo, targetPairTwo,
      aLinear, bLinear, Pi.basisFun, aCoord, bCoord]

/-- Exact Boolean version of the local correction decomposition.  Compared
with `rationalZero_booleanCorrection_decomposition`, the hypothesis contains
the literal quadratic--quadratic cubic overlap.  The conclusion still needs
only one decomposable two-form modulo the first-order envelope. -/
theorem rationalZero_exactBooleanCorrection_decomposition
    (x y : LinearForm)
    (hcubic : exactLowProductCubic x y rationalZeroValueTwo
      rationalZeroJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x rationalZeroJetTwo +
          ambientBooleanContraction y rationalZeroValueTwo =
        r + squarefreeWedge x z := by
  have hnormalized :
      factorPlaneCubic x (y + rationalZeroOverlapLinear)
        rationalZeroValueTwo rationalZeroJetTwo = 0 := by
    funext i j k
    have h := congrFun (congrFun (congrFun hcubic i) j) k
    have hoverlap := congrFun (congrFun
      (congrFun quadraticOverlapCubic_rationalZero_value_jet i) j) k
    simp only [exactLowProductCubic, factorPlaneCubic,
      ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      Pi.add_apply] at h hoverlap ⊢
    rw [hoverlap] at h
    ring_nf at h ⊢
    exact h
  rcases rationalZero_booleanCorrection_decomposition
      x (y + rationalZeroOverlapLinear) hnormalized with
    ⟨r, hr, z, hdecomp⟩
  refine ⟨r, hr, z + rationalZeroOverlapLinear, ?_⟩
  rw [squarefreeWedge_add_right,
    ambientBooleanContraction_add_left,
    ambientBooleanContraction_rationalZeroOverlapLinear_value,
    add_zero] at hdecomp
  rw [squarefreeWedge_add_right]
  let correction : TwoForm :=
    squarefreeWedge x rationalZeroOverlapLinear
  have hself : correction + correction = 0 := by
    funext s
    simp [correction]
  have hdecomp' :
      (squarefreeWedge x y +
          ambientBooleanContraction x rationalZeroJetTwo +
          ambientBooleanContraction y rationalZeroValueTwo) + correction =
        r + squarefreeWedge x z := by
    calc
      _ = squarefreeWedge x y +
            squarefreeWedge x rationalZeroOverlapLinear +
            ambientBooleanContraction x rationalZeroJetTwo +
            ambientBooleanContraction y rationalZeroValueTwo := by
        simp only [correction]
        abel
      _ = r + squarefreeWedge x z := hdecomp
  calc
    squarefreeWedge x y + ambientBooleanContraction x rationalZeroJetTwo +
          ambientBooleanContraction y rationalZeroValueTwo =
        (squarefreeWedge x y +
              ambientBooleanContraction x rationalZeroJetTwo +
              ambientBooleanContraction y rationalZeroValueTwo + correction) +
          correction := by
      calc
        _ = (squarefreeWedge x y +
              ambientBooleanContraction x rationalZeroJetTwo +
              ambientBooleanContraction y rationalZeroValueTwo) + 0 := by
          rw [add_zero]
        _ = (squarefreeWedge x y +
              ambientBooleanContraction x rationalZeroJetTwo +
              ambientBooleanContraction y rationalZeroValueTwo) +
              (correction + correction) := by rw [hself]
        _ = _ := by abel
    _ = (r + squarefreeWedge x z) + correction := by
      rw [hdecomp']
    _ = r + (squarefreeWedge x z + correction) := by abel

/-- Exact-ANF structural classification for a rational-zero local plane
against a dependent plane.  The fixed cubic overlap is absorbed into the
second local linear part before invoking the normalized classification. -/
theorem rationalZero_exact_local_dependent_structure
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : exactLowProductCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo =
      exactLowProductCubic x y 0 (targetTwo c)) :
    ∃ α β : F₂, ∃ remote : TwoForm,
      remote ∈ firstOrderEnvelopeTwoSpace ∧
      targetTwo c = α • rationalZeroValueTwo +
        β • rationalZeroJetTwo + remote ∧
      ambientVectorWedgeTwo x remote = 0 := by
  have hnormalized :
      factorPlaneCubic ell (m + rationalZeroOverlapLinear)
          rationalZeroValueTwo rationalZeroJetTwo =
        factorPlaneCubic x y 0 (targetTwo c) := by
    have hbase := hcubic
    rw [exactLowProductCubic, exactLowProductCubic,
      quadraticOverlapCubic_zero_left, zero_add,
      quadraticOverlapCubic_rationalZero_value_jet] at hbase
    funext i j k
    have h := congrFun (congrFun (congrFun hbase i) j) k
    simp only [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, Pi.add_apply] at h ⊢
    ring_nf at h ⊢
    exact h
  exact rationalZero_local_dependent_structure
    ell (m + rationalZeroOverlapLinear) x y c hc hnormalized

/-- Exact-ANF local/dependent shadow decomposition.  This is the literal
Boolean analogue of `rationalZero_local_dependent_shadow_decomposition`;
the conclusion retains the sharp bound of two decomposable corrections. -/
theorem rationalZero_exact_local_dependent_shadow_decomposition
    (a b a' b' α β : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = α • rationalZeroValueTwo +
      β • rationalZeroJetTwo + remote)
    (hcubic :
      exactLowProductCubic ell m rationalZeroValueTwo
          rationalZeroJetTwo =
        exactLowProductCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' x y 0 d =
      r + squarefreeWedge u v + squarefreeWedge s t := by
  have hvalue := rationalZeroValueTwo_mem_firstOrderEnvelope
  have hjet := rationalZeroJetTwo_mem_firstOrderEnvelope
  have hdmem : d ∈ firstOrderEnvelopeTwoSpace := by
    rw [hd]
    exact firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue)
        (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)) hremote
  by_cases hx : x = 0
  · subst x
    have hcubicZero :
        exactLowProductCubic ell m rationalZeroValueTwo
          rationalZeroJetTwo = 0 := by
      have hcubicWedge :
          exactLowProductCubic ell m rationalZeroValueTwo
              rationalZeroJetTwo = ambientVectorWedgeTwo 0 d := by
        simpa only [exactLowProductCubic,
          quadraticOverlapCubic_zero_left, factorPlaneCubic_zero_left,
          zero_add] using hcubic
      have hzero : ambientVectorWedgeTwo 0 d = 0 := by
        funext i j k
        simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]
      exact hcubicWedge.trans hzero
    rcases rationalZero_exactBooleanCorrection_decomposition
        ell m hcubicZero with ⟨r₀, hr₀, z, hcorrection⟩
    let r : TwoForm :=
      a • rationalZeroJetTwo + b • rationalZeroValueTwo + a' • d + r₀
    refine ⟨r, ?_, ell, z, 0, 0, ?_⟩
    · exact firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.add_mem
          (firstOrderEnvelopeTwoSpace.add_mem
            (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)
            (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue))
          (firstOrderEnvelopeTwoSpace.smul_mem _ hdmem)) hr₀
    · rw [show squarefreeWedge (0 : LinearForm) 0 = 0 by simp,
        add_zero]
      funext q
      rcases QuadraticIndex.exists_pair q with ⟨i, j, hij, rfl⟩
      have hcorr := congrFun hcorrection (quadraticPair i j hij)
      have hhad := congrFun ambientTwoHadamard_rationalZeroValue_jet
        (quadraticPair i j hij)
      simp only [Pi.add_apply, lowProductQuadraticShadow_pair,
        Pi.zero_apply, mul_zero, add_zero, zero_mul] at hcorr ⊢
      simp only [ambientTwoHadamard, Pi.zero_apply] at hhad
      change _ =
        (a • rationalZeroJetTwo + b • rationalZeroValueTwo + a' • d + r₀)
            (quadraticPair i j hij) + _ at ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair, ambientBooleanContraction_pair] at hcorr ⊢
      linear_combination hcorr + hhad
  · let X : LinearForm := ell + β • x
    let Y : LinearForm := m + α • x
    have hcubicZero :
        exactLowProductCubic X Y rationalZeroValueTwo
          rationalZeroJetTwo = 0 := by
      funext i j k
      have hc := congrFun (congrFun (congrFun hcubic i) j) k
      have hr := congrFun (congrFun (congrFun hxremote i) j) k
      simp only [exactLowProductCubic, quadraticOverlapCubic_zero_left,
        factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, Pi.add_apply,
        ambientTwoCoeff_zero] at hc hr ⊢
      simp only [X, Y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hd] at hc
      simp only [ambientTwoCoeff_add, ambientTwoCoeff_smul] at hc
      linear_combination
        (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
        hc + hr
    rcases rationalZero_exactBooleanCorrection_decomposition
        X Y hcubicZero with ⟨r₀, hr₀, z, hcorrection⟩
    rcases ambientBooleanContraction_of_vectorWedge_zero
        x remote hx hxremote with ⟨w, _hremoteWedge, hremoteContraction⟩
    let r : TwoForm :=
      a • rationalZeroJetTwo + b • rationalZeroValueTwo + a' • d +
        remote + r₀
    let t : LinearForm :=
      α • ell + β • m + y + ambientDiagonalProduct x w
    refine ⟨r, ?_, X, z, x, t, ?_⟩
    · exact firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.add_mem
          (firstOrderEnvelopeTwoSpace.add_mem
            (firstOrderEnvelopeTwoSpace.add_mem
              (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)
              (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue))
            (firstOrderEnvelopeTwoSpace.smul_mem _ hdmem)) hremote) hr₀
    · funext q
      rcases QuadraticIndex.exists_pair q with ⟨i, j, hij, rfl⟩
      have hcorr := congrFun hcorrection (quadraticPair i j hij)
      have hcontract := congrFun hremoteContraction
        (quadraticPair i j hij)
      have hhad := congrFun ambientTwoHadamard_rationalZeroValue_jet
        (quadraticPair i j hij)
      simp only [Pi.add_apply, lowProductQuadraticShadow_pair,
        Pi.zero_apply, mul_zero, add_zero, zero_mul] at hcorr ⊢
      simp only [ambientBooleanContraction_pair, Pi.add_apply] at hcontract
      simp only [ambientTwoHadamard, Pi.zero_apply] at hhad
      dsimp only [r]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair, ambientBooleanContraction_pair] at hcorr ⊢
      simp only [X, Y, t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        at hcorr ⊢
      rw [hd]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination
        (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
        hcorr + hcontract + hhad

/-- Exact-ANF missing-coset exclusion for the rational-zero
local/dependent comparison. -/
theorem rationalZero_exact_local_dependent_shadow_not_missingCoset
    (a b a' b' α β : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = α • rationalZeroValueTwo +
      β • rationalZeroJetTwo + remote)
    (hcubic : exactLowProductCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo = exactLowProductCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' x y 0 d ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  rcases rationalZero_exact_local_dependent_shadow_decomposition
      a b a' b' α β ell m x y d remote hremote hd hcubic hxremote with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  exact hdecomp.symm.trans hmissing

/-- Exact-ANF rational-zero local/dependent branch with its structural
hypotheses discharged from the literal cubic equation. -/
theorem rationalZero_actual_exact_local_dependent_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : exactLowProductCubic ell m rationalZeroValueTwo
      rationalZeroJetTwo = exactLowProductCubic x y 0 (targetTwo c))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' x y 0 (targetTwo c) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases rationalZero_exact_local_dependent_structure ell m x y c hc hcubic with
    ⟨α, β, remote, hremote, hd, hxremote⟩
  exact rationalZero_exact_local_dependent_shadow_not_missingCoset
    a b a' b' α β ell m x y (targetTwo c) remote
      hremote hd hcubic hxremote u hu

end
end N5
end UnrestrictedBooleanMul
