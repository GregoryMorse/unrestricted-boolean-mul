import UnrestrictedBooleanMul.N5.QuadraticReturnFeedback
import UnrestrictedBooleanMul.N5.RationalEnvelopeSymmetry

/-!
# Rational-place symmetry for quadratic returns

Translation and reversal act on the ten input coordinates and on squarefree
quadratic forms.  This file constructs the induced tensor action on ambient
four-forms and proves that it commutes with exterior multiplication.  The
four canonical rational-return kernel certificates therefore transport to
all six elements of the rational-place symmetry group.

The proof is linear algebra on exterior coordinates.  It does not enumerate
circuits, Boolean assignments, or quadratic quotient classes.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Tensor-coordinate action induced by a rational-place substitution on
ambient four-forms.  It is used only on alternating four-forms. -/
def rationalPlaceFourFormLinear (theta : Fin 2) :
    AmbientFourForm →ₗ[F₂] AmbientFourForm where
  toFun h := fun i j k l =>
    ∑ a : Fin 10, ∑ b : Fin 10, ∑ c : Fin 10, ∑ d : Fin 10,
      rationalPlaceInputChange theta a i *
        rationalPlaceInputChange theta b j *
        rationalPlaceInputChange theta c k *
        rationalPlaceInputChange theta d l * h a b c d
  map_add' h g := by
    funext i j k l
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' e h := by
    funext i j k l
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring

private abbrev returnSymmetryLinearBasis :
    Module.Basis (Fin 10) F₂ LinearForm := Pi.basisFun F₂ (Fin 10)

private abbrev returnSymmetryTwoBasis :
    Module.Basis (QuadraticIndex 10) F₂ TwoForm :=
  Pi.basisFun F₂ (QuadraticIndex 10)

private theorem returnSymmetryTwoBasis_eq_wedge
    (s : QuadraticIndex 10) :
    returnSymmetryTwoBasis s =
      squarefreeWedge
        (returnSymmetryLinearBasis (quadraticFirst s))
        (returnSymmetryLinearBasis (quadraticSecond s)) := by
  calc
    returnSymmetryTwoBasis s =
        returnSymmetryTwoBasis
          (quadraticPair (quadraticFirst s) (quadraticSecond s)
            (quadraticFirst_ne_second s)) :=
      congrArg returnSymmetryTwoBasis (quadraticPair_chosen s)
    _ = squarefreeWedge
        (coordinateLinearTen (quadraticFirst s))
        (coordinateLinearTen (quadraticSecond s)) :=
      quadraticBasisPair_eq_wedge _ _ _
    _ = squarefreeWedge
        (returnSymmetryLinearBasis (quadraticFirst s))
        (returnSymmetryLinearBasis (quadraticSecond s)) := by
      congr 1
      · funext i
        by_cases hi : i = quadraticFirst s
        · simp [returnSymmetryLinearBasis, coordinateLinearTen,
            Pi.basisFun, Pi.single_apply, hi, hi.symm]
        · simp [returnSymmetryLinearBasis, coordinateLinearTen,
            Pi.basisFun, Pi.single_apply, hi,
            fun h => hi h.symm]
      · funext i
        by_cases hi : i = quadraticSecond s
        · simp [returnSymmetryLinearBasis, coordinateLinearTen,
            Pi.basisFun, Pi.single_apply, hi, hi.symm]
        · simp [returnSymmetryLinearBasis, coordinateLinearTen,
            Pi.basisFun, Pi.single_apply, hi,
            fun h => hi h.symm]

set_option maxHeartbeats 3000000 in
private theorem rationalPlaceFourFormLinear_wedge_basis
    (theta : Fin 2) (s t : QuadraticIndex 10) :
    rationalPlaceFourFormLinear theta
        (ambientWedgeTwo (returnSymmetryTwoBasis s)
          (returnSymmetryTwoBasis t)) =
      ambientWedgeTwo
        (rationalPlaceTwoFormLinear theta (returnSymmetryTwoBasis s))
        (rationalPlaceTwoFormLinear theta (returnSymmetryTwoBasis t)) := by
  rw [returnSymmetryTwoBasis_eq_wedge,
    returnSymmetryTwoBasis_eq_wedge,
    rationalPlaceTwoFormLinear_squarefreeWedge',
    rationalPlaceTwoFormLinear_squarefreeWedge']
  funext i j k l
  simp only [rationalPlaceFourFormLinear, ambientWedgeTwo,
    ambientTwoCoeff_squarefreeWedge, rationalPlaceLinear_basis,
    returnSymmetryLinearBasis, Pi.basisFun, Pi.single_apply]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp [Pi.single_apply, eq_comm]
  ring_nf

private theorem ambientWedgeTwo_double_sum
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (a : I → F₂) (b : J → F₂)
    (p : I → TwoForm) (q : J → TwoForm) :
    ambientWedgeTwo (∑ i, a i • p i) (∑ j, b j • q j) =
      ∑ j, ∑ i, (a i * b j) • ambientWedgeTwo (p i) (q j) := by
  change ambientWedgeTwoBilinear (∑ i, a i • p i)
      (∑ j, b j • q j) = _
  simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  exact mul_comm (b j) (a i)

/-- Exterior multiplication of two quadratic forms is natural under either
rational-place generator. -/
theorem rationalPlaceFourFormLinear_ambientWedgeTwo
    (theta : Fin 2) (p q : TwoForm) :
    rationalPlaceFourFormLinear theta (ambientWedgeTwo p q) =
      ambientWedgeTwo (rationalPlaceTwoFormLinear theta p)
        (rationalPlaceTwoFormLinear theta q) := by
  classical
  have hp : ∑ s : QuadraticIndex 10,
      p s • returnSymmetryTwoBasis s = p := by
    simpa [returnSymmetryTwoBasis] using
      returnSymmetryTwoBasis.sum_repr p
  have hq : ∑ t : QuadraticIndex 10,
      q t • returnSymmetryTwoBasis t = q := by
    simpa [returnSymmetryTwoBasis] using
      returnSymmetryTwoBasis.sum_repr q
  rw [← hp, ← hq]
  calc
    rationalPlaceFourFormLinear theta
        (ambientWedgeTwo
          (∑ s : QuadraticIndex 10, p s • returnSymmetryTwoBasis s)
          (∑ t : QuadraticIndex 10, q t • returnSymmetryTwoBasis t)) =
      rationalPlaceFourFormLinear theta
        (∑ t : QuadraticIndex 10, ∑ s : QuadraticIndex 10,
          (p s * q t) • ambientWedgeTwo
            (returnSymmetryTwoBasis s) (returnSymmetryTwoBasis t)) := by
        rw [ambientWedgeTwo_double_sum]
    _ = ∑ t : QuadraticIndex 10, ∑ s : QuadraticIndex 10,
          (p s * q t) • ambientWedgeTwo
            (rationalPlaceTwoFormLinear theta (returnSymmetryTwoBasis s))
            (rationalPlaceTwoFormLinear theta
              (returnSymmetryTwoBasis t)) := by
      rw [(rationalPlaceFourFormLinear theta).map_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [(rationalPlaceFourFormLinear theta).map_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [(rationalPlaceFourFormLinear theta).map_smul,
        rationalPlaceFourFormLinear_wedge_basis]
    _ = ambientWedgeTwo
          (∑ s : QuadraticIndex 10,
            p s • rationalPlaceTwoFormLinear theta
              (returnSymmetryTwoBasis s))
          (∑ t : QuadraticIndex 10,
            q t • rationalPlaceTwoFormLinear theta
              (returnSymmetryTwoBasis t)) := by
      rw [ambientWedgeTwo_double_sum]
    _ = ambientWedgeTwo
          (rationalPlaceTwoFormLinear theta
            (∑ s : QuadraticIndex 10, p s • returnSymmetryTwoBasis s))
          (rationalPlaceTwoFormLinear theta
            (∑ t : QuadraticIndex 10, q t • returnSymmetryTwoBasis t)) := by
      simp only [map_sum, map_smul]

/-- The exterior-kernel property consumed by the rank-one return-feedback
theorem. -/
def FirstOrderReturnKernelCertificate (z : TwoForm) : Prop :=
  ∀ (u c : TargetCoeff),
    u ∈ firstOrderEnvelopeCoeffSpace →
    ambientWedgeTwo
        (targetTwo (firstOrderMissingCoeff + u) + z)
        (targetTwo c) = 0 →
    c = 0

/-- Every canonical rational-return representative has the required
exterior-kernel certificate. -/
theorem rationalReturnOrbit_kernelCertificate
    (orbit : RationalReturnOrbit) :
    FirstOrderReturnKernelCertificate
      (rationalReturnOrbitSection orbit) := by
  intro u c hu hzero
  exact rationalReturnOrbit_wedge_firstOrder_injective
    orbit u c hu hzero

/-- The return-kernel certificate is invariant under translation or
reversal of the rational places. -/
theorem FirstOrderReturnKernelCertificate.rationalPlace
    {z : TwoForm} (hkernel : FirstOrderReturnKernelCertificate z)
    (theta : Fin 2) :
    FirstOrderReturnKernelCertificate
      (rationalPlaceTwoFormLinear theta z) := by
  intro u c hu hzero
  let u' := rationalMissingCorrection theta +
    rationalTargetCoeffChange theta u
  have hu' : u' ∈ firstOrderEnvelopeCoeffSpace := by
    exact firstOrderEnvelopeCoeffSpace.add_mem
      (rationalMissingCorrection_mem theta)
      ((rationalTargetCoeffChange_mem_firstOrderEnvelope_iff theta u).2 hu)
  have hmapped : ambientWedgeTwo
      (rationalPlaceTwoFormLinear theta
        (targetTwo (firstOrderMissingCoeff + u) +
          rationalPlaceTwoFormLinear theta z))
      (rationalPlaceTwoFormLinear theta (targetTwo c)) = 0 := by
    rw [← rationalPlaceFourFormLinear_ambientWedgeTwo, hzero]
    exact (rationalPlaceFourFormLinear theta).map_zero
  rw [map_add, rationalPlaceTwoFormLinear_missingCoset,
    rationalPlaceTwoFormLinear_involutive,
    rationalPlaceTwoFormLinear_targetTwo] at hmapped
  have hcImage : rationalTargetCoeffChange theta c = 0 :=
    hkernel u' (rationalTargetCoeffChange theta c) hu' (by
      simpa only [u'] using hmapped)
  have hcBack := congrArg (rationalTargetCoeffChange theta) hcImage
  have hzeroImage : rationalTargetCoeffChange theta (0 : TargetCoeff) = 0 := by
    funext i
    fin_cases theta <;> fin_cases i <;>
      simp [rationalTargetCoeffChange]
  simpa [rationalTargetCoeffChange_involutive theta c,
    hzeroImage] using hcBack

/-- Unpopulatedness of a returned quadratic quotient is also invariant under
either rational-place generator. -/
theorem UnpopulatedQuadraticSection.rationalPlace
    {z : TwoForm} (hunpopulated : UnpopulatedQuadraticSection z)
    (theta : Fin 2) :
    UnpopulatedQuadraticSection
      (rationalPlaceTwoFormLinear theta z) := by
  intro d hd htarget
  apply hunpopulated (rationalPlaceTwoFormLinear theta d)
    (rationalPlaceTwoFormLinear_decomposable theta hd)
  rcases htarget with ⟨c, hc⟩
  have hc' : targetTwo c =
      d + rationalPlaceTwoFormLinear theta z := hc
  refine ⟨rationalTargetCoeffChange theta c, ?_⟩
  calc
    targetTwo (rationalTargetCoeffChange theta c) =
        rationalPlaceTwoFormLinear theta (targetTwo c) :=
      (rationalPlaceTwoFormLinear_targetTwo theta c).symm
    _ = rationalPlaceTwoFormLinear theta
        (d + rationalPlaceTwoFormLinear theta z) := by rw [hc']
    _ = rationalPlaceTwoFormLinear theta d + z := by
      rw [map_add, rationalPlaceTwoFormLinear_involutive]

/-- The six words needed for the rational-place `S₃` action. -/
inductive RationalPlaceWord where
  | identity
  | translation
  | reversal
  | translationReversal
  | reversalTranslation
  | translationReversalTranslation
  deriving DecidableEq

/-- Apply one of the six rational-place symmetry words to a quadratic form. -/
def RationalPlaceWord.twoForm : RationalPlaceWord → TwoForm → TwoForm
  | .identity, z => z
  | .translation, z => rationalPlaceTwoFormLinear 0 z
  | .reversal, z => rationalPlaceTwoFormLinear 1 z
  | .translationReversal, z =>
      rationalPlaceTwoFormLinear 0 (rationalPlaceTwoFormLinear 1 z)
  | .reversalTranslation, z =>
      rationalPlaceTwoFormLinear 1 (rationalPlaceTwoFormLinear 0 z)
  | .translationReversalTranslation, z =>
      rationalPlaceTwoFormLinear 0
        (rationalPlaceTwoFormLinear 1 (rationalPlaceTwoFormLinear 0 z))

theorem FirstOrderReturnKernelCertificate.rationalPlaceWord
    {z : TwoForm} (hkernel : FirstOrderReturnKernelCertificate z)
    (word : RationalPlaceWord) :
    FirstOrderReturnKernelCertificate (word.twoForm z) := by
  cases word with
  | identity => exact hkernel
  | translation => exact hkernel.rationalPlace 0
  | reversal => exact hkernel.rationalPlace 1
  | translationReversal =>
      exact (hkernel.rationalPlace 1).rationalPlace 0
  | reversalTranslation =>
      exact (hkernel.rationalPlace 0).rationalPlace 1
  | translationReversalTranslation =>
      exact ((hkernel.rationalPlace 0).rationalPlace 1).rationalPlace 0

theorem UnpopulatedQuadraticSection.rationalPlaceWord
    {z : TwoForm} (hunpopulated : UnpopulatedQuadraticSection z)
    (word : RationalPlaceWord) :
    UnpopulatedQuadraticSection (word.twoForm z) := by
  cases word with
  | identity => exact hunpopulated
  | translation => exact hunpopulated.rationalPlace 0
  | reversal => exact hunpopulated.rationalPlace 1
  | translationReversal =>
      exact (hunpopulated.rationalPlace 1).rationalPlace 0
  | reversalTranslation =>
      exact (hunpopulated.rationalPlace 0).rationalPlace 1
  | translationReversalTranslation =>
      exact ((hunpopulated.rationalPlace 0).rationalPlace 1).rationalPlace 0

/-- All rational-place transports of all four canonical return
representatives satisfy the rank-one exterior-kernel condition. -/
theorem rationalReturnOrbitWord_kernelCertificate
    (orbit : RationalReturnOrbit) (word : RationalPlaceWord) :
    FirstOrderReturnKernelCertificate
      (word.twoForm (rationalReturnOrbitSection orbit)) :=
  (rationalReturnOrbit_kernelCertificate orbit).rationalPlaceWord word

/-- Normalized rank-one feedback is sterile for every rational-place
transport of every canonical return representative. -/
theorem rankOne_rationalReturnOrbitWord_escape_impossible
    (orbit : RationalReturnOrbit) (word : RationalPlaceWord)
    (hunpopulated : UnpopulatedQuadraticSection
      (word.twoForm (rationalReturnOrbitSection orbit)))
    (U c v : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (hcquad : c ∈ N4.quadraticANFSpace 10)
    (hvquad : v ∈ N4.quadraticANFSpace 10)
    (fConst : F₂) (fLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hcSection : quadraticProjection 10 c ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂
          ({word.twoForm (rationalReturnOrbitSection orbit)} : Set TwoForm))
    (hvSection : quadraticProjection 10 v ∈
      firstOrderEnvelopeTwoSpace ⊔
        Submodule.span F₂
          ({word.twoForm (rationalReturnOrbitSection orbit)} : Set TwoForm))
    (hproduct :
      U * c = quadraticCoordinateANF fConst fLinear
        (targetTwo (firstOrderMissingCoeff + u)) + v)
    (habsorb : (U * c) * c = U * c) : False :=
  rankOne_unpopulatedSection_escape_impossible_of_kernel
    (word.twoForm (rationalReturnOrbitSection orbit)) hunpopulated
      (rationalReturnOrbitWord_kernelCertificate orbit word)
      U c v hUhigh hcquad hvquad fConst fLinear u hu hcSection hvSection
      hproduct habsorb

end
end N5
end UnrestrictedBooleanMul
