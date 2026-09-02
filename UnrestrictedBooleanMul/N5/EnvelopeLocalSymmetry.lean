import UnrestrictedBooleanMul.N5.EnvelopeLocalDependent
import UnrestrictedBooleanMul.N5.RationalPlaceSymmetry

/-!
# Rational-place transport for local/dependent envelope shadows

This module transports the algebraic rational-zero calculation to the other
two rational places.  The transport is through the explicit translation and
reversal linear maps; no circuit states or assignments are enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem rationalTargetCoeffChange_mem_firstOrderEnvelope_iff
    (theta : Fin 2) (c : TargetCoeff) :
    rationalTargetCoeffChange theta c ∈ firstOrderEnvelopeCoeffSpace ↔
      c ∈ firstOrderEnvelopeCoeffSpace := by
  rw [mem_firstOrderEnvelopeCoeffSpace, mem_firstOrderEnvelopeCoeffSpace]
  have hfunctional :
      firstOrderMissingFunctional (rationalTargetCoeffChange theta c) =
        firstOrderMissingFunctional c := by
    fin_cases theta <;>
      simp [firstOrderMissingFunctional, rationalTargetCoeffChange] <;>
      ring_nf <;>
      simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.three_eq_one_f2, N3Certificate.four_eq_zero_f2]
  rw [hfunctional]

theorem rationalPlaceTwoFormLinear_mem_firstOrderEnvelope
    (theta : Fin 2) (q : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace) :
    rationalPlaceTwoFormLinear theta q ∈ firstOrderEnvelopeTwoSpace := by
  rcases hq with ⟨c, hc, rfl⟩
  change rationalPlaceTwoFormLinear theta (targetTwo c) ∈
    firstOrderEnvelopeTwoSpace
  rw [rationalPlaceTwoFormLinear_targetTwo]
  exact ⟨rationalTargetCoeffChange theta c,
    (rationalTargetCoeffChange_mem_firstOrderEnvelope_iff theta c).2 hc, rfl⟩

theorem rationalPlaceTwoFormLinear_target_involutive
    (theta : Fin 2) (c : TargetCoeff) :
    rationalPlaceTwoFormLinear theta
        (rationalPlaceTwoFormLinear theta (targetTwo c)) = targetTwo c := by
  rw [rationalPlaceTwoFormLinear_targetTwo,
    rationalPlaceTwoFormLinear_targetTwo,
    rationalTargetCoeffChange_involutive]

theorem translation_rationalOneValueTwo :
    rationalPlaceTwoFormLinear 0 rationalOneValueTwo =
      rationalZeroValueTwo := by
  rw [rationalOneValueTwo_eq_target, rationalZeroValueTwo_eq_target,
    rationalPlaceTwoFormLinear_targetTwo]
  congr 1

theorem translation_rationalOneJetTwo :
    rationalPlaceTwoFormLinear 0 rationalOneJetTwo =
      rationalZeroJetTwo := by
  rw [rationalOneJetTwo_eq_target, rationalZeroJetTwo_eq_target,
    rationalPlaceTwoFormLinear_targetTwo]
  congr 1

theorem reversal_rationalInfinityValueTwo :
    rationalPlaceTwoFormLinear 1 rationalInfinityValueTwo =
      rationalZeroValueTwo := by
  rw [rationalInfinityValueTwo_eq_target, rationalZeroValueTwo_eq_target,
    rationalPlaceTwoFormLinear_targetTwo]
  congr 1

theorem reversal_rationalInfinityJetTwo :
    rationalPlaceTwoFormLinear 1 rationalInfinityJetTwo =
      rationalZeroJetTwo := by
  rw [rationalInfinityJetTwo_eq_target, rationalZeroJetTwo_eq_target,
    rationalPlaceTwoFormLinear_targetTwo]
  congr 1

/-! ## Naturality of the cubic exterior product -/

private abbrev ambientLinearBasis :
    Module.Basis (Fin 10) F₂ LinearForm := Pi.basisFun F₂ (Fin 10)

private abbrev ambientTwoBasis :
    Module.Basis (QuadraticIndex 10) F₂ TwoForm :=
  Pi.basisFun F₂ (QuadraticIndex 10)

/-- Tensor-coordinate action induced by the same input substitution on
ambient cubic forms.  We only use it on alternating cubic forms. -/
def rationalPlaceThreeFormLinear (theta : Fin 2) :
    AmbientThreeForm →ₗ[F₂] AmbientThreeForm where
  toFun h := fun i j k =>
    ∑ a : Fin 10, ∑ b : Fin 10, ∑ c : Fin 10,
      rationalPlaceInputChange theta a i *
        rationalPlaceInputChange theta b j *
        rationalPlaceInputChange theta c k * h a b c
  map_add' h g := by
    funext i j k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' d h := by
    funext i j k
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
    ring

private theorem ambientVectorWedgeTwo_add_right
    (u : LinearForm) (p q : TwoForm) :
    ambientVectorWedgeTwo u (p + q) =
      ambientVectorWedgeTwo u p + ambientVectorWedgeTwo u q := by
  funext i j k
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff_add, Pi.add_apply]
  ring

private theorem ambientVectorWedgeTwo_smul_right
    (u : LinearForm) (d : F₂) (p : TwoForm) :
    ambientVectorWedgeTwo u (d • p) =
      d • ambientVectorWedgeTwo u p := by
  funext i j k
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff_smul, Pi.smul_apply, smul_eq_mul]
  ring

private def ambientVectorWedgeRightMap (u : LinearForm) :
    TwoForm →ₗ[F₂] AmbientThreeForm where
  toFun p := ambientVectorWedgeTwo u p
  map_add' := ambientVectorWedgeTwo_add_right u
  map_smul' := ambientVectorWedgeTwo_smul_right u

private theorem ambientVectorWedgeTwo_double_sum
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (a : I → F₂) (b : J → F₂)
    (f : I → LinearForm) (g : J → TwoForm) :
    ambientVectorWedgeTwo (∑ i, a i • f i) (∑ j, b j • g j) =
      ∑ j, ∑ i, (a i * b j) • ambientVectorWedgeTwo (f i) (g j) := by
  change ambientVectorWedgeRightMap (∑ i, a i • f i)
      (∑ j, b j • g j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  have hleft : ambientVectorWedgeTwo (∑ i, a i • f i) (g j) =
      ∑ i, a i • ambientVectorWedgeTwo (f i) (g j) := by
    change ambientVectorWedgeMap (g j) (∑ i, a i • f i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  change b j • ambientVectorWedgeTwo (∑ i, a i • f i) (g j) = _
  rw [hleft, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  exact mul_comm (b j) (a i)

private theorem ambient_finset_pair_eq_pair_iff {m : Nat}
    {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) :
    ({i, j} : Finset (Fin m)) = {k, l} ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    have hi : i = k ∨ i = l := by
      have : i ∈ ({k, l} : Finset (Fin m)) := by rw [← h]; simp
      simpa using this
    rcases hi with hik | hil
    · left
      refine ⟨hik, ?_⟩
      have hj : j = k ∨ j = l := by
        have : j ∈ ({k, l} : Finset (Fin m)) := by rw [← h]; simp
        simpa using this
      exact hj.resolve_left (fun hjk => hij (hik.trans hjk.symm))
    · right
      refine ⟨hil, ?_⟩
      have hj : j = k ∨ j = l := by
        have : j ∈ ({k, l} : Finset (Fin m)) := by rw [← h]; simp
        simpa using this
      exact hj.resolve_right (fun hjl => hij (hil.trans hjl.symm))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

private theorem squarefreeWedge_ambientLinearBasis
    (i j : Fin 10) (hij : i ≠ j) :
    squarefreeWedge (ambientLinearBasis i) (ambientLinearBasis j) =
      ambientTwoBasis (quadraticPair i j hij) := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨k, l, hkl, rfl⟩
  simp only [squarefreeWedge_pair]
  by_cases hpair : quadraticPair k l hkl = quadraticPair i j hij
  · have hset := congrArg Subtype.val hpair
    have hcases : (k = i ∧ l = j) ∨ (k = j ∧ l = i) :=
      (ambient_finset_pair_eq_pair_iff hkl hij).mp hset
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [ambientLinearBasis, ambientTwoBasis, Pi.basisFun,
        hij, hkl, hpair]
  · have hset : ({k, l} : Finset (Fin 10)) ≠ {i, j} := by
      intro h
      apply hpair
      apply Subtype.ext
      simpa [quadraticPair] using h
    by_cases hki : k = i
    · subst k
      have hlj : l ≠ j := by
        intro hlj
        subst l
        exact hset rfl
      simp [ambientLinearBasis, ambientTwoBasis, Pi.basisFun,
        hpair, hkl, hij, hlj]
    · by_cases hkj : k = j
      · subst k
        have hli : l ≠ i := by
          intro hli
          subst l
          exact hset (Finset.pair_comm _ _)
        simp [ambientLinearBasis, ambientTwoBasis, Pi.basisFun,
          hpair, hkl, hij, hli]
      · simp [ambientLinearBasis, ambientTwoBasis, Pi.basisFun,
          hpair, hki, hkj]

private theorem ambientTwoBasis_eq_wedge (s : QuadraticIndex 10) :
    ambientTwoBasis s =
      squarefreeWedge (ambientLinearBasis (quadraticFirst s))
        (ambientLinearBasis (quadraticSecond s)) := by
  rw [squarefreeWedge_ambientLinearBasis _ _
    (quadraticFirst_ne_second s)]
  exact congrArg ambientTwoBasis (quadraticPair_chosen s)

private theorem rationalPlaceThreeFormLinear_wedge_basis
    (theta : Fin 2) (r : Fin 10) (s : QuadraticIndex 10) :
    rationalPlaceThreeFormLinear theta
        (ambientVectorWedgeTwo (ambientLinearBasis r) (ambientTwoBasis s)) =
      ambientVectorWedgeTwo
        (rationalPlaceLinear theta (ambientLinearBasis r))
        (rationalPlaceTwoFormLinear theta (ambientTwoBasis s)) := by
  rw [ambientTwoBasis_eq_wedge,
    rationalPlaceTwoFormLinear_squarefreeWedge',
    rationalPlaceLinear_basis, rationalPlaceLinear_basis,
    rationalPlaceLinear_basis]
  funext i j k
  simp only [rationalPlaceThreeFormLinear, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, ambientTwoCoeff_squarefreeWedge,
    ambientLinearBasis, Pi.basisFun, Pi.single_apply]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp [Pi.single_apply, eq_comm]
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff_squarefreeWedge]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp [Pi.single_apply, eq_comm]
  ring_nf

/-- Exterior-cubic naturality of the rational-place substitution. -/
theorem rationalPlaceThreeFormLinear_ambientVectorWedgeTwo
    (theta : Fin 2) (u : LinearForm) (p : TwoForm) :
    rationalPlaceThreeFormLinear theta (ambientVectorWedgeTwo u p) =
      ambientVectorWedgeTwo (rationalPlaceLinear theta u)
        (rationalPlaceTwoFormLinear theta p) := by
  classical
  have hu : ∑ i : Fin 10, u i • ambientLinearBasis i = u := by
    simpa [ambientLinearBasis] using ambientLinearBasis.sum_repr u
  have hp : ∑ s : QuadraticIndex 10, p s • ambientTwoBasis s = p := by
    simpa [ambientTwoBasis] using ambientTwoBasis.sum_repr p
  rw [← hu, ← hp]
  calc
    rationalPlaceThreeFormLinear theta
        (ambientVectorWedgeTwo
          (∑ i : Fin 10, u i • ambientLinearBasis i)
          (∑ s : QuadraticIndex 10, p s • ambientTwoBasis s)) =
      rationalPlaceThreeFormLinear theta
        (∑ s : QuadraticIndex 10, ∑ i : Fin 10,
          (u i * p s) • ambientVectorWedgeTwo
            (ambientLinearBasis i) (ambientTwoBasis s)) := by
        rw [ambientVectorWedgeTwo_double_sum]
    _ = ∑ s : QuadraticIndex 10, ∑ i : Fin 10,
          (u i * p s) • ambientVectorWedgeTwo
            (rationalPlaceLinear theta (ambientLinearBasis i))
            (rationalPlaceTwoFormLinear theta (ambientTwoBasis s)) := by
      simp_rw [map_sum, map_smul,
        rationalPlaceThreeFormLinear_wedge_basis]
    _ = ambientVectorWedgeTwo
          (∑ i : Fin 10, u i •
            rationalPlaceLinear theta (ambientLinearBasis i))
          (∑ s : QuadraticIndex 10, p s •
            rationalPlaceTwoFormLinear theta (ambientTwoBasis s)) := by
      rw [ambientVectorWedgeTwo_double_sum]
    _ = ambientVectorWedgeTwo
          (rationalPlaceLinear theta
            (∑ i : Fin 10, u i • ambientLinearBasis i))
          (rationalPlaceTwoFormLinear theta
            (∑ s : QuadraticIndex 10, p s • ambientTwoBasis s)) := by
      simp only [map_sum, map_smul]

theorem rationalPlaceThreeFormLinear_factorPlaneCubic
    (theta : Fin 2) (ell m : LinearForm) (q c : TwoForm) :
    rationalPlaceThreeFormLinear theta (factorPlaneCubic ell m q c) =
      factorPlaneCubic (rationalPlaceLinear theta ell)
        (rationalPlaceLinear theta m)
        (rationalPlaceTwoFormLinear theta q)
        (rationalPlaceTwoFormLinear theta c) := by
  simp only [factorPlaneCubic, map_add,
    rationalPlaceThreeFormLinear_ambientVectorWedgeTwo]

theorem translation_rationalZeroValueTwo :
    rationalPlaceTwoFormLinear 0 rationalZeroValueTwo =
      rationalOneValueTwo := by
  have h := congrArg (rationalPlaceTwoFormLinear 0)
    translation_rationalOneValueTwo
  have hinvol : rationalPlaceTwoFormLinear 0
      (rationalPlaceTwoFormLinear 0 rationalOneValueTwo) =
        rationalOneValueTwo := by
    simpa [rationalOneValueTwo_eq_target] using
      rationalPlaceTwoFormLinear_target_involutive 0 rOneCoeff
  exact h.symm.trans hinvol

theorem translation_rationalZeroJetTwo :
    rationalPlaceTwoFormLinear 0 rationalZeroJetTwo =
      rationalOneJetTwo := by
  have h := congrArg (rationalPlaceTwoFormLinear 0)
    translation_rationalOneJetTwo
  have hinvol : rationalPlaceTwoFormLinear 0
      (rationalPlaceTwoFormLinear 0 rationalOneJetTwo) =
        rationalOneJetTwo := by
    simpa [rationalOneJetTwo_eq_target] using
      rationalPlaceTwoFormLinear_target_involutive 0 exactJOneCoeff
  exact h.symm.trans hinvol

theorem reversal_rationalZeroValueTwo :
    rationalPlaceTwoFormLinear 1 rationalZeroValueTwo =
      rationalInfinityValueTwo := by
  have h := congrArg (rationalPlaceTwoFormLinear 1)
    reversal_rationalInfinityValueTwo
  have hinvol : rationalPlaceTwoFormLinear 1
      (rationalPlaceTwoFormLinear 1 rationalInfinityValueTwo) =
        rationalInfinityValueTwo := by
    simpa [rationalInfinityValueTwo_eq_target] using
      rationalPlaceTwoFormLinear_target_involutive 1 rInfinityCoeff
  exact h.symm.trans hinvol

theorem reversal_rationalZeroJetTwo :
    rationalPlaceTwoFormLinear 1 rationalZeroJetTwo =
      rationalInfinityJetTwo := by
  have h := congrArg (rationalPlaceTwoFormLinear 1)
    reversal_rationalInfinityJetTwo
  have hinvol : rationalPlaceTwoFormLinear 1
      (rationalPlaceTwoFormLinear 1 rationalInfinityJetTwo) =
        rationalInfinityJetTwo := by
    simpa [rationalInfinityJetTwo_eq_target] using
      rationalPlaceTwoFormLinear_target_involutive 1 exactJInfinityCoeff
  exact h.symm.trans hinvol

private theorem rationalLocal_dependent_structure_of_transport
    (theta : Fin 2) (value jet : TwoForm)
    (hvalueToZero : rationalPlaceTwoFormLinear theta value =
      rationalZeroValueTwo)
    (hjetToZero : rationalPlaceTwoFormLinear theta jet =
      rationalZeroJetTwo)
    (hvalueFromZero : rationalPlaceTwoFormLinear theta
      rationalZeroValueTwo = value)
    (hjetFromZero : rationalPlaceTwoFormLinear theta
      rationalZeroJetTwo = jet)
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : factorPlaneCubic ell m value jet =
      factorPlaneCubic x y 0 (targetTwo c)) :
    ∃ alpha beta : F₂, ∃ remote : TwoForm,
      remote ∈ firstOrderEnvelopeTwoSpace ∧
      targetTwo c = alpha • value + beta • jet + remote ∧
      ambientVectorWedgeTwo x remote = 0 := by
  let c' : TargetCoeff := rationalTargetCoeffChange theta c
  have hc' : c' ∈ firstOrderEnvelopeCoeffSpace :=
    (rationalTargetCoeffChange_mem_firstOrderEnvelope_iff theta c).2 hc
  have hcubic' :
      factorPlaneCubic (rationalPlaceLinear theta ell)
          (rationalPlaceLinear theta m) rationalZeroValueTwo
          rationalZeroJetTwo =
        factorPlaneCubic (rationalPlaceLinear theta x)
          (rationalPlaceLinear theta y) 0 (targetTwo c') := by
    have hmap := congrArg (rationalPlaceThreeFormLinear theta) hcubic
    simpa only [rationalPlaceThreeFormLinear_factorPlaneCubic,
      hvalueToZero, hjetToZero, map_zero,
      rationalPlaceTwoFormLinear_targetTwo, c'] using hmap
  rcases rationalZero_local_dependent_structure
      (rationalPlaceLinear theta ell) (rationalPlaceLinear theta m)
      (rationalPlaceLinear theta x) (rationalPlaceLinear theta y)
      c' hc' hcubic' with ⟨alpha, beta, remote', hremote', hd', hxremote'⟩
  let remote : TwoForm := rationalPlaceTwoFormLinear theta remote'
  have hremote : remote ∈ firstOrderEnvelopeTwoSpace :=
    rationalPlaceTwoFormLinear_mem_firstOrderEnvelope theta remote' hremote'
  have hdmap := congrArg (rationalPlaceTwoFormLinear theta) hd'
  have hcback : rationalPlaceTwoFormLinear theta (targetTwo c') =
      targetTwo c := by
    dsimp only [c']
    rw [rationalPlaceTwoFormLinear_targetTwo,
      rationalTargetCoeffChange_involutive]
  have hd : targetTwo c = alpha • value + beta • jet + remote := by
    simpa only [map_add, map_smul, hcback, hvalueFromZero,
      hjetFromZero, remote] using hdmap
  have hxmap := congrArg (rationalPlaceThreeFormLinear theta) hxremote'
  have hxremote : ambientVectorWedgeTwo x remote = 0 := by
    simpa only [rationalPlaceThreeFormLinear_ambientVectorWedgeTwo,
      rationalPlaceLinear_involutive, map_zero, remote] using hxmap
  exact ⟨alpha, beta, remote, hremote, hd, hxremote⟩

theorem rationalOne_local_dependent_structure
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : factorPlaneCubic ell m rationalOneValueTwo
      rationalOneJetTwo = factorPlaneCubic x y 0 (targetTwo c)) :
    ∃ alpha beta : F₂, ∃ remote : TwoForm,
      remote ∈ firstOrderEnvelopeTwoSpace ∧
      targetTwo c = alpha • rationalOneValueTwo +
        beta • rationalOneJetTwo + remote ∧
      ambientVectorWedgeTwo x remote = 0 :=
  rationalLocal_dependent_structure_of_transport 0
    rationalOneValueTwo rationalOneJetTwo
    translation_rationalOneValueTwo translation_rationalOneJetTwo
    translation_rationalZeroValueTwo translation_rationalZeroJetTwo
    ell m x y c hc hcubic

theorem rationalInfinity_local_dependent_structure
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : factorPlaneCubic ell m rationalInfinityValueTwo
      rationalInfinityJetTwo = factorPlaneCubic x y 0 (targetTwo c)) :
    ∃ alpha beta : F₂, ∃ remote : TwoForm,
      remote ∈ firstOrderEnvelopeTwoSpace ∧
      targetTwo c = alpha • rationalInfinityValueTwo +
        beta • rationalInfinityJetTwo + remote ∧
      ambientVectorWedgeTwo x remote = 0 :=
  rationalLocal_dependent_structure_of_transport 1
    rationalInfinityValueTwo rationalInfinityJetTwo
    reversal_rationalInfinityValueTwo reversal_rationalInfinityJetTwo
    reversal_rationalZeroValueTwo reversal_rationalZeroJetTwo
    ell m x y c hc hcubic

/-! ## Uniform Boolean-shadow assembly -/

theorem rationalLocal_dependent_shadow_decomposition
    (value jet : TwoForm)
    (hvalue : value ∈ firstOrderEnvelopeTwoSpace)
    (hjet : jet ∈ firstOrderEnvelopeTwoSpace)
    (hhadamard : ambientTwoHadamard value jet ∈
      firstOrderEnvelopeTwoSpace)
    (hcorrection : ∀ X Y : LinearForm,
      factorPlaneCubic X Y value jet = 0 →
        ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
          squarefreeWedge X Y + ambientBooleanContraction X jet +
              ambientBooleanContraction Y value =
            r + squarefreeWedge X z)
    (a b a' b' alpha beta : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = alpha • value + beta • jet + remote)
    (hcubic : factorPlaneCubic ell m value jet =
      factorPlaneCubic x y 0 d)
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
    have hcubicZero : factorPlaneCubic ell m value jet = 0 := by
      rw [factorPlaneCubic_zero_left] at hcubic
      have hzero : ambientVectorWedgeTwo 0 d = 0 := by
        funext i j k
        simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]
      exact hcubic.trans hzero
    rcases hcorrection ell m hcubicZero with ⟨r₀, hr₀, z, hcorr⟩
    let r : TwoForm :=
      a • jet + b • value + a' • d + r₀ +
        ambientTwoHadamard value jet
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
        Pi.zero_apply, mul_zero, add_zero, zero_mul, zero_add] at hcorr' ⊢
      dsimp only [r]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair, ambientBooleanContraction_pair,
        ambientTwoHadamard] at hcorr' ⊢
      linear_combination hcorr'
  · let X : LinearForm := ell + beta • x
    let Y : LinearForm := m + alpha • x
    have hcubicZero : factorPlaneCubic X Y value jet = 0 := by
      funext i j k
      have hc := congrFun (congrFun (congrFun hcubic i) j) k
      have hr := congrFun (congrFun (congrFun hxremote i) j) k
      simp only [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, ambientTwoCoeff_add, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, ambientTwoCoeff_zero] at hc hr ⊢
      simp only [X, Y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hd] at hc
      simp only [ambientTwoCoeff_add, ambientTwoCoeff_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
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
      alpha • ell + beta • m + y + ambientDiagonalProduct x w
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
      have hcontract := congrFun hremoteContraction (quadraticPair i j hij)
      simp only [Pi.add_apply, lowProductQuadraticShadow_pair,
        Pi.zero_apply, mul_zero, add_zero, zero_mul, zero_add] at hcorr' ⊢
      simp only [ambientBooleanContraction_pair, Pi.add_apply] at hcontract
      dsimp only [r]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair, ambientBooleanContraction_pair,
        ambientTwoHadamard] at hcorr' ⊢
      simp only [X, Y, t, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair] at hcorr' ⊢
      rw [hd]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination
        (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
        hcorr' + hcontract

theorem ambientTwoHadamard_rationalOneValue_jet :
    ambientTwoHadamard rationalOneValueTwo rationalOneJetTwo =
      rationalOneJetTwo := by
  rw [rationalOneValueTwo_eq_target, rationalOneJetTwo_eq_target]
  unfold ambientTwoHadamard
  apply twoForm_ext_blocks
  · intro i j hij
    simp only [targetTwo_sameA, zero_mul]
  · intro i j hij
    simp only [targetTwo_sameB, zero_mul]
  · intro i j
    rw [targetTwo_cross]
    fin_cases i <;> fin_cases j <;>
      simp [rOneCoeff, exactJOneCoeff, hankelIndex,
        N3Certificate.pow_two_f2]

theorem ambientTwoHadamard_rationalInfinityValue_jet :
    ambientTwoHadamard rationalInfinityValueTwo
      rationalInfinityJetTwo = 0 := by
  rw [rationalInfinityValueTwo_eq_target,
    rationalInfinityJetTwo_eq_target]
  unfold ambientTwoHadamard
  apply twoForm_ext_blocks
  · intro i j hij
    simp only [targetTwo_sameA, zero_mul, Pi.zero_apply]
  · intro i j hij
    simp only [targetTwo_sameB, zero_mul, Pi.zero_apply]
  · intro i j
    rw [targetTwo_cross]
    fin_cases i <;> fin_cases j <;>
      simp [ambientTwoHadamard, rInfinityCoeff, exactJInfinityCoeff,
        hankelIndex]

/-! ## The local/dependent shadow at every rational place -/

/-- The generic algebraic shadow calculation instantiated at the rational
place one. -/
theorem rationalOne_local_dependent_shadow_decomposition
    (a b a' b' alpha beta : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = alpha • rationalOneValueTwo +
      beta • rationalOneJetTwo + remote)
    (hcubic : factorPlaneCubic ell m rationalOneValueTwo
      rationalOneJetTwo = factorPlaneCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m rationalOneValueTwo
          rationalOneJetTwo +
        lowProductQuadraticShadow a' b' x y 0 d =
      r + squarefreeWedge u v + squarefreeWedge s t := by
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
  exact rationalLocal_dependent_shadow_decomposition
    rationalOneValueTwo rationalOneJetTwo hvalue hjet hhadamard
    rationalOne_booleanCorrection_decomposition
    a b a' b' alpha beta ell m x y d remote hremote hd hcubic hxremote

/-- The generic algebraic shadow calculation instantiated at the rational
place infinity. -/
theorem rationalInfinity_local_dependent_shadow_decomposition
    (a b a' b' alpha beta : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = alpha • rationalInfinityValueTwo +
      beta • rationalInfinityJetTwo + remote)
    (hcubic : factorPlaneCubic ell m rationalInfinityValueTwo
      rationalInfinityJetTwo = factorPlaneCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m rationalInfinityValueTwo
          rationalInfinityJetTwo +
        lowProductQuadraticShadow a' b' x y 0 d =
      r + squarefreeWedge u v + squarefreeWedge s t := by
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
  exact rationalLocal_dependent_shadow_decomposition
    rationalInfinityValueTwo rationalInfinityJetTwo hvalue hjet hhadamard
    rationalInfinity_booleanCorrection_decomposition
    a b a' b' alpha beta ell m x y d remote hremote hd hcubic hxremote

/-- Missing-coset exclusion for the local/dependent branch at the rational
place one. -/
theorem rationalOne_local_dependent_shadow_not_missingCoset
    (a b a' b' alpha beta : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = alpha • rationalOneValueTwo +
      beta • rationalOneJetTwo + remote)
    (hcubic : factorPlaneCubic ell m rationalOneValueTwo
      rationalOneJetTwo = factorPlaneCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalOneValueTwo
          rationalOneJetTwo +
        lowProductQuadraticShadow a' b' x y 0 d ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  rcases rationalOne_local_dependent_shadow_decomposition
      a b a' b' alpha beta ell m x y d remote hremote hd hcubic hxremote with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  exact hdecomp.symm.trans hmissing

/-- Missing-coset exclusion for the local/dependent branch at the rational
place infinity. -/
theorem rationalInfinity_local_dependent_shadow_not_missingCoset
    (a b a' b' alpha beta : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = alpha • rationalInfinityValueTwo +
      beta • rationalInfinityJetTwo + remote)
    (hcubic : factorPlaneCubic ell m rationalInfinityValueTwo
      rationalInfinityJetTwo = factorPlaneCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalInfinityValueTwo
          rationalInfinityJetTwo +
        lowProductQuadraticShadow a' b' x y 0 d ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  rcases rationalInfinity_local_dependent_shadow_decomposition
      a b a' b' alpha beta ell m x y d remote hremote hd hcubic hxremote with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  exact hdecomp.symm.trans hmissing

/-- The rational-one local/dependent branch with its structural hypotheses
discharged by the transported Hankel calculation. -/
theorem rationalOne_actual_local_dependent_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : factorPlaneCubic ell m rationalOneValueTwo
      rationalOneJetTwo = factorPlaneCubic x y 0 (targetTwo c))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalOneValueTwo
          rationalOneJetTwo +
        lowProductQuadraticShadow a' b' x y 0 (targetTwo c) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases rationalOne_local_dependent_structure ell m x y c hc hcubic with
    ⟨alpha, beta, remote, hremote, hd, hxremote⟩
  exact rationalOne_local_dependent_shadow_not_missingCoset
    a b a' b' alpha beta ell m x y (targetTwo c) remote
      hremote hd hcubic hxremote u hu

/-- The rational-infinity local/dependent branch with its structural
hypotheses discharged by the transported Hankel calculation. -/
theorem rationalInfinity_actual_local_dependent_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : factorPlaneCubic ell m rationalInfinityValueTwo
      rationalInfinityJetTwo = factorPlaneCubic x y 0 (targetTwo c))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalInfinityValueTwo
          rationalInfinityJetTwo +
        lowProductQuadraticShadow a' b' x y 0 (targetTwo c) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases rationalInfinity_local_dependent_structure ell m x y c hc hcubic with
    ⟨alpha, beta, remote, hremote, hd, hxremote⟩
  exact rationalInfinity_local_dependent_shadow_not_missingCoset
    a b a' b' alpha beta ell m x y (targetTwo c) remote
      hremote hd hcubic hxremote u hu

/-- Uniform local/dependent missing-coset exclusion for all three rational
value--jet planes. -/
theorem rationalJet_actual_local_dependent_shadow_not_missingCoset
    (place : Fin 3) (a b a' b' : F₂)
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : factorPlaneCubic ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right =
      factorPlaneCubic x y 0 (targetTwo c))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right +
        lowProductQuadraticShadow a' b' x y 0 (targetTwo c) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  fin_cases place
  · simpa [ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      rationalZero_actual_local_dependent_shadow_not_missingCoset
        a b a' b' ell m x y c hc hcubic u hu
  · simpa [ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      rationalOne_actual_local_dependent_shadow_not_missingCoset
        a b a' b' ell m x y c hc hcubic u hu
  · simpa [ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      rationalInfinity_actual_local_dependent_shadow_not_missingCoset
        a b a' b' ell m x y c hc hcubic u hu

end

end N5
end UnrestrictedBooleanMul
