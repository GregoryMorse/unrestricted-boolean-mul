import UnrestrictedBooleanMul.N5.RankOneShadow

/-!
# Independent-plane low-product shadows

This module treats the independent half of manuscript Lemma 11.2.  The first
representative is the rational value--jet plane at zero.  Its cubic syzygy is
solved by sparse coefficient pivots, after which the missing target functional
is an algebraic consequence of seven Hankel equations.  No assignments or
quadratic-form tables are enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The value direction in the rational zero two-jet. -/
def rationalZeroValueTwo : TwoForm := targetPairTwo 0 0

/-- The first-Hasse-jet direction in the rational zero two-jet. -/
def rationalZeroJetTwo : TwoForm :=
  targetPairTwo 0 1 + targetPairTwo 1 0

/-- Value direction in the rational one two-jet. -/
def rationalOneValueTwo : TwoForm :=
  squarefreeWedge aOneEval bOneEval

/-- Exact first-Hasse-jet direction at the rational place one. -/
def rationalOneJetTwo : TwoForm :=
  squarefreeWedge aOneEval bOneJet +
    squarefreeWedge aOneJet bOneEval

/-- Value direction in the rational infinity two-jet. -/
def rationalInfinityValueTwo : TwoForm := targetPairTwo 4 4

/-- Exact first-Hasse-jet direction at the rational place infinity. -/
def rationalInfinityJetTwo : TwoForm :=
  targetPairTwo 4 3 + targetPairTwo 3 4

theorem rationalZeroValueTwo_eq_target :
    rationalZeroValueTwo = targetTwo rZeroCoeff := by
  rw [rationalZeroValueTwo, targetTwo_rZero]

theorem rationalZeroJetTwo_eq_target :
    rationalZeroJetTwo = targetTwo jZeroCoeff := by
  rw [rationalZeroJetTwo, targetTwo_eq_double_sum]
  simp [jZeroCoeff, hankelIndex, Fin.sum_univ_succ]

theorem rationalOneValueTwo_eq_target :
    rationalOneValueTwo = targetTwo rOneCoeff := by
  exact targetTwo_rOne.symm

theorem rationalOneJetTwo_eq_target :
    rationalOneJetTwo = targetTwo exactJOneCoeff := by
  apply twoForm_ext_blocks
  · intro i j hij
    rw [targetTwo_sameA]
    simp [rationalOneJetTwo, squarefreeWedge_pair,
      aOneEval, aOneJet, bOneEval, bOneJet,
      aLinear, bLinear, Pi.basisFun, Fin.sum_univ_succ,
      aCoord_ne_bCoord]
  · intro i j hij
    rw [targetTwo_sameB]
    simp [rationalOneJetTwo, squarefreeWedge_pair,
      aOneEval, aOneJet, bOneEval, bOneJet,
      aLinear, bLinear, Pi.basisFun, Fin.sum_univ_succ,
      bCoord_ne_aCoord]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rationalOneJetTwo, squarefreeWedge_pair,
        exactJOneCoeff, hankelIndex, aOneEval, aOneJet,
        bOneEval, bOneJet, aLinear, bLinear, Pi.basisFun,
        Fin.sum_univ_succ]

theorem rationalInfinityValueTwo_eq_target :
    rationalInfinityValueTwo = targetTwo rInfinityCoeff := by
  exact targetTwo_rInfinity.symm

theorem rationalInfinityJetTwo_eq_target :
    rationalInfinityJetTwo = targetTwo exactJInfinityCoeff := by
  rw [rationalInfinityJetTwo, targetTwo_eq_double_sum]
  simp [exactJInfinityCoeff, hankelIndex, Fin.sum_univ_succ]
  module

theorem targetTwo_exactFirstOrderDirection_mem (i : Fin 8) :
    targetTwo (exactFirstOrderDirections i) ∈
      firstOrderEnvelopeTwoSpace :=
  ⟨exactFirstOrderDirections i, exactFirstOrderDirection_mem i, rfl⟩

/-- Left rational-value direction in one of the three rational-pair
exceptional planes. -/
def rationalPairLeftValueTwo (pair : Fin 3) : TwoForm :=
  targetTwo (rationalValueCoeff (rationalPairLeft pair))

/-- Right rational-value direction in one of the three rational-pair
exceptional planes. -/
def rationalPairRightValueTwo (pair : Fin 3) : TwoForm :=
  targetTwo (rationalValueCoeff (rationalPairRight pair))

/-- First basis direction of the degree-two exceptional target plane. -/
def dStarZeroTwo : TwoForm := targetTwo dStarZeroCoeff

/-- Second basis direction of the degree-two exceptional target plane. -/
def dStarOneTwo : TwoForm := targetTwo dStarOneCoeff

theorem rationalPairLeftValueTwo_eq_wedge (pair : Fin 3) :
    rationalPairLeftValueTwo pair =
      squarefreeWedge (rationalValueA (rationalPairLeft pair))
        (rationalValueB (rationalPairLeft pair)) := by
  rw [rationalPairLeftValueTwo, targetTwo_rationalValueCoeff]

theorem rationalPairRightValueTwo_eq_wedge (pair : Fin 3) :
    rationalPairRightValueTwo pair =
      squarefreeWedge (rationalValueA (rationalPairRight pair))
        (rationalValueB (rationalPairRight pair)) := by
  rw [rationalPairRightValueTwo, targetTwo_rationalValueCoeff]

/-- The `a`- and `b`-side factors of every rational value have disjoint
coordinate support. -/
theorem rationalValue_factors_disjoint (place : Fin 3) :
    ∀ i, rationalValueA place i * rationalValueB place i = 0 := by
  intro i
  fin_cases place <;> fin_cases i <;>
    simp [rationalValueA, rationalValueB, aOneEval, bOneEval,
      aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
      Fin.sum_univ_succ]

/-- Every rational value direction is already in the first-order envelope. -/
theorem rationalValueTwo_mem_firstOrderEnvelope (place : Fin 3) :
    targetTwo (rationalValueCoeff place) ∈ firstOrderEnvelopeTwoSpace := by
  refine ⟨rationalValueCoeff place, ?_, rfl⟩
  change rationalValueCoeff place ∈ firstOrderEnvelopeCoeffSpace
  rw [mem_firstOrderEnvelopeCoeffSpace]
  fin_cases place <;>
    simp [firstOrderMissingFunctional, rationalValueCoeff,
      rZeroCoeff, rOneCoeff, rInfinityCoeff]

@[simp] theorem ambientBooleanContraction_pair
    (ell : LinearForm) (q : TwoForm)
    (i j : Fin 10) (hij : i ≠ j) :
    ambientBooleanContraction ell q (quadraticPair i j hij) =
      (ell i + ell j) * q (quadraticPair i j hij) := by
  simp [ambientBooleanContraction, quadraticPair, hij]

/-- Coordinate formula for the complete Boolean quadratic shadow. -/
theorem lowProductQuadraticShadow_pair
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (i j : Fin 10) (hij : i ≠ j) :
    lowProductQuadraticShadow a b ell m q c
        (quadraticPair i j hij) =
      a * c (quadraticPair i j hij) +
      b * q (quadraticPair i j hij) +
      (ell i * m j + ell j * m i) +
      (ell i + ell j) * c (quadraticPair i j hij) +
      (m i + m j) * q (quadraticPair i j hij) +
      q (quadraticPair i j hij) * c (quadraticPair i j hij) := by
  simp [lowProductQuadraticShadow, ambientTwoHadamard,
    squarefreeWedge_pair]

/-- When only the two linear parts change, the common terms in the two
Boolean quadratic shadows cancel.  This is the algebraic normal form used
to separate the two decomposable exterior products from the local Boolean
correction. -/
theorem lowProductQuadraticShadow_linear_difference
    (a b a' b' : F₂) (ell m x y : LinearForm) (q c : TwoForm) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' (ell + x) (m + y) q c =
      (a + a') • c + (b + b') • q +
        squarefreeWedge ell y + squarefreeWedge x m +
          (squarefreeWedge x y + ambientBooleanContraction x c +
            ambientBooleanContraction y q) := by
  rw [lowProductQuadraticShadow, lowProductQuadraticShadow,
    squarefreeWedge_add_left, squarefreeWedge_add_right,
    ambientBooleanContraction_add_left]
  rw [squarefreeWedge_add_right, ambientBooleanContraction_add_left]
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Boolean contraction by a decomposable two-form whose two factors have
disjoint coordinate support.  A linear combination of those factors acts by
the sum of its two coefficients. -/
theorem ambientBooleanContraction_factorSpan_of_disjoint
    (u v : LinearForm) (hdisjoint : ∀ i, u i * v i = 0)
    (p q : F₂) :
    ambientBooleanContraction (p • u + q • v) (squarefreeWedge u v) =
      (p + q) • squarefreeWedge u v := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  rw [ambientBooleanContraction_pair]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    squarefreeWedge_pair]
  have hi := hdisjoint i
  have hj := hdisjoint j
  ring_nf at hi hj ⊢
  simp only [N3Certificate.pow_two_f2]
  linear_combination
    u j * p * hi + v j * q * hi + u i * p * hj + v i * q * hj

/-- Universal Boolean lowering identity for a rational value--jet frame.
The two sides of the local frame may have arbitrary internal overlap; only
their `A`/`B` coordinate blocks must be disjoint. -/
theorem rationalValueJet_booleanCorrection_identity
    (A A' B B' : LinearForm)
    (hAB : ∀ i, A i * B i = 0)
    (hAB' : ∀ i, A i * B' i = 0)
    (hA'B : ∀ i, A' i * B i = 0)
    (p q r s : F₂) (x y : LinearForm)
    (hx : x = p • A + q • B)
    (hy : y = r • A + p • A' + s • B + q • B') :
    squarefreeWedge x y +
        ambientBooleanContraction x
          (squarefreeWedge A B' + squarefreeWedge A' B) +
        ambientBooleanContraction y (squarefreeWedge A B) =
      ((p * s + q * r + r + s) • squarefreeWedge A B +
          (p * q) •
            (squarefreeWedge A B' + squarefreeWedge A' B)) +
        squarefreeWedge x (A' + B') := by
  funext t
  rcases QuadraticIndex.exists_pair t with ⟨i, j, hij, rfl⟩
  have hABi := hAB i
  have hABj := hAB j
  have hAB'i := hAB' i
  have hAB'j := hAB' j
  have hA'Bi := hA'B i
  have hA'Bj := hA'B j
  simp only [hx, hy, squarefreeWedge_pair,
    ambientBooleanContraction_pair, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring_nf at hABi hABj hAB'i hAB'j hA'Bi hA'Bj ⊢
  simp [N3Certificate.pow_two_f2, N3Certificate.two_eq_zero_f2,
    hABi, hABj]
  ring_nf
  linear_combination
    A i * r * hABj + A j * p * hAB'i + A i * p * hAB'j +
    B j * q * hAB'i + A i * p * hA'Bj + B i * s * hABj +
    A j * p * hA'Bi + B i * q * hAB'j + B i * q * hA'Bj +
    B j * q * hA'Bi

/-- For two transverse decomposable cross-directions, a cubic syzygy already
written in the four factor coordinates has a one-decomposable Boolean
correction modulo any envelope containing the two directions. -/
theorem transversePair_booleanCorrection_decomposition
    (W : Submodule F₂ TwoForm)
    (A B U V : LinearForm)
    (hAB : ∀ i, A i * B i = 0) (hUV : ∀ i, U i * V i = 0)
    (p q r s : F₂) (x y : LinearForm)
    (hx : x = p • U + q • V) (hy : y = r • A + s • B)
    (hq : squarefreeWedge A B ∈ W)
    (hc : squarefreeWedge U V ∈ W) :
    ∃ zform ∈ W, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x (squarefreeWedge U V) +
          ambientBooleanContraction y (squarefreeWedge A B) =
        zform + squarefreeWedge x z := by
  refine ⟨(p + q) • squarefreeWedge U V +
      (r + s) • squarefreeWedge A B,
    W.add_mem (W.smul_mem _ hc) (W.smul_mem _ hq), y, ?_⟩
  rw [hx, hy,
    ambientBooleanContraction_factorSpan_of_disjoint U V hUV p q,
    ambientBooleanContraction_factorSpan_of_disjoint A B hAB r s]
  module

/-- Equality of two cubic parts is equivalently a zero cubic syzygy for the
two changed linear parts. -/
theorem factorPlaneCubic_difference_eq_zero
    (ell m ell' m' : LinearForm) (q c : TwoForm)
    (h : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q c) :
    factorPlaneCubic (ell + ell') (m + m') q c = 0 := by
  change (ambientVectorWedgeMap c) (ell + ell') +
      (ambientVectorWedgeMap q) (m + m') = 0
  rw [map_add, map_add]
  funext i j k
  have hcoord := congrFun (congrFun (congrFun h i) j) k
  change ambientVectorWedgeTwo ell c i j k +
      ambientVectorWedgeTwo m q i j k =
    ambientVectorWedgeTwo ell' c i j k +
      ambientVectorWedgeTwo m' q i j k at hcoord
  simp only [Pi.add_apply, Pi.zero_apply]
  let A := ambientVectorWedgeTwo ell c i j k
  let B := ambientVectorWedgeTwo m q i j k
  let C := ambientVectorWedgeTwo ell' c i j k
  let D := ambientVectorWedgeTwo m' q i j k
  change (A + C) + (B + D) = 0
  change A + B = C + D at hcoord
  calc
    (A + C) + (B + D) = (A + B) + (C + D) := by ac_rfl
    _ = (C + D) + (C + D) := by rw [hcoord]
    _ = 0 := CharTwo.add_self_eq_zero (C + D)

/-- Sparse solution of the cubic syzygy
`x ∧ j₀ + y ∧ r₀ = 0` on precisely the coordinates used by the
Hankel shadow calculation. -/
theorem rationalZero_cubic_syzygy
    (x y : LinearForm)
    (h : factorPlaneCubic x y rationalZeroValueTwo
      rationalZeroJetTwo = 0) :
    x (aCoord 1) = 0 ∧
    x (aCoord 2) = 0 ∧
    x (aCoord 3) = 0 ∧
    x (aCoord 4) = 0 ∧
    x (bCoord 1) = 0 ∧
    x (bCoord 2) = 0 ∧
    x (bCoord 3) = 0 ∧
    x (bCoord 4) = 0 ∧
    y (aCoord 1) = x (aCoord 0) ∧
    y (aCoord 2) = 0 ∧
    y (aCoord 3) = 0 ∧
    y (aCoord 4) = 0 ∧
    y (bCoord 1) = x (bCoord 0) ∧
    y (bCoord 2) = 0 ∧
    y (bCoord 3) = 0 ∧
    y (bCoord 4) = 0 := by
  have h016 := congrFun (congrFun (congrFun h
    (aCoord 0)) (aCoord 1)) (bCoord 1)
  have h012 := congrFun (congrFun (congrFun h
    (aCoord 0)) (aCoord 1)) (bCoord 0)
  have h056 := congrFun (congrFun (congrFun h
    (aCoord 0)) (bCoord 0)) (bCoord 1)
  have h156 := congrFun (congrFun (congrFun h
    (aCoord 1)) (bCoord 0)) (bCoord 1)
  have hExternal (e : Fin 10)
      (he0 : e ≠ aCoord 0) (he1 : e ≠ aCoord 1)
      (he5 : e ≠ bCoord 0) (he6 : e ≠ bCoord 1) :
      x e = 0 ∧ y e = 0 := by
    have hx := congrFun (congrFun (congrFun h e)
      (aCoord 1)) (bCoord 0)
    have hy := congrFun (congrFun (congrFun h e)
      (aCoord 0)) (bCoord 0)
    constructor
    · simpa [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, rationalZeroValueTwo,
        rationalZeroJetTwo, targetPairTwo,
        ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
        aLinear, bLinear, Pi.basisFun, he0, he1, he5, he6,
        aCoord_ne_bCoord, bCoord_ne_aCoord] using hx
    · simpa [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, rationalZeroValueTwo,
        rationalZeroJetTwo, targetPairTwo,
        ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
        aLinear, bLinear, Pi.basisFun, he0, he1, he5, he6,
        aCoord_ne_bCoord, bCoord_ne_aCoord] using hy
  have hA2 := hExternal (aCoord 2) (by simp) (by simp)
    (aCoord_ne_bCoord 2 0) (aCoord_ne_bCoord 2 1)
  have hA3 := hExternal (aCoord 3) (by simp) (by simp)
    (aCoord_ne_bCoord 3 0) (aCoord_ne_bCoord 3 1)
  have hA4 := hExternal (aCoord 4) (by simp) (by simp)
    (aCoord_ne_bCoord 4 0) (aCoord_ne_bCoord 4 1)
  have hB2 := hExternal (bCoord 2)
    (bCoord_ne_aCoord 2 0) (bCoord_ne_aCoord 2 1) (by simp) (by simp)
  have hB3 := hExternal (bCoord 3)
    (bCoord_ne_aCoord 3 0) (bCoord_ne_aCoord 3 1) (by simp) (by simp)
  have hB4 := hExternal (bCoord 4)
    (bCoord_ne_aCoord 4 0) (bCoord_ne_aCoord 4 1) (by simp) (by simp)
  have hx1 : x (aCoord 1) = 0 := by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, rationalZeroValueTwo,
      rationalZeroJetTwo, targetPairTwo,
      ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
      aLinear, bLinear, Pi.basisFun] using h016
  have hx6 : x (bCoord 1) = 0 := by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, rationalZeroValueTwo,
      rationalZeroJetTwo, targetPairTwo,
      ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
      aLinear, bLinear, Pi.basisFun] using h156
  have hy1 : y (aCoord 1) = x (aCoord 0) := by
    have hxy : x (aCoord 0) + y (aCoord 1) = 0 := by
      simpa [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, rationalZeroValueTwo,
      rationalZeroJetTwo, targetPairTwo,
      ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
      aLinear, bLinear, Pi.basisFun, add_comm] using h012
    rw [← CharTwo.sub_eq_add] at hxy
    exact (sub_eq_zero.mp hxy).symm
  have hy6 : y (bCoord 1) = x (bCoord 0) := by
    have hxy : x (bCoord 0) + y (bCoord 1) = 0 := by
      simpa [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, rationalZeroValueTwo,
      rationalZeroJetTwo, targetPairTwo,
      ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
      aLinear, bLinear, Pi.basisFun, add_comm] using h056
    rw [← CharTwo.sub_eq_add] at hxy
    exact (sub_eq_zero.mp hxy).symm
  exact ⟨hx1, hA2.1, hA3.1, hA4.1,
    hx6, hB2.1, hB3.1, hB4.1,
    hy1, hA2.2, hA3.2, hA4.2,
    hy6, hB2.2, hB3.2, hB4.2⟩

/-- Sparse cubic kernel at infinity.  It is the reversed rational-zero
kernel, stated intrinsically in the value/jet frame. -/
theorem rationalInfinity_cubic_syzygy
    (x y : LinearForm)
    (h : factorPlaneCubic x y rationalInfinityValueTwo
      rationalInfinityJetTwo = 0) :
    ∃ p q r s : F₂,
      x = p • aLinear 4 + q • bLinear 4 ∧
      y = r • aLinear 4 + p • aLinear 3 +
        s • bLinear 4 + q • bLinear 3 := by
  have hc (i j k : Fin 10) := congrFun (congrFun (congrFun h i) j) k
  have hExternal (e : Fin 10)
      (heA4 : e ≠ aCoord 4) (heA3 : e ≠ aCoord 3)
      (heB4 : e ≠ bCoord 4) (heB3 : e ≠ bCoord 3) :
      x e = 0 ∧ y e = 0 := by
    have hx := hc e (aCoord 3) (bCoord 4)
    have hy := hc e (aCoord 4) (bCoord 4)
    constructor
    · simpa [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, rationalInfinityValueTwo,
        rationalInfinityJetTwo, targetPairTwo,
        ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
        aLinear, bLinear, Pi.basisFun, heA4, heA3, heB4, heB3,
        aCoord_ne_bCoord, bCoord_ne_aCoord] using hx
    · simpa [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, rationalInfinityValueTwo,
        rationalInfinityJetTwo, targetPairTwo,
        ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
        aLinear, bLinear, Pi.basisFun, heA4, heA3, heB4, heB3,
        aCoord_ne_bCoord, bCoord_ne_aCoord] using hy
  have hA0 := hExternal (aCoord 0) (by simp) (by simp)
    (aCoord_ne_bCoord 0 4) (aCoord_ne_bCoord 0 3)
  have hA1 := hExternal (aCoord 1) (by simp) (by simp)
    (aCoord_ne_bCoord 1 4) (aCoord_ne_bCoord 1 3)
  have hA2 := hExternal (aCoord 2) (by simp) (by simp)
    (aCoord_ne_bCoord 2 4) (aCoord_ne_bCoord 2 3)
  have hB0 := hExternal (bCoord 0)
    (bCoord_ne_aCoord 0 4) (bCoord_ne_aCoord 0 3) (by simp) (by simp)
  have hB1 := hExternal (bCoord 1)
    (bCoord_ne_aCoord 1 4) (bCoord_ne_aCoord 1 3) (by simp) (by simp)
  have hB2 := hExternal (bCoord 2)
    (bCoord_ne_aCoord 2 4) (bCoord_ne_aCoord 2 3) (by simp) (by simp)
  have hxA3 : x (aCoord 3) = 0 := by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, rationalInfinityValueTwo,
      rationalInfinityJetTwo, targetPairTwo,
      ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
      aLinear, bLinear, Pi.basisFun] using
      hc (aCoord 4) (aCoord 3) (bCoord 3)
  have hxB3 : x (bCoord 3) = 0 := by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, rationalInfinityValueTwo,
      rationalInfinityJetTwo, targetPairTwo,
      ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
      aLinear, bLinear, Pi.basisFun] using
      hc (aCoord 3) (bCoord 4) (bCoord 3)
  have hyA3 : y (aCoord 3) = x (aCoord 4) := by
    have hxy : x (aCoord 4) + y (aCoord 3) = 0 := by
      simpa [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, rationalInfinityValueTwo,
        rationalInfinityJetTwo, targetPairTwo,
        ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
        aLinear, bLinear, Pi.basisFun, add_comm] using
        hc (aCoord 4) (aCoord 3) (bCoord 4)
    rw [← CharTwo.sub_eq_add] at hxy
    exact (sub_eq_zero.mp hxy).symm
  have hyB3 : y (bCoord 3) = x (bCoord 4) := by
    have hxy : x (bCoord 4) + y (bCoord 3) = 0 := by
      simpa [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, rationalInfinityValueTwo,
        rationalInfinityJetTwo, targetPairTwo,
        ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
        aLinear, bLinear, Pi.basisFun, add_comm] using
        hc (aCoord 4) (bCoord 4) (bCoord 3)
    rw [← CharTwo.sub_eq_add] at hxy
    exact (sub_eq_zero.mp hxy).symm
  refine ⟨x (aCoord 4), x (bCoord 4), y (aCoord 4), y (bCoord 4), ?_, ?_⟩
  · funext i
    fin_cases i <;> simp_all [aLinear, bLinear, Pi.basisFun, aCoord, bCoord]
  · funext i
    fin_cases i <;> simp_all [aLinear, bLinear, Pi.basisFun, aCoord, bCoord]

/-- Sparse cubic kernel at the rational place one.  Sixteen named exterior
coordinates recover the four local value/jet coefficients; no assignments
of the twenty scalar coordinates are enumerated. -/
theorem rationalOne_cubic_syzygy
    (x y : LinearForm)
    (h : factorPlaneCubic x y rationalOneValueTwo
      rationalOneJetTwo = 0) :
    ∃ p q r s : F₂,
      x = p • aOneEval + q • bOneEval ∧
      y = r • aOneEval + p • aOneJet +
        s • bOneEval + q • bOneJet := by
  have hc (i j k : Fin 10) := congrFun (congrFun (congrFun h i) j) k
  have h025 := hc (aCoord 0) (aCoord 2) (bCoord 0)
  have h045 := hc (aCoord 0) (aCoord 4) (bCoord 0)
  have h057 := hc (aCoord 0) (bCoord 0) (bCoord 2)
  have h059 := hc (aCoord 0) (bCoord 0) (bCoord 4)
  have h136 := hc (aCoord 1) (aCoord 3) (bCoord 1)
  have h168 := hc (aCoord 1) (bCoord 1) (bCoord 3)
  have h015 := hc (aCoord 0) (aCoord 1) (bCoord 0)
  have h016 := hc (aCoord 0) (aCoord 1) (bCoord 1)
  have h036 := hc (aCoord 0) (aCoord 3) (bCoord 1)
  have h056 := hc (aCoord 0) (bCoord 0) (bCoord 1)
  have h067 := hc (aCoord 0) (bCoord 1) (bCoord 2)
  have h069 := hc (aCoord 0) (bCoord 1) (bCoord 4)
  have h125 := hc (aCoord 1) (aCoord 2) (bCoord 0)
  have h145 := hc (aCoord 1) (aCoord 4) (bCoord 0)
  have h156 := hc (aCoord 1) (bCoord 0) (bCoord 1)
  have h158 := hc (aCoord 1) (bCoord 0) (bCoord 3)
  simp [factorPlaneCubic, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, rationalOneValueTwo, rationalOneJetTwo,
    ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
    aOneEval, aOneJet, bOneEval, bOneJet,
    aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
    Fin.sum_univ_succ, CharTwo.add_self_eq_zero] at h025 h045 h057 h059 h136 h168 h015 h016 h036 h056 h067 h069 h125 h145 h156 h158
  have hxA1 : x 1 = x 0 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h015 + h016
  have hxA2 : x 2 = x 0 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h025 + h015 + h125
  have hxA3 : x 3 = x 0 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h136 + h015 + h036
  have hxA4 : x 4 = x 0 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h045 + h015 + h145
  have hxB1 : x 6 = x 5 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h056 + h156
  have hxB2 : x 7 = x 5 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h057 + h056 + h067
  have hxB3 : x 8 = x 5 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h168 + h056 + h158
  have hxB4 : x 9 = x 5 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h059 + h056 + h069
  have hyA1 : y 1 = y 0 + x 0 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2])) h015
  have hyA2 : y 2 = y 0 := by
    exact h025.symm
  have hyA3 : y 3 = y 0 + x 0 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h136 + h015
  have hyA4 : y 4 = y 0 := by
    exact h045.symm
  have hyB1 : y 6 = y 5 + x 5 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2])) h056
  have hyB2 : y 7 = y 5 := by
    exact h057.symm
  have hyB3 : y 8 = y 5 + x 5 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
      h168 + h056
  have hyB4 : y 9 = y 5 := by
    exact h059.symm
  refine ⟨x (aCoord 0), x (bCoord 0), y (aCoord 0), y (bCoord 0), ?_, ?_⟩
  · funext i
    fin_cases i <;>
      simp [aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ,
        hxA1, hxA2, hxA3, hxA4, hxB1, hxB2, hxB3, hxB4]
  · funext i
    fin_cases i <;>
      simp [aOneEval, aOneJet, bOneEval, bOneJet,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        Fin.sum_univ_succ, hyA1, hyA2, hyA3, hyA4,
        hyB1, hyB2, hyB3, hyB4]

/-- Cubic kernel on the rational-value plane `⟨r₀,r₁⟩`.  The first changed
linear factor is supported on the value-one factors and the second on the
value-zero factors. -/
theorem rationalPair_zero_one_cubic_syzygy
    (x y : LinearForm)
    (h : factorPlaneCubic x y (rationalPairLeftValueTwo 0)
      (rationalPairRightValueTwo 0) = 0) :
    ∃ p q r s : F₂,
      x = p • rationalValueA 1 + q • rationalValueB 1 ∧
      y = r • rationalValueA 0 + s • rationalValueB 0 := by
  rw [rationalPairLeftValueTwo_eq_wedge,
    rationalPairRightValueTwo_eq_wedge] at h
  have hc (i j k : Fin 10) := congrFun (congrFun (congrFun h i) j) k
  have hadd (a b : F₂) (hab : a + b = 0) : b = a := by
    rw [add_comm, ← CharTwo.sub_eq_add] at hab
    exact sub_eq_zero.mp hab
  have hxA1 : x (aCoord 1) = x (aCoord 0) := hadd _ _ (by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] using
      hc (aCoord 0) (aCoord 1) (bCoord 1))
  have hxA2 : x (aCoord 2) = x (aCoord 0) := hadd _ _ (by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] using
      hc (aCoord 0) (aCoord 2) (bCoord 1))
  have hxA3 : x (aCoord 3) = x (aCoord 0) := hadd _ _ (by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] using
      hc (aCoord 0) (aCoord 3) (bCoord 1))
  have hxA4 : x (aCoord 4) = x (aCoord 0) := hadd _ _ (by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] using
      hc (aCoord 0) (aCoord 4) (bCoord 1))
  have hxB1 : x (bCoord 1) = x (bCoord 0) := hadd _ _ (by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] using
      hc (aCoord 1) (bCoord 0) (bCoord 1))
  have hxB2 : x (bCoord 2) = x (bCoord 0) := hadd _ _ (by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] using
      hc (aCoord 1) (bCoord 0) (bCoord 2))
  have hxB3 : x (bCoord 3) = x (bCoord 0) := hadd _ _ (by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] using
      hc (aCoord 1) (bCoord 0) (bCoord 3))
  have hxB4 : x (bCoord 4) = x (bCoord 0) := hadd _ _ (by
    simpa [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] using
      hc (aCoord 1) (bCoord 0) (bCoord 4))
  simp [aCoord, bCoord] at hxA1 hxA2 hxA3 hxA4 hxB1 hxB2 hxB3 hxB4
  have hyA1 : y (aCoord 1) = 0 := by
    have hz := hc (aCoord 0) (aCoord 1) (bCoord 0)
    simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hz
    rw [hxA1] at hz
    simpa [aCoord, CharTwo.add_self_eq_zero] using hz.symm
  have hyA2 : y (aCoord 2) = 0 := by
    have hz := hc (aCoord 0) (aCoord 2) (bCoord 0)
    simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hz
    rw [hxA2] at hz
    simpa [aCoord, CharTwo.add_self_eq_zero] using hz.symm
  have hyA3 : y (aCoord 3) = 0 := by
    have hz := hc (aCoord 0) (aCoord 3) (bCoord 0)
    simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hz
    rw [hxA3] at hz
    simpa [aCoord, CharTwo.add_self_eq_zero] using hz.symm
  have hyA4 : y (aCoord 4) = 0 := by
    have hz := hc (aCoord 0) (aCoord 4) (bCoord 0)
    simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hz
    rw [hxA4] at hz
    simpa [aCoord, CharTwo.add_self_eq_zero] using hz.symm
  have hyB1 : y (bCoord 1) = 0 := by
    have hz := hc (aCoord 0) (bCoord 0) (bCoord 1)
    simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hz
    rw [hxB1] at hz
    simpa [bCoord, CharTwo.add_self_eq_zero] using hz.symm
  have hyB2 : y (bCoord 2) = 0 := by
    have hz := hc (aCoord 0) (bCoord 0) (bCoord 2)
    simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hz
    rw [hxB2] at hz
    simpa [bCoord, CharTwo.add_self_eq_zero] using hz.symm
  have hyB3 : y (bCoord 3) = 0 := by
    have hz := hc (aCoord 0) (bCoord 0) (bCoord 3)
    simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hz
    rw [hxB3] at hz
    simpa [bCoord, CharTwo.add_self_eq_zero] using hz.symm
  have hyB4 : y (bCoord 4) = 0 := by
    have hz := hc (aCoord 0) (bCoord 0) (bCoord 4)
    simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_squarefreeWedge, rationalPairLeft, rationalPairRight,
      rationalValueA, rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
      Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hz
    rw [hxB4] at hz
    simpa [bCoord, CharTwo.add_self_eq_zero] using hz.symm
  simp [aCoord, bCoord] at hyA1 hyA2 hyA3 hyA4 hyB1 hyB2 hyB3 hyB4
  refine ⟨x (aCoord 0), x (bCoord 0),
    y (aCoord 0), y (bCoord 0), ?_, ?_⟩
  · funext i
    fin_cases i <;>
      simp [rationalValueA, rationalValueB, aOneEval, bOneEval,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        Fin.sum_univ_succ, hxA1, hxA2, hxA3, hxA4,
        hxB1, hxB2, hxB3, hxB4]
  · funext i
    fin_cases i <;>
      simp [rationalValueA, rationalValueB, aOneEval, bOneEval,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        Fin.sum_univ_succ, hyA1, hyA2, hyA3, hyA4,
        hyB1, hyB2, hyB3, hyB4]

/-- Cubic kernel on the rational-value plane `⟨r₀,r∞⟩`. -/
theorem rationalPair_zero_infinity_cubic_syzygy
    (x y : LinearForm)
    (h : factorPlaneCubic x y (rationalPairLeftValueTwo 1)
      (rationalPairRightValueTwo 1) = 0) :
    ∃ p q r s : F₂,
      x = p • rationalValueA 2 + q • rationalValueB 2 ∧
      y = r • rationalValueA 0 + s • rationalValueB 0 := by
  rw [rationalPairLeftValueTwo_eq_wedge,
    rationalPairRightValueTwo_eq_wedge] at h
  have hxA (i : Fin 5) (hi : i ≠ 4) : x (aCoord i) = 0 := by
    have hc := congrFun (congrFun (congrFun h
      (aCoord i)) (aCoord 4)) (bCoord 4)
    fin_cases i <;> try exact (hi rfl).elim
    all_goals
      simp [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, ambientTwoCoeff_squarefreeWedge,
        rationalPairLeft, rationalPairRight, rationalValueA,
        rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hc
      exact hc
  have hxB (i : Fin 5) (hi : i ≠ 4) : x (bCoord i) = 0 := by
    have hc := congrFun (congrFun (congrFun h
      (aCoord 4)) (bCoord i)) (bCoord 4)
    fin_cases i <;> try exact (hi rfl).elim
    all_goals
      simp [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, ambientTwoCoeff_squarefreeWedge,
        rationalPairLeft, rationalPairRight, rationalValueA,
        rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hc
      exact hc
  have hyA (j : Fin 5) (hj : j ≠ 0) : y (aCoord j) = 0 := by
    have hc := congrFun (congrFun (congrFun h
      (aCoord 0)) (aCoord j)) (bCoord 0)
    fin_cases j
    · exact (hj rfl).elim
    all_goals
      simp [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, ambientTwoCoeff_squarefreeWedge,
        rationalPairLeft, rationalPairRight, rationalValueA,
        rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hc
      exact hc
  have hyB (j : Fin 5) (hj : j ≠ 0) : y (bCoord j) = 0 := by
    have hc := congrFun (congrFun (congrFun h
      (aCoord 0)) (bCoord 0)) (bCoord j)
    fin_cases j
    · exact (hj rfl).elim
    all_goals
      simp [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, ambientTwoCoeff_squarefreeWedge,
        rationalPairLeft, rationalPairRight, rationalValueA,
        rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hc
      exact hc
  refine ⟨x (aCoord 4), x (bCoord 4),
    y (aCoord 0), y (bCoord 0), ?_, ?_⟩
  · funext i
    fin_cases i <;>
      simp [rationalValueA, rationalValueB, aOneEval, bOneEval,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        Fin.sum_univ_succ]
    all_goals first
      | simpa [aCoord] using hxA 0 (by decide)
      | simpa [aCoord] using hxA 1 (by decide)
      | simpa [aCoord] using hxA 2 (by decide)
      | simpa [aCoord] using hxA 3 (by decide)
      | simpa [bCoord] using hxB 0 (by decide)
      | simpa [bCoord] using hxB 1 (by decide)
      | simpa [bCoord] using hxB 2 (by decide)
      | simpa [bCoord] using hxB 3 (by decide)
  · funext i
    fin_cases i <;>
      simp [rationalValueA, rationalValueB, aOneEval, bOneEval,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        Fin.sum_univ_succ]
    all_goals first
      | simpa [aCoord] using hyA 1 (by decide)
      | simpa [aCoord] using hyA 2 (by decide)
      | simpa [aCoord] using hyA 3 (by decide)
      | simpa [aCoord] using hyA 4 (by decide)
      | simpa [bCoord] using hyB 1 (by decide)
      | simpa [bCoord] using hyB 2 (by decide)
      | simpa [bCoord] using hyB 3 (by decide)
      | simpa [bCoord] using hyB 4 (by decide)

/-- Cubic kernel on the rational-value plane `⟨r₁,r∞⟩`. -/
theorem rationalPair_one_infinity_cubic_syzygy
    (x y : LinearForm)
    (h : factorPlaneCubic x y (rationalPairLeftValueTwo 2)
      (rationalPairRightValueTwo 2) = 0) :
    ∃ p q r s : F₂,
      x = p • rationalValueA 2 + q • rationalValueB 2 ∧
      y = r • rationalValueA 1 + s • rationalValueB 1 := by
  rw [rationalPairLeftValueTwo_eq_wedge,
    rationalPairRightValueTwo_eq_wedge] at h
  have hyA (j : Fin 5) : y (aCoord j) = y (aCoord 0) := by
    have hc := congrFun (congrFun (congrFun h
      (aCoord 0)) (aCoord j)) (bCoord 0)
    fin_cases j
    · rfl
    all_goals
      simp [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, ambientTwoCoeff_squarefreeWedge,
        rationalPairLeft, rationalPairRight, rationalValueA,
        rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hc
      exact hc.symm
  have hyB (j : Fin 5) : y (bCoord j) = y (bCoord 0) := by
    have hc := congrFun (congrFun (congrFun h
      (aCoord 0)) (bCoord 0)) (bCoord j)
    fin_cases j
    · rfl
    all_goals
      simp [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, ambientTwoCoeff_squarefreeWedge,
        rationalPairLeft, rationalPairRight, rationalValueA,
        rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hc
      exact hc.symm
  have hxA (i : Fin 5) (hi : i ≠ 4) : x (aCoord i) = 0 := by
    have hc := congrFun (congrFun (congrFun h
      (aCoord i)) (aCoord 4)) (bCoord 4)
    have hyi := hyA i
    have hy4 := hyA 4
    simp only [factorPlaneCubic, Pi.add_apply, Pi.zero_apply,
      ambientVectorWedgeTwo, N4.vectorWedgeTwoN] at hc
    rw [hyi, hy4] at hc
    fin_cases i <;> try exact (hi rfl).elim
    all_goals
      simp [ambientTwoCoeff_squarefreeWedge,
        rationalPairLeft, rationalPairRight, rationalValueA,
        rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hc
      simpa [aCoord, CharTwo.add_self_eq_zero] using hc
  have hxB (i : Fin 5) (hi : i ≠ 4) : x (bCoord i) = 0 := by
    have hc := congrFun (congrFun (congrFun h
      (aCoord 4)) (bCoord i)) (bCoord 4)
    have hyi := hyB i
    have hy4 := hyB 4
    simp only [factorPlaneCubic, Pi.add_apply, Pi.zero_apply,
      ambientVectorWedgeTwo, N4.vectorWedgeTwoN] at hc
    rw [hyi, hy4] at hc
    fin_cases i <;> try exact (hi rfl).elim
    all_goals
      simp [ambientTwoCoeff_squarefreeWedge,
        rationalPairLeft, rationalPairRight, rationalValueA,
        rationalValueB, aOneEval, bOneEval, aLinear, bLinear,
        Pi.basisFun, aCoord, bCoord, Fin.sum_univ_succ] at hc
      simpa [bCoord, CharTwo.add_self_eq_zero] using hc
  refine ⟨x (aCoord 4), x (bCoord 4),
    y (aCoord 0), y (bCoord 0), ?_, ?_⟩
  · funext i
    fin_cases i <;>
      simp [rationalValueA, rationalValueB, aOneEval, bOneEval,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        Fin.sum_univ_succ]
    all_goals first
      | simpa [aCoord] using hxA 0 (by decide)
      | simpa [aCoord] using hxA 1 (by decide)
      | simpa [aCoord] using hxA 2 (by decide)
      | simpa [aCoord] using hxA 3 (by decide)
      | simpa [bCoord] using hxB 0 (by decide)
      | simpa [bCoord] using hxB 1 (by decide)
      | simpa [bCoord] using hxB 2 (by decide)
      | simpa [bCoord] using hxB 3 (by decide)
  · funext i
    fin_cases i <;>
      simp [rationalValueA, rationalValueB, aOneEval, bOneEval,
        aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
        Fin.sum_univ_succ]
    all_goals first
      | simpa [aCoord] using hyA 1
      | simpa [aCoord] using hyA 2
      | simpa [aCoord] using hyA 3
      | simpa [aCoord] using hyA 4
      | simpa [bCoord] using hyB 1
      | simpa [bCoord] using hyB 2
      | simpa [bCoord] using hyB 3
      | simpa [bCoord] using hyB 4

/-- Uniform cubic-kernel classification for the three rational-pair
exceptional planes. -/
theorem rationalPair_cubic_syzygy
    (pair : Fin 3) (x y : LinearForm)
    (h : factorPlaneCubic x y (rationalPairLeftValueTwo pair)
      (rationalPairRightValueTwo pair) = 0) :
    ∃ p q r s : F₂,
      x = p • rationalValueA (rationalPairRight pair) +
          q • rationalValueB (rationalPairRight pair) ∧
      y = r • rationalValueA (rationalPairLeft pair) +
          s • rationalValueB (rationalPairLeft pair) := by
  fin_cases pair
  · simpa [rationalPairLeft, rationalPairRight] using
      rationalPair_zero_one_cubic_syzygy x y h
  · simpa [rationalPairLeft, rationalPairRight] using
      rationalPair_zero_infinity_cubic_syzygy x y h
  · simpa [rationalPairLeft, rationalPairRight] using
      rationalPair_one_infinity_cubic_syzygy x y h

/-- On every rational-pair exceptional plane, the Boolean lowering
correction is one decomposable form modulo the first-order envelope. -/
theorem rationalPair_booleanCorrection_decomposition
    (pair : Fin 3) (x y : LinearForm)
    (hcubic : factorPlaneCubic x y (rationalPairLeftValueTwo pair)
      (rationalPairRightValueTwo pair) = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x (rationalPairRightValueTwo pair) +
          ambientBooleanContraction y (rationalPairLeftValueTwo pair) =
        r + squarefreeWedge x z := by
  rcases rationalPair_cubic_syzygy pair x y hcubic with
    ⟨p, q, r, s, hx, hy⟩
  rw [rationalPairLeftValueTwo_eq_wedge,
    rationalPairRightValueTwo_eq_wedge]
  exact transversePair_booleanCorrection_decomposition
    firstOrderEnvelopeTwoSpace
    (rationalValueA (rationalPairLeft pair))
    (rationalValueB (rationalPairLeft pair))
    (rationalValueA (rationalPairRight pair))
    (rationalValueB (rationalPairRight pair))
    (rationalValue_factors_disjoint (rationalPairLeft pair))
    (rationalValue_factors_disjoint (rationalPairRight pair))
    p q r s x y hx hy
    (by
      rw [← targetTwo_rationalValueCoeff]
      exact rationalValueTwo_mem_firstOrderEnvelope
        (rationalPairLeft pair))
    (by
      rw [← targetTwo_rationalValueCoeff]
      exact rationalValueTwo_mem_firstOrderEnvelope
        (rationalPairRight pair))

/-- A local Boolean correction which is one decomposable form modulo an old
quadratic envelope turns the whole shadow difference into two decomposable
forms modulo that envelope. -/
theorem lowProductShadow_decomposition_of_correction
    (W : Submodule F₂ TwoForm)
    (a b a' b' : F₂) (ell m x y : LinearForm) (q c : TwoForm)
    (hq : q ∈ W) (hc : c ∈ W)
    (r : TwoForm) (hr : r ∈ W) (z : LinearForm)
    (hcorrection :
      squarefreeWedge x y + ambientBooleanContraction x c +
          ambientBooleanContraction y q = r + squarefreeWedge x z) :
    ∃ r₀ ∈ W, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' (ell + x) (m + y) q c =
        r₀ + squarefreeWedge u v + squarefreeWedge s t := by
  refine ⟨(a + a') • c + (b + b') • q + r,
    W.add_mem (W.add_mem (W.smul_mem _ hc) (W.smul_mem _ hq)) hr,
    ell, y, x, m + z, ?_⟩
  rw [lowProductQuadraticShadow_linear_difference, hcorrection,
    squarefreeWedge_add_right]
  module

/-- Structural shadow form for all three rational-pair exceptional planes:
equal cubics leave only two decomposable forms modulo the first-order
envelope. -/
theorem rationalPair_shadow_decomposition
    (pair : Fin 3) (a b a' b' : F₂) (ell m x y : LinearForm)
    (hcubic : factorPlaneCubic x y (rationalPairLeftValueTwo pair)
      (rationalPairRightValueTwo pair) = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m
          (rationalPairLeftValueTwo pair)
          (rationalPairRightValueTwo pair) +
        lowProductQuadraticShadow a' b' (ell + x) (m + y)
          (rationalPairLeftValueTwo pair)
          (rationalPairRightValueTwo pair) =
        r + squarefreeWedge u v + squarefreeWedge s t := by
  rcases rationalPair_booleanCorrection_decomposition pair x y hcubic with
    ⟨r, hr, z, hcorrection⟩
  exact lowProductShadow_decomposition_of_correction
    firstOrderEnvelopeTwoSpace a b a' b' ell m x y
    (rationalPairLeftValueTwo pair) (rationalPairRightValueTwo pair)
    (rationalValueTwo_mem_firstOrderEnvelope (rationalPairLeft pair))
    (rationalValueTwo_mem_firstOrderEnvelope (rationalPairRight pair))
    r hr z hcorrection

/-- No rational-pair independent plane can produce the unique target coset
outside the first-order envelope. -/
theorem rationalPair_shadow_not_missingCoset
    (pair : Fin 3) (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic :
      factorPlaneCubic ell m (rationalPairLeftValueTwo pair)
          (rationalPairRightValueTwo pair) =
        factorPlaneCubic ell' m' (rationalPairLeftValueTwo pair)
          (rationalPairRightValueTwo pair))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m
          (rationalPairLeftValueTwo pair)
          (rationalPairRightValueTwo pair) +
        lowProductQuadraticShadow a' b' ell' m'
          (rationalPairLeftValueTwo pair)
          (rationalPairRightValueTwo pair) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  let x : LinearForm := ell + ell'
  let y : LinearForm := m + m'
  have hx : ell + x = ell' := by
    change ell + (ell + ell') = ell'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hy : m + y = m' := by
    change m + (m + m') = m'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hcubicZero :
      factorPlaneCubic x y (rationalPairLeftValueTwo pair)
        (rationalPairRightValueTwo pair) = 0 :=
    factorPlaneCubic_difference_eq_zero ell m ell' m'
      (rationalPairLeftValueTwo pair) (rationalPairRightValueTwo pair)
      hcubic
  rcases rationalPair_shadow_decomposition pair
      a b a' b' ell m x y hcubicZero with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  have hdecomp' :
      lowProductQuadraticShadow a b ell m
            (rationalPairLeftValueTwo pair)
            (rationalPairRightValueTwo pair) +
          lowProductQuadraticShadow a' b' ell' m'
            (rationalPairLeftValueTwo pair)
            (rationalPairRightValueTwo pair) =
        r + squarefreeWedge p q + squarefreeWedge s t := by
    simpa only [hx, hy] using hdecomp
  exact hdecomp'.symm.trans hmissing

/-- The degree-two exceptional plane has trivial cubic syzygy kernel.  The
twenty scalar unknowns are removed by twenty sparse Hankel pivots. -/
theorem dStar_cubic_syzygy (x y : LinearForm)
    (h : factorPlaneCubic x y dStarZeroTwo dStarOneTwo = 0) :
    x = 0 ∧ y = 0 := by
  have hc (i j k : Fin 10) := congrFun (congrFun (congrFun h i) j) k
  have h026 := hc (aCoord 0) (aCoord 2) (bCoord 1)
  have h018 := hc (aCoord 0) (aCoord 1) (bCoord 3)
  have h016 := hc (aCoord 0) (aCoord 1) (bCoord 1)
  have h028 := hc (aCoord 0) (aCoord 2) (bCoord 3)
  have h038 := hc (aCoord 0) (aCoord 3) (bCoord 3)
  have h048 := hc (aCoord 0) (aCoord 4) (bCoord 3)
  have h058 := hc (aCoord 0) (bCoord 0) (bCoord 3)
  have h068 := hc (aCoord 0) (bCoord 1) (bCoord 3)
  have h078 := hc (aCoord 0) (bCoord 2) (bCoord 3)
  have h168 := hc (aCoord 1) (bCoord 1) (bCoord 3)
  have h178 := hc (aCoord 1) (bCoord 2) (bCoord 3)
  have h089 := hc (aCoord 0) (bCoord 3) (bCoord 4)
  have h017 := hc (aCoord 0) (aCoord 1) (bCoord 2)
  have h027 := hc (aCoord 0) (aCoord 2) (bCoord 2)
  have h037 := hc (aCoord 0) (aCoord 3) (bCoord 2)
  have h047 := hc (aCoord 0) (aCoord 4) (bCoord 2)
  have h057 := hc (aCoord 0) (bCoord 0) (bCoord 2)
  have h067 := hc (aCoord 0) (bCoord 1) (bCoord 2)
  have h167 := hc (aCoord 1) (bCoord 1) (bCoord 2)
  have h079 := hc (aCoord 0) (bCoord 2) (bCoord 4)
  simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff, dStarZeroTwo, dStarOneTwo, dStarZeroCoeff,
    dStarOneCoeff, hankelIndex, aCoord_ne_bCoord] at h026 h018 h016 h028 h038 h048 h058 h068 h078 h168
  simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff, dStarZeroTwo, dStarOneTwo, dStarZeroCoeff,
    dStarOneCoeff, hankelIndex, aCoord_ne_bCoord] at h178 h089 h017 h027 h037 h047 h057 h067 h167 h079
  have hx0 : x (aCoord 0) = 0 := h026
  have hx1 : x (aCoord 1) = 0 := h018
  have hy0 : y (aCoord 0) = 0 := h016
  have hx2 : x (aCoord 2) = 0 := by simpa [hy0] using h028
  have hx3 : x (aCoord 3) = 0 := by simpa [hx0] using h038.symm
  have hx4 : x (aCoord 4) = 0 := h048
  have hx5 : x (bCoord 0) = 0 := h058
  have hx6 : x (bCoord 1) = 0 := h068
  have hy8 : y (bCoord 3) = 0 := h168
  have hx7 : x (bCoord 2) = 0 := by simpa [hy8] using h078
  have hx8 : x (bCoord 3) = 0 := h178
  have hx9 : x (bCoord 4) = 0 := h089
  have hy1 : y (aCoord 1) = 0 := by simpa [hx0] using h017.symm
  have hy2 : y (aCoord 2) = 0 := h027
  have hy3 : y (aCoord 3) = 0 := by simpa [hy0] using h037.symm
  have hy4 : y (aCoord 4) = 0 := by simpa [hx0] using h047.symm
  have hy5 : y (bCoord 0) = 0 := h057
  have hy6 : y (bCoord 1) = 0 := h067
  have hy7 : y (bCoord 2) = 0 := by simpa [hx6] using h167.symm
  have hy9 : y (bCoord 4) = 0 := h079
  constructor
  · funext i
    fin_cases i <;> simp_all [aCoord, bCoord]
  · funext i
    fin_cases i <;> simp_all [aCoord, bCoord]

theorem dStarZeroTwo_mem_firstOrderEnvelope :
    dStarZeroTwo ∈ firstOrderEnvelopeTwoSpace := by
  refine ⟨dStarZeroCoeff,
    Submodule.subset_span ⟨6, by simp [closedPlaceDirections]⟩, rfl⟩

theorem dStarOneTwo_mem_firstOrderEnvelope :
    dStarOneTwo ∈ firstOrderEnvelopeTwoSpace := by
  refine ⟨dStarOneCoeff,
    Submodule.subset_span ⟨7, by simp [closedPlaceDirections]⟩, rfl⟩

/-- Equal cubics on `D_*` leave a quadratic shadow already contained in the
first-order envelope. -/
theorem dStar_shadow_mem_firstOrderEnvelope
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m dStarZeroTwo dStarOneTwo =
      factorPlaneCubic ell' m' dStarZeroTwo dStarOneTwo) :
    lowProductQuadraticShadow a b ell m dStarZeroTwo dStarOneTwo +
        lowProductQuadraticShadow a' b' ell' m'
          dStarZeroTwo dStarOneTwo ∈ firstOrderEnvelopeTwoSpace := by
  let x : LinearForm := ell + ell'
  let y : LinearForm := m + m'
  have hx : ell + x = ell' := by
    change ell + (ell + ell') = ell'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hy : m + y = m' := by
    change m + (m + m') = m'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hcubicZero : factorPlaneCubic x y dStarZeroTwo dStarOneTwo = 0 :=
    factorPlaneCubic_difference_eq_zero ell m ell' m'
      dStarZeroTwo dStarOneTwo hcubic
  rcases dStar_cubic_syzygy x y hcubicZero with ⟨hx0, hy0⟩
  have hell : ell = ell' := by
    rw [← hx, hx0, add_zero]
  have hm : m = m' := by
    rw [← hy, hy0, add_zero]
  let r : TwoForm :=
    (a + a') • dStarOneTwo + (b + b') • dStarZeroTwo
  have hr : r ∈ firstOrderEnvelopeTwoSpace :=
    firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.smul_mem _
        dStarOneTwo_mem_firstOrderEnvelope)
      (firstOrderEnvelopeTwoSpace.smul_mem _
        dStarZeroTwo_mem_firstOrderEnvelope)
  have hshadow := lowProductQuadraticShadow_linear_difference
    a b a' b' ell m (0 : LinearForm) 0 dStarZeroTwo dStarOneTwo
  rw [show lowProductQuadraticShadow a b ell m dStarZeroTwo dStarOneTwo +
        lowProductQuadraticShadow a' b' ell' m'
          dStarZeroTwo dStarOneTwo = r by
    rw [← hell, ← hm]
    simpa only [add_zero, squarefreeWedge_zero_left,
      squarefreeWedge_zero_right, ambientBooleanContraction_zero_left,
      r] using hshadow]
  exact hr

/-- The degree-two exceptional plane cannot produce the missing target
coset. -/
theorem dStar_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m dStarZeroTwo dStarOneTwo =
      factorPlaneCubic ell' m' dStarZeroTwo dStarOneTwo)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m dStarZeroTwo dStarOneTwo +
        lowProductQuadraticShadow a' b' ell' m'
          dStarZeroTwo dStarOneTwo ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  have hmem := dStar_shadow_mem_firstOrderEnvelope
    a b a' b' ell m ell' m' hcubic
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    _ hmem 0 0 0 0 u hu
  simpa using hmissing

/-- The Boolean lowering correction on the infinity value--jet plane is one
decomposable form modulo the first-order envelope. -/
theorem rationalInfinity_booleanCorrection_decomposition
    (x y : LinearForm)
    (hcubic : factorPlaneCubic x y rationalInfinityValueTwo
      rationalInfinityJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x rationalInfinityJetTwo +
          ambientBooleanContraction y rationalInfinityValueTwo =
        r + squarefreeWedge x z := by
  rcases rationalInfinity_cubic_syzygy x y hcubic with
    ⟨p, q, r, s, hx, hy⟩
  have hvalue : rationalInfinityValueTwo ∈
      firstOrderEnvelopeTwoSpace := by
    rw [rationalInfinityValueTwo_eq_target]
    simpa [exactFirstOrderDirections] using
      targetTwo_exactFirstOrderDirection_mem 2
  have hjet : rationalInfinityJetTwo ∈
      firstOrderEnvelopeTwoSpace := by
    rw [rationalInfinityJetTwo_eq_target]
    simpa [exactFirstOrderDirections] using
      targetTwo_exactFirstOrderDirection_mem 5
  have hAB : ∀ i, aLinear 4 i * bLinear 4 i = 0 := by
    intro i
    fin_cases i <;> simp [aLinear, bLinear, Pi.basisFun, aCoord, bCoord]
  have hAB' : ∀ i, aLinear 4 i * bLinear 3 i = 0 := by
    intro i
    fin_cases i <;> simp [aLinear, bLinear, Pi.basisFun, aCoord, bCoord]
  have hA'B : ∀ i, aLinear 3 i * bLinear 4 i = 0 := by
    intro i
    fin_cases i <;> simp [aLinear, bLinear, Pi.basisFun, aCoord, bCoord]
  let rform : TwoForm :=
    (p * s + q * r + r + s) • rationalInfinityValueTwo +
      (p * q) • rationalInfinityJetTwo
  refine ⟨rform,
    firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue)
      (firstOrderEnvelopeTwoSpace.smul_mem _ hjet),
    aLinear 3 + bLinear 3, ?_⟩
  simpa only [rform, rationalInfinityValueTwo,
    rationalInfinityJetTwo, targetPairTwo] using
    rationalValueJet_booleanCorrection_identity
      (aLinear 4) (aLinear 3) (bLinear 4) (bLinear 3)
      hAB hAB' hA'B p q r s x y hx hy

/-- Equal cubic parts on the infinity value--jet plane leave only two
decomposable quadratic forms modulo the first-order envelope. -/
theorem rationalInfinity_shadow_decomposition
    (a b a' b' : F₂) (ell m x y : LinearForm)
    (hcubic : factorPlaneCubic x y rationalInfinityValueTwo
      rationalInfinityJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m rationalInfinityValueTwo
          rationalInfinityJetTwo +
        lowProductQuadraticShadow a' b' (ell + x) (m + y)
          rationalInfinityValueTwo rationalInfinityJetTwo =
        r + squarefreeWedge u v + squarefreeWedge s t := by
  rcases rationalInfinity_booleanCorrection_decomposition x y hcubic with
    ⟨r, hr, z, hcorrection⟩
  have hvalue : rationalInfinityValueTwo ∈
      firstOrderEnvelopeTwoSpace := by
    rw [rationalInfinityValueTwo_eq_target]
    simpa [exactFirstOrderDirections] using
      targetTwo_exactFirstOrderDirection_mem 2
  have hjet : rationalInfinityJetTwo ∈
      firstOrderEnvelopeTwoSpace := by
    rw [rationalInfinityJetTwo_eq_target]
    simpa [exactFirstOrderDirections] using
      targetTwo_exactFirstOrderDirection_mem 5
  exact lowProductShadow_decomposition_of_correction
    firstOrderEnvelopeTwoSpace a b a' b' ell m x y
    rationalInfinityValueTwo rationalInfinityJetTwo
    hvalue hjet r hr z hcorrection

/-- The rational-infinity value--jet plane cannot produce the missing target
coset. -/
theorem rationalInfinity_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m rationalInfinityValueTwo
        rationalInfinityJetTwo =
      factorPlaneCubic ell' m' rationalInfinityValueTwo
        rationalInfinityJetTwo)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalInfinityValueTwo
          rationalInfinityJetTwo +
        lowProductQuadraticShadow a' b' ell' m' rationalInfinityValueTwo
          rationalInfinityJetTwo ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  let x : LinearForm := ell + ell'
  let y : LinearForm := m + m'
  have hx : ell + x = ell' := by
    change ell + (ell + ell') = ell'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hy : m + y = m' := by
    change m + (m + m') = m'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hcubicZero : factorPlaneCubic x y rationalInfinityValueTwo
      rationalInfinityJetTwo = 0 :=
    factorPlaneCubic_difference_eq_zero ell m ell' m'
      rationalInfinityValueTwo rationalInfinityJetTwo hcubic
  rcases rationalInfinity_shadow_decomposition
      a b a' b' ell m x y hcubicZero with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  have hdecomp' :
      lowProductQuadraticShadow a b ell m rationalInfinityValueTwo
            rationalInfinityJetTwo +
          lowProductQuadraticShadow a' b' ell' m'
            rationalInfinityValueTwo rationalInfinityJetTwo =
        r + squarefreeWedge p q + squarefreeWedge s t := by
    simpa only [hx, hy] using hdecomp
  exact hdecomp'.symm.trans hmissing

/-- The Boolean lowering correction on the rational-one value--jet plane is
one decomposable form modulo the first-order envelope. -/
theorem rationalOne_booleanCorrection_decomposition
    (x y : LinearForm)
    (hcubic : factorPlaneCubic x y rationalOneValueTwo
      rationalOneJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x rationalOneJetTwo +
          ambientBooleanContraction y rationalOneValueTwo =
        r + squarefreeWedge x z := by
  rcases rationalOne_cubic_syzygy x y hcubic with
    ⟨p, q, r, s, hx, hy⟩
  have hvalue : rationalOneValueTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [rationalOneValueTwo_eq_target]
    simpa [exactFirstOrderDirections] using
      targetTwo_exactFirstOrderDirection_mem 1
  have hjet : rationalOneJetTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [rationalOneJetTwo_eq_target]
    simpa [exactFirstOrderDirections] using
      targetTwo_exactFirstOrderDirection_mem 4
  have hAB : ∀ i, aOneEval i * bOneEval i = 0 := by
    intro i
    fin_cases i <;>
      simp [aOneEval, bOneEval, aLinear, bLinear, Pi.basisFun,
        aCoord, bCoord, Fin.sum_univ_succ]
  have hAB' : ∀ i, aOneEval i * bOneJet i = 0 := by
    intro i
    fin_cases i <;>
      simp [aOneEval, bOneJet, aLinear, bLinear, Pi.basisFun,
        aCoord, bCoord, Fin.sum_univ_succ]
  have hA'B : ∀ i, aOneJet i * bOneEval i = 0 := by
    intro i
    fin_cases i <;>
      simp [aOneJet, bOneEval, aLinear, bLinear, Pi.basisFun,
        aCoord, bCoord, Fin.sum_univ_succ]
  let rform : TwoForm :=
    (p * s + q * r + r + s) • rationalOneValueTwo +
      (p * q) • rationalOneJetTwo
  refine ⟨rform,
    firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue)
      (firstOrderEnvelopeTwoSpace.smul_mem _ hjet),
    aOneJet + bOneJet, ?_⟩
  simpa only [rform, rationalOneValueTwo, rationalOneJetTwo] using
    rationalValueJet_booleanCorrection_identity
      aOneEval aOneJet bOneEval bOneJet
      hAB hAB' hA'B p q r s x y hx hy

/-- Equal cubic parts on the rational-one value--jet plane leave only two
decomposable quadratic forms modulo the first-order envelope. -/
theorem rationalOne_shadow_decomposition
    (a b a' b' : F₂) (ell m x y : LinearForm)
    (hcubic : factorPlaneCubic x y rationalOneValueTwo
      rationalOneJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m rationalOneValueTwo
          rationalOneJetTwo +
        lowProductQuadraticShadow a' b' (ell + x) (m + y)
          rationalOneValueTwo rationalOneJetTwo =
        r + squarefreeWedge u v + squarefreeWedge s t := by
  rcases rationalOne_booleanCorrection_decomposition x y hcubic with
    ⟨r, hr, z, hcorrection⟩
  have hvalue : rationalOneValueTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [rationalOneValueTwo_eq_target]
    simpa [exactFirstOrderDirections] using
      targetTwo_exactFirstOrderDirection_mem 1
  have hjet : rationalOneJetTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [rationalOneJetTwo_eq_target]
    simpa [exactFirstOrderDirections] using
      targetTwo_exactFirstOrderDirection_mem 4
  exact lowProductShadow_decomposition_of_correction
    firstOrderEnvelopeTwoSpace a b a' b' ell m x y
    rationalOneValueTwo rationalOneJetTwo
    hvalue hjet r hr z hcorrection

/-- The rational-one value--jet plane cannot produce the missing target
coset. -/
theorem rationalOne_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m rationalOneValueTwo
        rationalOneJetTwo =
      factorPlaneCubic ell' m' rationalOneValueTwo rationalOneJetTwo)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalOneValueTwo
          rationalOneJetTwo +
        lowProductQuadraticShadow a' b' ell' m' rationalOneValueTwo
          rationalOneJetTwo ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  let x : LinearForm := ell + ell'
  let y : LinearForm := m + m'
  have hx : ell + x = ell' := by
    change ell + (ell + ell') = ell'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hy : m + y = m' := by
    change m + (m + m') = m'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hcubicZero : factorPlaneCubic x y rationalOneValueTwo
      rationalOneJetTwo = 0 :=
    factorPlaneCubic_difference_eq_zero ell m ell' m'
      rationalOneValueTwo rationalOneJetTwo hcubic
  rcases rationalOne_shadow_decomposition
      a b a' b' ell m x y hcubicZero with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  have hdecomp' :
      lowProductQuadraticShadow a b ell m rationalOneValueTwo
            rationalOneJetTwo +
          lowProductQuadraticShadow a' b' ell' m'
            rationalOneValueTwo rationalOneJetTwo =
        r + squarefreeWedge p q + squarefreeWedge s t := by
    simpa only [hx, hy] using hdecomp
  exact hdecomp'.symm.trans hmissing

/-- On the rational-zero value--jet plane, the Boolean lowering correction
is a single exterior product modulo the first-order envelope. -/
theorem rationalZero_booleanCorrection_decomposition
    (x y : LinearForm)
    (hcubic : factorPlaneCubic x y rationalZeroValueTwo
      rationalZeroJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x rationalZeroJetTwo +
          ambientBooleanContraction y rationalZeroValueTwo =
        r + squarefreeWedge x z := by
  rcases rationalZero_cubic_syzygy x y hcubic with
    ⟨hxA1, hxA2, hxA3, hxA4, hxB1, hxB2, hxB3, hxB4,
      hyA1, hyA2, hyA3, hyA4, hyB1, hyB2, hyB3, hyB4⟩
  let z : LinearForm := aLinear 1 + bLinear 1
  let r : TwoForm :=
    (x (aCoord 0) * y (bCoord 0) +
        x (bCoord 0) * y (aCoord 0) +
        y (aCoord 0) + y (bCoord 0)) • rationalZeroValueTwo +
      (x (aCoord 0) * x (bCoord 0)) • rationalZeroJetTwo
  have hvalue : rationalZeroValueTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [rationalZeroValueTwo_eq_target]
    exact ⟨rZeroCoeff,
      Submodule.subset_span ⟨0, by simp [closedPlaceDirections]⟩, rfl⟩
  have hjet : rationalZeroJetTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [rationalZeroJetTwo_eq_target]
    exact ⟨jZeroCoeff,
      Submodule.subset_span ⟨3, by simp [closedPlaceDirections]⟩, rfl⟩
  refine ⟨r, firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue)
      (firstOrderEnvelopeTwoSpace.smul_mem _ hjet), z, ?_⟩
  apply twoForm_ext_blocks
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [r, z, squarefreeWedge_pair,
        ambientBooleanContraction_pair,
        rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
        aLinear, bLinear, Pi.basisFun] <;>
      ring_nf <;> simp [N3Certificate.pow_two_f2]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [r, z, squarefreeWedge_pair,
        ambientBooleanContraction_pair,
        rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
        aLinear, bLinear, Pi.basisFun] <;>
      ring_nf <;> simp [N3Certificate.pow_two_f2]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [r, z, squarefreeWedge_pair,
        ambientBooleanContraction_pair,
        rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
        aLinear, bLinear, Pi.basisFun] <;>
      ring_nf

/-- Structural form of the canonical independent shadow comparison: equal
cubic parts leave only two decomposable quadratic forms modulo the envelope. -/
theorem rationalZero_shadow_decomposition
    (a b a' b' : F₂) (ell m x y : LinearForm)
    (hcubic : factorPlaneCubic x y rationalZeroValueTwo
      rationalZeroJetTwo = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' (ell + x) (m + y)
          rationalZeroValueTwo rationalZeroJetTwo =
        r + squarefreeWedge u v + squarefreeWedge s t := by
  rcases rationalZero_booleanCorrection_decomposition x y hcubic with
    ⟨r, hr, z, hcorrection⟩
  have hvalue : rationalZeroValueTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [rationalZeroValueTwo_eq_target]
    exact ⟨rZeroCoeff,
      Submodule.subset_span ⟨0, by simp [closedPlaceDirections]⟩, rfl⟩
  have hjet : rationalZeroJetTwo ∈ firstOrderEnvelopeTwoSpace := by
    rw [rationalZeroJetTwo_eq_target]
    exact ⟨jZeroCoeff,
      Submodule.subset_span ⟨3, by simp [closedPlaceDirections]⟩, rfl⟩
  exact lowProductShadow_decomposition_of_correction
    firstOrderEnvelopeTwoSpace a b a' b' ell m x y
      rationalZeroValueTwo rationalZeroJetTwo hvalue hjet
      r hr z hcorrection

set_option linter.unusedSimpArgs false in
/-- Canonical independent-plane target-shadow theorem at the rational zero
two-jet.  A shadow difference which is Hankel has zero missing coordinate. -/
theorem rationalZero_shadow_target_mem_firstOrder
    (a b a' b' : F₂) (ell m x y : LinearForm) (t : TargetCoeff)
    (hcubic : factorPlaneCubic x y rationalZeroValueTwo
      rationalZeroJetTwo = 0)
    (htarget :
      lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' (ell + x) (m + y)
          rationalZeroValueTwo rationalZeroJetTwo = targetTwo t) :
    firstOrderMissingFunctional t = 0 := by
  let D : TwoForm :=
    lowProductQuadraticShadow a b ell m rationalZeroValueTwo
        rationalZeroJetTwo +
      lowProductQuadraticShadow a' b' (ell + x) (m + y)
        rationalZeroValueTwo rationalZeroJetTwo
  have hD : D = targetTwo t := htarget
  rcases rationalZero_cubic_syzygy x y hcubic with
    ⟨hxA1, hxA2, _hxA3, _hxA4, hxB1, hxB2, hxB3, hxB4,
      hyA1, hyA2, _hyA3, _hyA4, hyB1, hyB2, hyB3, hyB4⟩
  have hAA02raw : D (quadraticPair (aCoord 0) (aCoord 2) (by decide)) = 0 := by
    calc
      D (quadraticPair (aCoord 0) (aCoord 2) (by decide)) =
          targetTwo t (quadraticPair (aCoord 0) (aCoord 2) (by decide)) :=
        congrFun hD _
      _ = 0 := by simp
  have hAA12raw : D (quadraticPair (aCoord 1) (aCoord 2) (by decide)) = 0 := by
    calc
      D (quadraticPair (aCoord 1) (aCoord 2) (by decide)) =
          targetTwo t (quadraticPair (aCoord 1) (aCoord 2) (by decide)) :=
        congrFun hD _
      _ = 0 := by simp
  have hBB02raw : D (quadraticPair (bCoord 0) (bCoord 2) (by decide)) = 0 := by
    calc
      D (quadraticPair (bCoord 0) (bCoord 2) (by decide)) =
          targetTwo t (quadraticPair (bCoord 0) (bCoord 2) (by decide)) :=
        congrFun hD _
      _ = 0 := by simp
  have hBB12raw : D (quadraticPair (bCoord 1) (bCoord 2) (by decide)) = 0 := by
    calc
      D (quadraticPair (bCoord 1) (bCoord 2) (by decide)) =
          targetTwo t (quadraticPair (bCoord 1) (bCoord 2) (by decide)) :=
        congrFun hD _
      _ = 0 := by simp
  have hH2raw :
      D (quadraticPair (aCoord 0) (bCoord 2) (aCoord_ne_bCoord 0 2)) =
        D (quadraticPair (aCoord 2) (bCoord 0) (aCoord_ne_bCoord 2 0)) := by
    calc
      D (quadraticPair (aCoord 0) (bCoord 2) (aCoord_ne_bCoord 0 2)) =
          targetTwo t
            (quadraticPair (aCoord 0) (bCoord 2) (aCoord_ne_bCoord 0 2)) :=
        congrFun hD _
      _ = targetTwo t
            (quadraticPair (aCoord 2) (bCoord 0) (aCoord_ne_bCoord 2 0)) := by
        simp [hankelIndex]
      _ = D (quadraticPair (aCoord 2) (bCoord 0)
            (aCoord_ne_bCoord 2 0)) := (congrFun hD _).symm
  have hH3Araw :
      D (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) =
        D (quadraticPair (aCoord 1) (bCoord 2) (aCoord_ne_bCoord 1 2)) := by
    calc
      D (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) =
          targetTwo t
            (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) :=
        congrFun hD _
      _ = targetTwo t
            (quadraticPair (aCoord 1) (bCoord 2) (aCoord_ne_bCoord 1 2)) := by
        simp [hankelIndex]
      _ = D (quadraticPair (aCoord 1) (bCoord 2)
            (aCoord_ne_bCoord 1 2)) := (congrFun hD _).symm
  have hH3Braw :
      D (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) =
        D (quadraticPair (aCoord 2) (bCoord 1) (aCoord_ne_bCoord 2 1)) := by
    calc
      D (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) =
          targetTwo t
            (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) :=
        congrFun hD _
      _ = targetTwo t
            (quadraticPair (aCoord 2) (bCoord 1) (aCoord_ne_bCoord 2 1)) := by
        simp [hankelIndex]
      _ = D (quadraticPair (aCoord 2) (bCoord 1)
            (aCoord_ne_bCoord 2 1)) := (congrFun hD _).symm
  have hAA02 :
      ell (aCoord 2) * y (aCoord 0) +
        m (aCoord 2) * x (aCoord 0) = 0 := by
    have h := hAA02raw
    simp [D, lowProductQuadraticShadow_pair,
      rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
      aLinear, bLinear, Pi.basisFun, hxA1, hxA2, hxB1, hxB2, hxB3,
      hxB4, hyA1, hyA2, hyB1, hyB2, hyB3, hyB4,
      N3Certificate.two_eq_zero_f2] at h
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
        N3Certificate.two_eq_zero_f2])) h
  have hAA12 : ell (aCoord 2) * x (aCoord 0) = 0 := by
    have h := hAA12raw
    simp [D, lowProductQuadraticShadow_pair,
      rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
      aLinear, bLinear, Pi.basisFun, hxA1, hxA2, hxB1, hxB2, hxB3,
      hxB4, hyA1, hyA2, hyB1, hyB2, hyB3, hyB4,
      N3Certificate.two_eq_zero_f2] at h
    rcases h with hx | he
    · simp [hx]
    · simp [he]
  have hBB02 :
      ell (bCoord 2) * y (bCoord 0) +
        m (bCoord 2) * x (bCoord 0) = 0 := by
    have h := hBB02raw
    simp [D, lowProductQuadraticShadow_pair,
      rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
      aLinear, bLinear, Pi.basisFun, hxA1, hxA2, hxB1, hxB2, hxB3,
      hxB4, hyA1, hyA2, hyB1, hyB2, hyB3, hyB4,
      N3Certificate.two_eq_zero_f2] at h
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
        N3Certificate.two_eq_zero_f2])) h
  have hBB12 : ell (bCoord 2) * x (bCoord 0) = 0 := by
    have h := hBB12raw
    simp [D, lowProductQuadraticShadow_pair,
      rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
      aLinear, bLinear, Pi.basisFun, hxA1, hxA2, hxB1, hxB2, hxB3,
      hxB4, hyA1, hyA2, hyB1, hyB2, hyB3, hyB4,
      N3Certificate.two_eq_zero_f2] at h
    rcases h with hx | he
    · simp [hx]
    · simp [he]
  have hH2 :
      ell (aCoord 2) * y (bCoord 0) +
      ell (bCoord 2) * y (aCoord 0) +
      m (aCoord 2) * x (bCoord 0) +
      m (bCoord 2) * x (aCoord 0) = 0 := by
    have hsum :
        D (quadraticPair (aCoord 0) (bCoord 2) (aCoord_ne_bCoord 0 2)) +
          D (quadraticPair (aCoord 2) (bCoord 0)
            (aCoord_ne_bCoord 2 0)) = 0 := by
      rw [hH2raw, CharTwo.add_self_eq_zero]
    have h := hsum
    simp [D, lowProductQuadraticShadow_pair,
      rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
      aLinear, bLinear, Pi.basisFun, hxA1, hxA2, hxB1, hxB2, hxB3,
      hxB4, hyA1, hyA2, hyB1, hyB2, hyB3, hyB4,
      N3Certificate.two_eq_zero_f2] at h
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
        N3Certificate.two_eq_zero_f2])) h
  have hH3A :
      ell (bCoord 2) * x (aCoord 0) +
      ell (bCoord 3) * y (aCoord 0) +
      m (bCoord 3) * x (aCoord 0) = 0 := by
    have hsum :
        D (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) +
          D (quadraticPair (aCoord 1) (bCoord 2)
            (aCoord_ne_bCoord 1 2)) = 0 := by
      rw [hH3Araw, CharTwo.add_self_eq_zero]
    have h := hsum
    simp [D, lowProductQuadraticShadow_pair,
      rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
      aLinear, bLinear, Pi.basisFun, hxA1, hxA2, hxB1, hxB2, hxB3,
      hxB4, hyA1, hyA2, hyB1, hyB2, hyB3, hyB4,
      N3Certificate.two_eq_zero_f2] at h
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
        N3Certificate.two_eq_zero_f2])) h
  have hH3B :
      ell (aCoord 2) * x (bCoord 0) +
      ell (bCoord 3) * y (aCoord 0) +
      m (bCoord 3) * x (aCoord 0) = 0 := by
    have hsum :
        D (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) +
          D (quadraticPair (aCoord 2) (bCoord 1)
            (aCoord_ne_bCoord 2 1)) = 0 := by
      rw [hH3Braw, CharTwo.add_self_eq_zero]
    have h := hsum
    simp [D, lowProductQuadraticShadow_pair,
      rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
      aLinear, bLinear, Pi.basisFun, hxA1, hxA2, hxB1, hxB2, hxB3,
      hxB4, hyA1, hyA2, hyB1, hyB2, hyB3, hyB4,
      N3Certificate.two_eq_zero_f2] at h
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
        N3Certificate.two_eq_zero_f2])) h
  have hpoly :
      ell (bCoord 2) * y (aCoord 0) +
      ell (bCoord 3) * y (aCoord 0) +
      m (bCoord 2) * x (aCoord 0) +
      m (bCoord 3) * x (aCoord 0) = 0 := by
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
        N3Certificate.two_eq_zero_f2]))
      x (bCoord 0) * hAA02 +
      (ell (bCoord 2) + y (bCoord 0)) * hAA12 +
      ell (aCoord 2) * hBB02 +
      m (aCoord 2) * hBB12 +
      (ell (bCoord 2) + x (aCoord 0)) * hH2 +
      (ell (aCoord 2) + m (bCoord 2) + y (aCoord 0)) * hH3A +
      (1 + ell (aCoord 2) + m (bCoord 2) + y (aCoord 0)) * hH3B
  have ht2 :
      D (quadraticPair (aCoord 0) (bCoord 2) (aCoord_ne_bCoord 0 2)) =
        t 2 := by
    simpa [hankelIndex] using congrFun hD
      (quadraticPair (aCoord 0) (bCoord 2) (aCoord_ne_bCoord 0 2))
  have ht3 :
      D (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) =
        t 3 := by
    simpa [hankelIndex] using congrFun hD
      (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3))
  have ht5 :
      D (quadraticPair (aCoord 2) (bCoord 3) (aCoord_ne_bCoord 2 3)) =
        t 5 := by
    simpa [hankelIndex] using congrFun hD
      (quadraticPair (aCoord 2) (bCoord 3) (aCoord_ne_bCoord 2 3))
  have ht6 :
      D (quadraticPair (aCoord 2) (bCoord 4) (aCoord_ne_bCoord 2 4)) =
        t 6 := by
    simpa [hankelIndex] using congrFun hD
      (quadraticPair (aCoord 2) (bCoord 4) (aCoord_ne_bCoord 2 4))
  change t 2 + t 3 + t 5 + t 6 = 0
  rw [← ht2, ← ht3, ← ht5, ← ht6]
  simp [D, lowProductQuadraticShadow_pair,
    rationalZeroValueTwo, rationalZeroJetTwo, targetPairTwo,
    aLinear, bLinear, Pi.basisFun, hxA1, hxA2, hxB1, hxB2, hxB3,
    hxB4, hyA1, hyA2, hyB1, hyB2, hyB3, hyB4,
    N3Certificate.two_eq_zero_f2]
  linear_combination
    (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
      N3Certificate.two_eq_zero_f2])) hpoly

/-- Presentation-independent form of the rational-zero shadow theorem. -/
theorem rationalZero_shadow_targetCoeff_mem
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (t : TargetCoeff)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo =
      factorPlaneCubic ell' m' rationalZeroValueTwo rationalZeroJetTwo)
    (htarget :
      lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' ell' m' rationalZeroValueTwo
          rationalZeroJetTwo = targetTwo t) :
    t ∈ firstOrderEnvelopeCoeffSpace := by
  let x : LinearForm := ell + ell'
  let y : LinearForm := m + m'
  have hx : ell + x = ell' := by
    change ell + (ell + ell') = ell'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hy : m + y = m' := by
    change m + (m + m') = m'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  apply (mem_firstOrderEnvelopeCoeffSpace t).2
  apply rationalZero_shadow_target_mem_firstOrder
    a b a' b' ell m x y t
  · exact factorPlaneCubic_difference_eq_zero ell m ell' m'
      rationalZeroValueTwo rationalZeroJetTwo hcubic
  · simpa only [hx, hy] using htarget

/-- The canonical independent value--jet plane cannot produce the unique
target coset outside the first-order envelope. -/
theorem rationalZero_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo =
      factorPlaneCubic ell' m' rationalZeroValueTwo rationalZeroJetTwo)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' ell' m' rationalZeroValueTwo
          rationalZeroJetTwo ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  let x : LinearForm := ell + ell'
  let y : LinearForm := m + m'
  have hx : ell + x = ell' := by
    change ell + (ell + ell') = ell'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hy : m + y = m' := by
    change m + (m + m') = m'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hcubicZero : factorPlaneCubic x y rationalZeroValueTwo
      rationalZeroJetTwo = 0 :=
    factorPlaneCubic_difference_eq_zero ell m ell' m'
      rationalZeroValueTwo rationalZeroJetTwo hcubic
  rcases rationalZero_shadow_decomposition
      a b a' b' ell m x y hcubicZero with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  have hdecomp' :
      lowProductQuadraticShadow a b ell m rationalZeroValueTwo
            rationalZeroJetTwo +
          lowProductQuadraticShadow a' b' ell' m' rationalZeroValueTwo
            rationalZeroJetTwo =
        r + squarefreeWedge p q + squarefreeWedge s t := by
    simpa only [hx, hy] using hdecomp
  exact hdecomp'.symm.trans hmissing

/-- Target-valued shadows on the canonical independent value--jet plane
actually lie in the embedded first-order envelope. -/
theorem rationalZero_shadow_mem_firstOrderEnvelopeTwoSpace
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (t : TargetCoeff)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo =
      factorPlaneCubic ell' m' rationalZeroValueTwo rationalZeroJetTwo)
    (htarget :
      lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' ell' m' rationalZeroValueTwo
          rationalZeroJetTwo = targetTwo t) :
    lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' ell' m' rationalZeroValueTwo
          rationalZeroJetTwo ∈ firstOrderEnvelopeTwoSpace := by
  rw [htarget]
  exact ⟨t,
    rationalZero_shadow_targetCoeff_mem a b a' b' ell m ell' m' t
      hcubic htarget,
    rfl⟩

end
end N5
end UnrestrictedBooleanMul
