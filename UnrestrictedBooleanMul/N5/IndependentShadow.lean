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

theorem rationalZeroValueTwo_eq_target :
    rationalZeroValueTwo = targetTwo rZeroCoeff := by
  rw [rationalZeroValueTwo, targetTwo_rZero]

theorem rationalZeroJetTwo_eq_target :
    rationalZeroJetTwo = targetTwo jZeroCoeff := by
  rw [rationalZeroJetTwo, targetTwo_eq_double_sum]
  simp [jZeroCoeff, hankelIndex, Fin.sum_univ_succ]

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
    x (bCoord 1) = 0 ∧
    x (bCoord 2) = 0 ∧
    x (bCoord 3) = 0 ∧
    x (bCoord 4) = 0 ∧
    y (aCoord 1) = x (aCoord 0) ∧
    y (aCoord 2) = 0 ∧
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
  exact ⟨hx1, hA2.1, hx6, hB2.1, hB3.1, hB4.1,
    hy1, hA2.2, hy6, hB2.2, hB3.2, hB4.2⟩

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
    ⟨hxA1, hxA2, hxB1, hxB2, hxB3, hxB4,
      hyA1, hyA2, hyB1, hyB2, hyB3, hyB4⟩
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
  have hsum : firstOrderMissingCoeff + u ∈
      firstOrderEnvelopeCoeffSpace :=
    rationalZero_shadow_targetCoeff_mem a b a' b' ell m ell' m'
      (firstOrderMissingCoeff + u) hcubic hmissing
  have htau : firstOrderMissingCoeff ∈ firstOrderEnvelopeCoeffSpace := by
    have := firstOrderEnvelopeCoeffSpace.sub_mem hsum hu
    simpa using this
  exact firstOrderMissingCoeff_not_mem htau

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
