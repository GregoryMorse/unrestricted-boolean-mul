import UnrestrictedBooleanMul.N5.LowProductSemantic
import UnrestrictedBooleanMul.N5.SecantPfaffian

/-!
# Cubic ANF coordinates for ten-variable low products

This module identifies the literal cubic coefficients of a product of a
linear ANF and a pure quadratic ANF with the ambient exterior expression
used by the N5 envelope calculations.  Together with the exact high quotient
in `N5.LowProductSemantic`, it is the normalization bridge that keeps the
quadratic--quadratic cubic overlap explicit.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def anfThreeProjectionTen : ANF 10 →ₗ[F₂] AmbientThreeForm where
  toFun p i j k :=
    if ({i, j, k} : Finset (Fin 10)).card = 3 then
      p.coeff ⟨{i, j, k}⟩ else 0
  map_add' p q := by
    funext i j k
    by_cases h : ({i, j, k} : Finset (Fin 10)).card = 3 <;> simp [h]
  map_smul' a p := by
    funext i j k
    by_cases h : ({i, j, k} : Finset (Fin 10)).card = 3 <;> simp [h]

def monomialThreeTen (s : Finset (Fin 10)) : AmbientThreeForm :=
  fun i j k =>
    if ({i, j, k} : Finset (Fin 10)).card = 3 then
      if s = {i, j, k} then 1 else 0
    else 0

theorem anfThreeProjectionTen_monomial (s : Finset (Fin 10)) :
    anfThreeProjectionTen (monomial s) = monomialThreeTen s := by
  funext i j k
  by_cases hcard : ({i, j, k} : Finset (Fin 10)).card = 3 <;>
    simp [anfThreeProjectionTen, monomialThreeTen, hcard, coeff_monomial]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
private theorem anfThreeProjectionTen_three_X (r a b : Fin 10) :
    anfThreeProjectionTen (X r * (X a * X b)) =
      ambientVectorWedgeTwo (coordinateLinearTen r)
        (squarefreeWedge (coordinateLinearTen a) (coordinateLinearTen b)) := by
  rw [show X r * (X a * X b) = monomial {r, a, b} by
    rw [X, X, X, monomial_mul, monomial_mul]
    congr 1]
  rw [anfThreeProjectionTen_monomial]
  funext i j k
  simp only [monomialThreeTen, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, ambientTwoCoeff_squarefreeWedge,
    coordinateLinearTen]
  by_cases hcard : ({i, j, k} : Finset (Fin 10)).card = 3
  · have hij : i ≠ j := by
      intro hij
      subst j
      have hle := Finset.card_le_two (a := i) (b := k)
      have hcard' : ({i, k} : Finset (Fin 10)).card = 3 := by
        simpa using hcard
      omega
    have hik : i ≠ k := by
      intro hik
      subst k
      have hle := Finset.card_le_two (a := i) (b := j)
      have hcard' : ({i, j} : Finset (Fin 10)).card = 3 := by
        simpa [Finset.pair_comm] using hcard
      omega
    have hjk : j ≠ k := by
      intro hjk
      subst k
      have hle := Finset.card_le_two (a := i) (b := j)
      have hcard' : ({i, j} : Finset (Fin 10)).card = 3 := by
        simpa using hcard
      omega
    rw [if_pos hcard]
    by_cases hset : ({r, a, b} : Finset (Fin 10)) = {i, j, k}
    · rw [if_pos hset]
      have hrab : ({r, a, b} : Finset (Fin 10)).card = 3 := by
        rw [hset]
        exact hcard
      have hra : r ≠ a := by
        intro h
        subst a
        have hcard' : ({r, b} : Finset (Fin 10)).card = 3 := by
          simpa using hrab
        have hle := Finset.card_le_two (a := r) (b := b)
        omega
      have hrb : r ≠ b := by
        intro h
        subst b
        have hcard' : ({r, a} : Finset (Fin 10)).card = 3 := by
          simpa [Finset.pair_comm] using hrab
        have hle := Finset.card_le_two (a := r) (b := a)
        omega
      have hab : a ≠ b := by
        intro h
        subst b
        have hcard' : ({r, a} : Finset (Fin 10)).card = 3 := by
          simpa using hrab
        have hle := Finset.card_le_two (a := r) (b := a)
        omega
      have hr : r = i ∨ r = j ∨ r = k := by
        have hrmem : r ∈ ({i, j, k} : Finset (Fin 10)) := by
          rw [← hset]
          simp
        simpa using hrmem
      have ha : a = i ∨ a = j ∨ a = k := by
        have hamem : a ∈ ({i, j, k} : Finset (Fin 10)) := by
          rw [← hset]
          simp
        simpa using hamem
      have hb : b = i ∨ b = j ∨ b = k := by
        have hbmem : b ∈ ({i, j, k} : Finset (Fin 10)) := by
          rw [← hset]
          simp
        simpa using hbmem
      rcases hr with rfl | rfl | rfl <;>
        rcases ha with rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl
      all_goals
        clear hset hcard hrab
        simp_all [N3Certificate.two_eq_zero_f2]
    · rw [if_neg hset]
      by_cases hri : r = i
      · subst r
        simp only [if_pos rfl, if_neg hij.symm, if_neg hik.symm,
          one_mul, zero_mul, zero_add, add_zero]
        split_ifs <;>
          simp_all [Finset.ext_iff, or_comm, or_left_comm, or_assoc,
            N3Certificate.two_eq_zero_f2]
      by_cases hrj : r = j
      · subst r
        simp only [if_neg hij, if_pos rfl, if_neg hjk.symm,
          one_mul, zero_mul, zero_add, add_zero]
        split_ifs <;>
          simp_all [Finset.ext_iff, or_comm, or_left_comm, or_assoc,
            N3Certificate.two_eq_zero_f2]
      by_cases hrk : r = k
      · subst r
        simp only [if_neg hik, if_neg hjk, if_pos rfl,
          one_mul, zero_mul, zero_add, add_zero]
        split_ifs <;>
          simp_all [Finset.ext_iff, or_comm, or_left_comm, or_assoc,
            N3Certificate.two_eq_zero_f2]
      · simp [hri, hrj, hrk, Ne.symm hri, Ne.symm hrj, Ne.symm hrk]
  · rw [if_neg hcard]
    by_cases hij : i = j
    · subst j
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    by_cases hik : i = k
    · subst k
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    by_cases hjk : j = k
    · subst k
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · exact False.elim (hcard (by simp [hij, hik, hjk]))

def ambientVectorWedgeTwoBilinear :
    LinearForm →ₗ[F₂] TwoForm →ₗ[F₂] AmbientThreeForm where
  toFun ell := {
    toFun := fun q => ambientVectorWedgeTwo ell q
    map_add' := by
      intro q c
      funext i j k
      simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
        ambientTwoCoeff_add, Pi.add_apply]
      ring
    map_smul' := by
      intro a q
      funext i j k
      simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
        ambientTwoCoeff_smul, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring }
  map_add' := by
    intro ell m
    apply LinearMap.ext
    intro q
    funext i j k
    change N4.vectorWedgeTwoN (ell + m) (ambientTwoCoeff q) i j k =
      N4.vectorWedgeTwoN ell (ambientTwoCoeff q) i j k +
        N4.vectorWedgeTwoN m (ambientTwoCoeff q) i j k
    simp only [N4.vectorWedgeTwoN, Pi.add_apply]
    ring
  map_smul' := by
    intro a ell
    apply LinearMap.ext
    intro q
    funext i j k
    change N4.vectorWedgeTwoN (a • ell) (ambientTwoCoeff q) i j k =
      a • N4.vectorWedgeTwoN ell (ambientTwoCoeff q) i j k
    simp only [N4.vectorWedgeTwoN, Pi.smul_apply, smul_eq_mul]
    ring

theorem linearForm_eq_sum_coordinates (ell : LinearForm) :
    ell = ∑ i : Fin 10, ell i • coordinateLinearTen i := by
  classical
  funext j
  simp [coordinateLinearTen]

theorem twoForm_eq_sum_basis (q : TwoForm) :
    q = ∑ s : QuadraticIndex 10,
      q s • (Pi.basisFun F₂ (QuadraticIndex 10)) s := by
  classical
  funext t
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  change q t = ∑ s : QuadraticIndex 10,
    q s * (Pi.basisFun F₂ (QuadraticIndex 10)) s t
  rw [Fintype.sum_eq_single t]
  · simp [Pi.basisFun]
  · intro s hst
    simp [Pi.basisFun, hst]

theorem quadraticBasisPair_eq_wedge
    (i j : Fin 10) (hij : i ≠ j) :
    (Pi.basisFun F₂ (QuadraticIndex 10)) (quadraticPair i j hij) =
      squarefreeWedge (coordinateLinearTen i) (coordinateLinearTen j) := by
  have hi : linearProjection 10 (X i) = coordinateLinearTen i := by
    rw [← linearANFTen_coordinate i, linearProjection_linearANFTen]
  have hj : linearProjection 10 (X j) = coordinateLinearTen j := by
    rw [← linearANFTen_coordinate j, linearProjection_linearANFTen]
  calc
    (Pi.basisFun F₂ (QuadraticIndex 10)) (quadraticPair i j hij) =
        quadraticProjection 10
          (quadraticANFOfForm
            ((Pi.basisFun F₂ (QuadraticIndex 10))
              (quadraticPair i j hij))) := by
          rw [quadraticProjection_quadraticANFOfForm]
    _ = quadraticProjection 10 (X i * X j) := by
      rw [quadraticANFOfForm_basis]
      simp [quadraticPair, X]
    _ = squarefreeWedge (coordinateLinearTen i)
          (coordinateLinearTen j) := by
      simpa [hi, hj] using quadraticProjection_X_mul_X' i j

private theorem anfThreeProjectionTen_X_mul_quadraticMonomial
    (r : Fin 10) (s : QuadraticIndex 10) :
    anfThreeProjectionTen
        (X r * monomial s.1) =
      ambientVectorWedgeTwo (coordinateLinearTen r)
        ((Pi.basisFun F₂ (QuadraticIndex 10)) s) := by
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  change anfThreeProjectionTen (X r * monomial ({i, j} : Finset (Fin 10))) = _
  have hmonomial : monomial ({i, j} : Finset (Fin 10)) = X i * X j := by
    simp [X]
  rw [hmonomial, anfThreeProjectionTen_three_X,
    quadraticBasisPair_eq_wedge]

/-- Literal cubic coefficients of a linear--quadratic Boolean product are
the ambient vector--two-form wedge used by the envelope modules. -/
theorem anfThreeProjectionTen_linear_mul_quadratic
    (ell : LinearForm) (q : TwoForm) :
    anfThreeProjectionTen (linearANFTen ell * quadraticANFOfForm q) =
      ambientVectorWedgeTwo ell q := by
  classical
  let ellSum := ∑ i : Fin 10, ell i • coordinateLinearTen i
  let qSum := ∑ s : QuadraticIndex 10,
    q s • (Pi.basisFun F₂ (QuadraticIndex 10)) s
  have hell : ellSum = ell := (linearForm_eq_sum_coordinates ell).symm
  have hq : qSum = q := (twoForm_eq_sum_basis q).symm
  calc
    anfThreeProjectionTen (linearANFTen ell * quadraticANFOfForm q) =
        ∑ s : QuadraticIndex 10, ∑ i : Fin 10,
          (q s * ell i) •
            anfThreeProjectionTen (X i * monomial s.1) := by
      rw [linearANFTen, quadraticANFOfForm]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm, map_sum, map_smul, Finset.smul_sum, smul_smul]
    _ = ambientVectorWedgeTwoBilinear ellSum qSum := by
      simp only [ellSum, qSum, map_sum, map_smul,
        anfThreeProjectionTen_X_mul_quadraticMonomial]
      apply Finset.sum_congr rfl
      intro s _hs
      change
        (∑ i : Fin 10, (q s * ell i) •
          ambientVectorWedgeTwo (coordinateLinearTen i)
            ((Pi.basisFun F₂ (QuadraticIndex 10)) s)) =
        q s • ∑ i : Fin 10,
          (ell i • ambientVectorWedgeTwoBilinear (coordinateLinearTen i))
            ((Pi.basisFun F₂ (QuadraticIndex 10)) s)
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [smul_smul, ambientVectorWedgeTwoBilinear,
        mul_comm]
    _ = ambientVectorWedgeTwo ell q := by
      rw [hell, hq]
      rfl

theorem anfThreeProjectionTen_quadratic_mul_linear
    (q : TwoForm) (ell : LinearForm) :
    anfThreeProjectionTen (quadraticANFOfForm q * linearANFTen ell) =
      ambientVectorWedgeTwo ell q := by
  rw [mul_comm]
  exact anfThreeProjectionTen_linear_mul_quadratic ell q

/-- Cubic overlap created when two pure quadratic Boolean ANFs share one
input variable.  This term is absent from the exterior quartic tensor and
must be retained at the semantic boundary. -/
def quadraticOverlapCubic (q c : TwoForm) : AmbientThreeForm :=
  anfThreeProjectionTen (quadraticANFOfForm q * quadraticANFOfForm c)

/-- The complete literal cubic part of a low--low product. -/
def exactLowProductCubic
    (ell m : LinearForm) (q c : TwoForm) : AmbientThreeForm :=
  quadraticOverlapCubic q c + factorPlaneCubic ell m q c

theorem anfThreeProjectionTen_eq_zero_of_degreeLE_two
    {p : ANF 10} (hp : N4.DegreeLE 2 p) :
    anfThreeProjectionTen p = 0 := by
  funext i j k
  change (if ({i, j, k} : Finset (Fin 10)).card = 3
    then p.coeff ⟨{i, j, k}⟩ else 0) = 0
  by_cases hcard : ({i, j, k} : Finset (Fin 10)).card = 3
  · rw [if_pos hcard]
    apply hp ⟨{i, j, k}⟩
    change 2 < ({i, j, k} : Finset (Fin 10)).card
    omega
  · rw [if_neg hcard]

theorem anfThreeProjectionTen_eq_zero_of_quadratic
    {p : ANF 10} (hp : p ∈ N4.quadraticANFSpace 10) :
    anfThreeProjectionTen p = 0 :=
  anfThreeProjectionTen_eq_zero_of_degreeLE_two hp

@[simp] theorem anfThreeProjectionTen_quadraticCoordinateANF
    (a : F₂) (ell : LinearForm) (q : TwoForm) :
    anfThreeProjectionTen (quadraticCoordinateANF a ell q) = 0 :=
  anfThreeProjectionTen_eq_zero_of_quadratic
    (quadraticCoordinateANF_mem_quadraticANFSpace a ell q)

theorem linearANFTen_degreeLE_one (ell : LinearForm) :
    N4.DegreeLE 1 (linearANFTen ell) := by
  intro s hs
  exact N4.affine_coeff_zero_of_two_le
    (linearANFTen_mem_affine ell) s (by omega)

@[simp] theorem anfThreeProjectionTen_linear_mul_linear
    (ell m : LinearForm) :
    anfThreeProjectionTen (linearANFTen ell * linearANFTen m) = 0 :=
  anfThreeProjectionTen_eq_zero_of_degreeLE_two
    ((linearANFTen_degreeLE_one ell).mul
      (linearANFTen_degreeLE_one m))

@[simp] theorem anfThreeProjectionTen_one :
    anfThreeProjectionTen (1 : ANF 10) = 0 := by
  apply anfThreeProjectionTen_eq_zero_of_degreeLE_two
  exact (N4.affine_le_quadraticANFSpace (one_mem_affine 10))

@[simp] theorem anfThreeProjectionTen_linearANFTen
    (ell : LinearForm) :
    anfThreeProjectionTen (linearANFTen ell) = 0 :=
  anfThreeProjectionTen_eq_zero_of_quadratic
    (N4.affine_le_quadraticANFSpace (linearANFTen_mem_affine ell))

@[simp] theorem anfThreeProjectionTen_quadraticANFOfForm
    (q : TwoForm) :
    anfThreeProjectionTen (quadraticANFOfForm q) = 0 :=
  anfThreeProjectionTen_eq_zero_of_quadratic
    (pureQuadraticANFSpace_le_quadraticANFSpace ⟨q, rfl⟩)

/-- Exact cubic projection formula, including quadratic--quadratic overlap. -/
theorem anfThreeProjectionTen_quadraticCoordinateANF_mul
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    anfThreeProjectionTen
        (quadraticCoordinateANF a ell q *
          quadraticCoordinateANF b m c) =
      exactLowProductCubic ell m q c := by
  simp only [quadraticCoordinateANF, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, map_add, map_smul,
    anfThreeProjectionTen_one, anfThreeProjectionTen_linearANFTen,
    anfThreeProjectionTen_quadraticANFOfForm,
    anfThreeProjectionTen_linear_mul_linear,
    anfThreeProjectionTen_linear_mul_quadratic,
    anfThreeProjectionTen_quadratic_mul_linear, smul_zero, zero_add]
  rw [exactLowProductCubic, quadraticOverlapCubic, factorPlaneCubic]
  module

@[simp] theorem quadraticOverlapCubic_self (q : TwoForm) :
    quadraticOverlapCubic q q = 0 := by
  rw [quadraticOverlapCubic, N4.anf_mul_self]
  exact anfThreeProjectionTen_quadraticANFOfForm q

/-- Equality in the literal high quotient forces equality of the complete
cubic parts, including overlap terms. -/
theorem exactLowProductCubic_eq_of_highClass_eq
    (ell m ell' m' : LinearForm) (q c q' c' : TwoForm)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c') :
    exactLowProductCubic ell m q c =
      exactLowProductCubic ell' m' q' c' := by
  let p := quadraticCoordinateANF 0 ell q *
    quadraticCoordinateANF 0 m c
  let p' := quadraticCoordinateANF 0 ell' q' *
    quadraticCoordinateANF 0 m' c'
  have hquot : highProjectionTen (p + p') = 0 := by
    rw [map_add]
    change lowProductHighClass ell m q c +
      lowProductHighClass ell' m' q' c' = 0
    rw [hhigh]
    calc
      lowProductHighClass ell' m' q' c' +
          lowProductHighClass ell' m' q' c' =
          ((1 : F₂) + 1) • lowProductHighClass ell' m' q' c' := by
            rw [add_smul, one_smul]
      _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  have hquad : p + p' ∈ N4.quadraticANFSpace 10 :=
    (highProjectionTen_eq_zero_iff (p + p')).1 hquot
  have hcubic := anfThreeProjectionTen_eq_zero_of_quadratic hquad
  rw [map_add] at hcubic
  change anfThreeProjectionTen p + anfThreeProjectionTen p' = 0 at hcubic
  rw [anfThreeProjectionTen_quadraticCoordinateANF_mul,
    anfThreeProjectionTen_quadraticCoordinateANF_mul] at hcubic
  have hself (x : AmbientThreeForm) : x + x = 0 := by
    calc
      x + x = ((1 : F₂) + 1) • x := by rw [add_smul, one_smul]
      _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  calc
    exactLowProductCubic ell m q c =
        exactLowProductCubic ell m q c + 0 := by rw [add_zero]
    _ = exactLowProductCubic ell m q c +
        (exactLowProductCubic ell' m' q' c' +
          exactLowProductCubic ell' m' q' c') := by
            rw [hself]
    _ = (exactLowProductCubic ell m q c +
          exactLowProductCubic ell' m' q' c') +
        exactLowProductCubic ell' m' q' c' := by ac_rfl
    _ = exactLowProductCubic ell' m' q' c' := by rw [hcubic, zero_add]

/-- When the two products have the same quadratic factor directions, their
fixed overlap cancels and literal high equality gives precisely the cubic
equation expected by `envelope_shadow`. -/
theorem factorPlaneCubic_eq_of_samePlane_highClass_eq
    (ell m ell' m' : LinearForm) (q c : TwoForm)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q c) :
    factorPlaneCubic ell m q c = factorPlaneCubic ell' m' q c := by
  have h := exactLowProductCubic_eq_of_highClass_eq
    ell m ell' m' q c q c hhigh
  simp only [exactLowProductCubic] at h
  exact add_left_cancel h

end
end N5
end UnrestrictedBooleanMul
