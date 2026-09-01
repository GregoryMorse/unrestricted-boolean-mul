import UnrestrictedBooleanMul.N5.EnvelopeKernel
import UnrestrictedBooleanMul.N5.MissingCosetQuadratic

/-!
# Cubic recovery of an external quadratic shadow

This module isolates the basis-free linear-algebra step in the proof of
manuscript Lemma 11.2.  If two independent quadratic factor directions are
supported away from a set of external coordinates, equality of their cubic
products recovers both external linear coefficient vectors.  Their exterior
quadratic shadows therefore agree on every pair of external coordinates.

The argument uses the cubic equation itself and linear independence; it does
not enumerate factor presentations.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The two quadratic directions of an ordered factor plane. -/
def quadraticPlaneDirections (q c : TwoForm) : Fin 2 → TwoForm := ![c, q]

/-- The squarefree cubic part contributed by the linear and quadratic parts
of `(ell + q) * (m + c)`.  Boolean contractions occur in degree two and hence
do not enter this expression. -/
def factorPlaneCubic (ell m : LinearForm) (q c : TwoForm) :
    AmbientThreeForm :=
  ambientVectorWedgeTwo ell c + ambientVectorWedgeTwo m q

/-- A quadratic form has no coefficient involving the coordinate `i`. -/
def QuadraticSupportAvoids (q : TwoForm) (i : Fin 10) : Prop :=
  ∀ j, ambientTwoCoeff q i j = 0

/-- Pairing of two coefficient vectors in the fixed ambient basis.  The
second argument can be viewed as a vector specifying an arbitrary changed
coordinate. -/
def ambientLinearPair (x u : LinearForm) : F₂ :=
  ∑ i : Fin 10, u i * x i

/-- A vector lies in the radical of an ambient alternating two-form. -/
def AmbientRadicalVector (q : TwoForm) (u : LinearForm) : Prop :=
  ∀ j, ∑ i : Fin 10, u i * ambientTwoCoeff q i j = 0

/-- Contract only the first slot of a cubic coefficient form.  Unlike a full
three-fold tensor sum, this retains the alternating cubic data in
characteristic two. -/
def ambientCubicFirstContraction (u : LinearForm) (h : AmbientThreeForm) :
    Fin 10 → Fin 10 → F₂ :=
  fun j k => ∑ i : Fin 10, u i * h i j k

/-- Exterior quadratic shadow evaluated on two arbitrary changed
coordinates. -/
def externalShadowValue (ell m u v : LinearForm) : F₂ :=
  ambientLinearPair ell u * ambientLinearPair m v +
    ambientLinearPair ell v * ambientLinearPair m u

private theorem sum_mul_mul_right
    (x y : LinearForm) (a : F₂) :
    (∑ i : Fin 10, x i * (y i * a)) =
      (∑ i : Fin 10, x i * y i) * a := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sum_mul_mul_left
    (x y : LinearForm) (a : F₂) :
    (∑ i : Fin 10, x i * (a * y i)) =
      a * ∑ i : Fin 10, x i * y i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Contracting the cubic factor-plane equation along a common radical
vector leaves precisely the two scalar coefficients of the quadratic plane.
This is the coordinate-free form used for local evaluation bases. -/
theorem ambientCubicFirstContraction_factorPlaneCubic
    (ell m : LinearForm) (q c : TwoForm) (u : LinearForm)
    (hqu : AmbientRadicalVector q u)
    (hcu : AmbientRadicalVector c u) :
    ambientCubicFirstContraction u (factorPlaneCubic ell m q c) =
      fun j k =>
        ambientLinearPair ell u * ambientTwoCoeff c j k +
          ambientLinearPair m u * ambientTwoCoeff q j k := by
  funext j k
  simp only [ambientCubicFirstContraction, factorPlaneCubic,
    Pi.add_apply, ambientVectorWedgeTwo, N4.vectorWedgeTwoN, mul_add]
  repeat' rw [Finset.sum_add_distrib]
  rw [sum_mul_mul_right, sum_mul_mul_left, sum_mul_mul_left,
    sum_mul_mul_right, sum_mul_mul_left, sum_mul_mul_left,
    hcu k, hcu j, hqu k, hqu j]
  simp [ambientLinearPair]

/-- Coefficients of two independent quadratic directions are unique. -/
theorem quadraticPlaneDirections_coefficients
    (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (a b : F₂) (hzero : a • c + b • q = 0) :
    a = 0 ∧ b = 0 := by
  let f : Fin 2 → F₂ := ![a, b]
  have hsum : ∑ k : Fin 2,
      f k • quadraticPlaneDirections q c k = 0 := by
    simpa [f, quadraticPlaneDirections, Fin.sum_univ_succ] using hzero
  have hf := Fintype.linearIndependent_iff.mp hind f hsum
  exact ⟨by simpa [f] using hf 0, by simpa [f] using hf 1⟩

/-- Cubic equality for an independent factor plane recovers the two linear
coefficients at every coordinate avoided by both quadratic directions. -/
theorem independentPlane_cubic_recovers_external_coefficients
    (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q c)
    (i : Fin 10) (hqi : QuadraticSupportAvoids q i)
    (hci : QuadraticSupportAvoids c i) :
    ell i = ell' i ∧ m i = m' i := by
  have hform : (ell i + ell' i) • c + (m i + m' i) • q = 0 := by
    apply ambientTwoCoeff_injective
    intro j k
    rw [ambientTwoCoeff_add, ambientTwoCoeff_smul,
      ambientTwoCoeff_smul]
    rw [show ambientTwoCoeff (0 : TwoForm) j k = 0 by
      by_cases hjk : j = k <;> simp [ambientTwoCoeff, hjk]]
    have hijk := congrFun (congrFun (congrFun hcubic i) j) k
    simp only [factorPlaneCubic, Pi.add_apply, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN] at hijk
    rw [hci j, hci k, hqi j, hqi k] at hijk
    simp only [mul_zero, add_zero] at hijk
    calc
      (ell i + ell' i) * ambientTwoCoeff c j k +
          (m i + m' i) * ambientTwoCoeff q j k =
          (ell i * ambientTwoCoeff c j k +
            m i * ambientTwoCoeff q j k) +
          (ell' i * ambientTwoCoeff c j k +
            m' i * ambientTwoCoeff q j k) := by ring
      _ = (ell' i * ambientTwoCoeff c j k +
            m' i * ambientTwoCoeff q j k) +
          (ell' i * ambientTwoCoeff c j k +
            m' i * ambientTwoCoeff q j k) := by rw [hijk]
      _ = 0 := CharTwo.add_self_eq_zero _
  rcases quadraticPlaneDirections_coefficients q c hind
      (ell i + ell' i) (m i + m' i) hform with ⟨hell, hm⟩
  constructor
  · rw [← CharTwo.sub_eq_add] at hell
    exact sub_eq_zero.mp hell
  · rw [← CharTwo.sub_eq_add] at hm
    exact sub_eq_zero.mp hm

/-- Basis-free version of external coefficient recovery.  Any vector in the
common radical of the two independent quadratic directions may be used as an
external changed coordinate. -/
theorem independentPlane_cubic_recovers_radical_pairings
    (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q c)
    (u : LinearForm) (hqu : AmbientRadicalVector q u)
    (hcu : AmbientRadicalVector c u) :
    ambientLinearPair ell u = ambientLinearPair ell' u ∧
      ambientLinearPair m u = ambientLinearPair m' u := by
  have hcontract := congrArg (ambientCubicFirstContraction u) hcubic
  rw [ambientCubicFirstContraction_factorPlaneCubic ell m q c u hqu hcu,
    ambientCubicFirstContraction_factorPlaneCubic ell' m' q c u hqu hcu]
      at hcontract
  have hform :
      (ambientLinearPair ell u + ambientLinearPair ell' u) • c +
        (ambientLinearPair m u + ambientLinearPair m' u) • q = 0 := by
    apply ambientTwoCoeff_injective
    intro j k
    rw [ambientTwoCoeff_add, ambientTwoCoeff_smul,
      ambientTwoCoeff_smul]
    rw [show ambientTwoCoeff (0 : TwoForm) j k = 0 by
      by_cases hjk : j = k <;> simp [ambientTwoCoeff, hjk]]
    have hjk := congrFun (congrFun hcontract j) k
    calc
      (ambientLinearPair ell u + ambientLinearPair ell' u) *
            ambientTwoCoeff c j k +
          (ambientLinearPair m u + ambientLinearPair m' u) *
            ambientTwoCoeff q j k =
          (ambientLinearPair ell u * ambientTwoCoeff c j k +
            ambientLinearPair m u * ambientTwoCoeff q j k) +
          (ambientLinearPair ell' u * ambientTwoCoeff c j k +
            ambientLinearPair m' u * ambientTwoCoeff q j k) := by ring
      _ = (ambientLinearPair ell' u * ambientTwoCoeff c j k +
            ambientLinearPair m' u * ambientTwoCoeff q j k) +
          (ambientLinearPair ell' u * ambientTwoCoeff c j k +
            ambientLinearPair m' u * ambientTwoCoeff q j k) := by rw [hjk]
      _ = 0 := CharTwo.add_self_eq_zero _
  rcases quadraticPlaneDirections_coefficients q c hind
      (ambientLinearPair ell u + ambientLinearPair ell' u)
      (ambientLinearPair m u + ambientLinearPair m' u) hform with
    ⟨hell, hm⟩
  constructor
  · rw [← CharTwo.sub_eq_add] at hell
    exact sub_eq_zero.mp hell
  · rw [← CharTwo.sub_eq_add] at hm
    exact sub_eq_zero.mp hm

/-- Cubic equality recovers the exterior quadratic shadow on every pair of
vectors in the common radical.  This packages the `Λ² E` argument without
choosing coordinate axes for the local evaluation basis. -/
theorem independentPlane_cubic_recovers_radical_shadow
    (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q c)
    (u v : LinearForm)
    (hqu : AmbientRadicalVector q u) (hcu : AmbientRadicalVector c u)
    (hqv : AmbientRadicalVector q v) (hcv : AmbientRadicalVector c v) :
    externalShadowValue ell m u v = externalShadowValue ell' m' u v := by
  rcases independentPlane_cubic_recovers_radical_pairings
      q c hind ell m ell' m' hcubic u hqu hcu with ⟨hellu, hmu⟩
  rcases independentPlane_cubic_recovers_radical_pairings
      q c hind ell m ell' m' hcubic v hqv hcv with ⟨hellv, hmv⟩
  simp only [externalShadowValue]
  rw [hellu, hmu, hellv, hmv]

/-- The `Λ² E` consequence of cubic recovery: the quadratic shadow made
from the two linear factors is identical on every pair of external
coordinates.  This is the algebraic rank-two shadow step in manuscript
Lemma 11.2. -/
theorem independentPlane_cubic_recovers_external_shadow
    (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q c)
    (i j : Fin 10) (hij : i ≠ j)
    (hqi : QuadraticSupportAvoids q i)
    (hci : QuadraticSupportAvoids c i)
    (hqj : QuadraticSupportAvoids q j)
    (hcj : QuadraticSupportAvoids c j) :
    squarefreeWedge ell m (quadraticPair i j hij) =
      squarefreeWedge ell' m' (quadraticPair i j hij) := by
  rcases independentPlane_cubic_recovers_external_coefficients
      q c hind ell m ell' m' hcubic i hqi hci with ⟨helli, hmi⟩
  rcases independentPlane_cubic_recovers_external_coefficients
      q c hind ell m ell' m' hcubic j hqj hcj with ⟨hellj, hmj⟩
  simp only [squarefreeWedge_pair]
  rw [helli, hmi, hellj, hmj]

/-- For one nonzero quadratic direction, equality of the two cubic
contractions recovers the external linear coefficients.  Unlike the
independent-plane result, the common external coefficient may be nonzero. -/
theorem singleDirection_cubic_recovers_external_coefficient
    (q : TwoForm) (hq : q ≠ 0) (ell m : LinearForm)
    (hcubic : ambientVectorWedgeTwo ell q =
      ambientVectorWedgeTwo m q)
    (i : Fin 10) (hqi : QuadraticSupportAvoids q i) :
    ell i = m i := by
  have hex : ∃ s : QuadraticIndex 10, q s ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hq (funext hnone)
  rcases hex with ⟨s, hs⟩
  rcases QuadraticIndex.exists_pair s with ⟨j, k, hjk, rfl⟩
  have hqjk : ambientTwoCoeff q j k = 1 := by
    have hne : ambientTwoCoeff q j k ≠ 0 := by
      simpa [ambientTwoCoeff, hjk] using hs
    exact (f2_eq_zero_or_one _).resolve_left hne
  have hijk := congrFun (congrFun (congrFun hcubic i) j) k
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN] at hijk
  rw [hqi j, hqi k, hqjk] at hijk
  simpa using hijk

/-- Basis-free rank-one recovery on a radical vector. -/
theorem singleDirection_cubic_recovers_radical_pairing
    (q : TwoForm) (hq : q ≠ 0) (ell m : LinearForm)
    (hcubic : ambientVectorWedgeTwo ell q =
      ambientVectorWedgeTwo m q)
    (u : LinearForm) (hqu : AmbientRadicalVector q u) :
    ambientLinearPair ell u = ambientLinearPair m u := by
  have hleft : ambientCubicFirstContraction u
        (ambientVectorWedgeTwo ell q) =
      fun j k => ambientLinearPair ell u * ambientTwoCoeff q j k := by
    funext j k
    simp only [ambientCubicFirstContraction, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, mul_add]
    repeat' rw [Finset.sum_add_distrib]
    rw [sum_mul_mul_right, sum_mul_mul_left, sum_mul_mul_left,
      hqu k, hqu j]
    simp [ambientLinearPair]
  have hright : ambientCubicFirstContraction u
        (ambientVectorWedgeTwo m q) =
      fun j k => ambientLinearPair m u * ambientTwoCoeff q j k := by
    funext j k
    simp only [ambientCubicFirstContraction, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, mul_add]
    repeat' rw [Finset.sum_add_distrib]
    rw [sum_mul_mul_right, sum_mul_mul_left, sum_mul_mul_left,
      hqu k, hqu j]
    simp [ambientLinearPair]
  have hcontract := congrArg (ambientCubicFirstContraction u) hcubic
  rw [hleft, hright] at hcontract
  have hex : ∃ s : QuadraticIndex 10, q s ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hq (funext hnone)
  rcases hex with ⟨s, hs⟩
  rcases QuadraticIndex.exists_pair s with ⟨j, k, hjk, rfl⟩
  have hqjk : ambientTwoCoeff q j k = 1 := by
    have hne : ambientTwoCoeff q j k ≠ 0 := by
      simpa [ambientTwoCoeff, hjk] using hs
    exact (f2_eq_zero_or_one _).resolve_left hne
  have hjkEq := congrFun (congrFun hcontract j) k
  simpa [hqjk] using hjkEq

/-- Rank-one radical shadow vanishing in an arbitrary local evaluation
basis.  The two recovered external coefficient vectors can coincide
nontrivially, but their exterior shadow is zero. -/
theorem singleDirection_cubic_forces_radical_shadow_zero
    (q : TwoForm) (hq : q ≠ 0) (ell m : LinearForm)
    (hcubic : ambientVectorWedgeTwo ell q =
      ambientVectorWedgeTwo m q)
    (u v : LinearForm)
    (hqu : AmbientRadicalVector q u)
    (hqv : AmbientRadicalVector q v) :
    externalShadowValue ell m u v = 0 := by
  have hu := singleDirection_cubic_recovers_radical_pairing
    q hq ell m hcubic u hqu
  have hv := singleDirection_cubic_recovers_radical_pairing
    q hq ell m hcubic v hqv
  simp only [externalShadowValue]
  rw [hu, hv]
  simp [mul_comm]

/-- Rank-one companion to the independent shadow theorem.  Equal cubic
contractions may leave one common nonzero external vector, but the exterior
quadratic shadow of two such vectors vanishes on `Λ² E`. -/
theorem singleDirection_cubic_forces_external_shadow_zero
    (q : TwoForm) (hq : q ≠ 0) (ell m : LinearForm)
    (hcubic : ambientVectorWedgeTwo ell q =
      ambientVectorWedgeTwo m q)
    (i j : Fin 10) (hij : i ≠ j)
    (hqi : QuadraticSupportAvoids q i)
    (hqj : QuadraticSupportAvoids q j) :
    squarefreeWedge ell m (quadraticPair i j hij) = 0 := by
  have hi := singleDirection_cubic_recovers_external_coefficient
    q hq ell m hcubic i hqi
  have hj := singleDirection_cubic_recovers_external_coefficient
    q hq ell m hcubic j hqj
  simp only [squarefreeWedge_pair]
  rw [hi, hj]
  simp [mul_comm]

end
end N5
end UnrestrictedBooleanMul
