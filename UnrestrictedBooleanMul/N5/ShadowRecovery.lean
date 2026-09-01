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
