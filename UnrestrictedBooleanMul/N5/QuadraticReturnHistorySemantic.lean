import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryModel
import UnrestrictedBooleanMul.N5.QuadraticReturnHistorySymbolic
import UnrestrictedBooleanMul.N5.CubicSemantic
import UnrestrictedBooleanMul.N5.ClosedPlaces
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Semantic bridge for the rational-return history certificate

This module identifies the named polynomial history parameters with the
literal ANF products used by the circuit proof.  It is intentionally built
one projection layer at a time so every generated constraint has an auditable
algebraic source.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The Boolean point supported on a prescribed subset of the ten input
coordinates. -/
def supportAssignmentTen (t : Finset (Fin 10)) : Fin 10 → F₂ :=
  fun i => if i ∈ t then 1 else 0

theorem prod_supportAssignmentTen (s t : Finset (Fin 10)) :
    ∏ i ∈ s, supportAssignmentTen t i = if s ⊆ t then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have ih' : (∏ i ∈ s, if i ∈ t then (1 : F₂) else 0) =
          if s ⊆ t then 1 else 0 := by
        simpa [supportAssignmentTen] using ih
      by_cases hit : i ∈ t <;>
        simp [his, hit, ih', supportAssignmentTen,
          Finset.insert_subset_iff]

@[simp] theorem eval_monomial_supportAssignmentTen
    (s t : Finset (Fin 10)) :
    eval (monomial s) (supportAssignmentTen t) =
      if s ⊆ t then 1 else 0 := by
  rw [eval_monomial, prod_supportAssignmentTen]

@[simp] theorem evalHom_X_supportAssignmentTen
    (i : Fin 10) (t : Finset (Fin 10)) :
    evalHom (supportAssignmentTen t) (X i) =
      if i ∈ t then 1 else 0 := by
  rw [← eval_eq_evalHom, eval_X]
  rfl

@[simp] theorem evalHom_X_ten (i : Fin 10) (x : Fin 10 → F₂) :
    evalHom x (X i) = x i := by
  rw [← eval_eq_evalHom, eval_X]

/-- Sum of all subset evaluations on a Boolean coordinate cube. -/
def cubeEvalMapTen (t : Finset (Fin 10)) : ANF 10 →ₗ[F₂] F₂ :=
  ∑ u ∈ t.powerset, (evalHom (supportAssignmentTen u)).toLinearMap

/-- Extraction of the coefficient supported on `t`. -/
def cubeCoeffMapTen (t : Finset (Fin 10)) : ANF 10 →ₗ[F₂] F₂ where
  toFun p := p.coeff ⟨t⟩
  map_add' p q := by simp
  map_smul' a p := by simp

/-- Möbius inversion on a Boolean subset cube; in characteristic two the
zeta transform is its own inverse. -/
theorem subset_cube_sum_f2 (s t : Finset (Fin 10)) :
    (∑ u ∈ t.powerset, if s ⊆ u then (1 : F₂) else 0) =
      if s = t then 1 else 0 := by
  classical
  by_cases hst : s ⊆ t
  · by_cases heq : s = t
    · subst s
      rw [Finset.sum_eq_single t]
      · simp
      · intro u hu hut
        have hut' : u ⊆ t := Finset.mem_powerset.mp hu
        have hnot : ¬t ⊆ u := fun htu =>
          hut (Finset.Subset.antisymm hut' htu)
        simp [hnot]
      · simp
    · have hss : s ⊂ t := hst.ssubset_of_ne heq
      obtain ⟨a, hat, has⟩ := Finset.exists_of_ssubset hss
      let t' := t.erase a
      have hat' : a ∉ t' := by simp [t']
      have ht : insert a t' = t := Finset.insert_erase hat
      have hst' : s ⊆ t' := by
        intro x hxs
        simp only [t', Finset.mem_erase]
        exact ⟨fun hxa => has (hxa ▸ hxs), hst hxs⟩
      rw [← ht, Finset.sum_powerset_insert hat']
      have hinsert (u : Finset (Fin 10)) (hu : u ⊆ t') :
          (s ⊆ insert a u) ↔ s ⊆ u := by
        constructor
        · intro hsu x hxs
          have hx := hsu hxs
          simp only [Finset.mem_insert] at hx
          rcases hx with hxa | hxu
          · exact (has (hxa ▸ hxs)).elim
          · exact hxu
        · exact fun hsu => hsu.trans (Finset.subset_insert a u)
      have hsums :
          (∑ u ∈ t'.powerset, if s ⊆ insert a u then (1 : F₂) else 0) =
            ∑ u ∈ t'.powerset, if s ⊆ u then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        have hi := hinsert u (Finset.mem_powerset.mp hu)
        by_cases hsu : s ⊆ u
        · simp [hsu, hi.mpr hsu]
        · have hnot : ¬s ⊆ insert a u := fun h => hsu (hi.mp h)
          simp [hsu, hnot]
      rw [hsums, CharTwo.add_self_eq_zero]
      have hneInsert : s ≠ insert a t' := fun h => heq (h.trans ht)
      simp [hneInsert]
  · have hnone (u : Finset (Fin 10)) (hu : u ∈ t.powerset) : ¬s ⊆ u := by
      intro hsu
      exact hst (hsu.trans (Finset.mem_powerset.mp hu))
    have hne : s ≠ t := fun h => hst (h ▸ Finset.Subset.rfl)
    rw [Finset.sum_eq_zero]
    · simp [hne]
    · intro u hu
      simp [hnone u hu]

theorem cubeEvalMapTen_single (t : Finset (Fin 10)) (s : Monomial 10)
    (c : F₂) :
    cubeEvalMapTen t (MonoidAlgebra.single s c) =
      c * (if s.vars = t then 1 else 0) := by
  rw [cubeEvalMapTen]
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  change (∑ u ∈ t.powerset,
      eval (MonoidAlgebra.single s c) (supportAssignmentTen u)) = _
  have hsingle : (MonoidAlgebra.single s c : ANF 10) =
      c • monomial s.vars := by
    apply MonoidAlgebra.coeff_injective
    ext v
    rw [show s = ⟨s.vars⟩ by cases s; rfl]
    simp [monomial]
  simp_rw [hsingle, eval_smul', eval_monomial_supportAssignmentTen]
  rw [← Finset.mul_sum, subset_cube_sum_f2]

/-- Coefficient extraction through a support-sized evaluation cube.  This
keeps the feedback checks exponential only in the selected degree (at most
five here), rather than in the ten-variable ambient space. -/
theorem cubeEvalMapTen_eq_cubeCoeffMapTen (t : Finset (Fin 10)) :
    cubeEvalMapTen t = cubeCoeffMapTen t := by
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext
  intro c
  change cubeEvalMapTen t (MonoidAlgebra.single s c) =
    cubeCoeffMapTen t (MonoidAlgebra.single s c)
  rw [cubeEvalMapTen_single]
  change c * (if s.vars = t then 1 else 0) =
    (Finsupp.single s c : Monomial 10 →₀ F₂) ⟨t⟩
  rw [Finsupp.single_apply]
  by_cases h : s.vars = t
  · rw [if_pos h, if_pos (Monomial.ext h), mul_one]
  · rw [if_neg h, if_neg (fun hs => h (congrArg Monomial.vars hs)), mul_zero]

/-- Coefficient extraction as a sum over the corresponding Boolean cube. -/
theorem coeff_eq_cube_eval_sum (q : ANF 10) (t : Finset (Fin 10)) :
    q.coeff ⟨t⟩ =
      ∑ u ∈ t.powerset, eval q (supportAssignmentTen u) := by
  have h := LinearMap.congr_fun (cubeEvalMapTen_eq_cubeCoeffMapTen t) q
  rw [cubeEvalMapTen, cubeCoeffMapTen] at h
  simp only [LinearMap.coe_sum, Finset.sum_apply] at h
  exact h.symm

/-- The `0x023` cubic coefficient as eight explicit Boolean evaluations. -/
theorem coeff_zero_one_five_eq_eval_sum (q : ANF 10) :
    q.coeff ⟨({0, 1, 5} : Finset (Fin 10))⟩ =
      eval q (supportAssignmentTen ∅) +
      eval q (supportAssignmentTen {0}) +
      eval q (supportAssignmentTen {1}) +
      eval q (supportAssignmentTen {0, 1}) +
      eval q (supportAssignmentTen {5}) +
      eval q (supportAssignmentTen {0, 5}) +
      eval q (supportAssignmentTen {1, 5}) +
      eval q (supportAssignmentTen {0, 1, 5}) := by
  have h := congrArg (fun L : ANF 10 →ₗ[F₂] F₂ => L q)
    (cubeEvalMapTen_eq_cubeCoeffMapTen
      ({0, 1, 5} : Finset (Fin 10)))
  rw [cubeEvalMapTen] at h
  simp only [LinearMap.coe_sum, Finset.sum_apply] at h
  change (∑ u ∈ ({0, 1, 5} : Finset (Fin 10)).powerset,
      eval q (supportAssignmentTen u)) =
        q.coeff ⟨({0, 1, 5} : Finset (Fin 10))⟩ at h
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by
    decide
  rw [hpowerset] at h
  simpa +decide [add_assoc] using h.symm

/-- The first high product in the canonical `(0,1)` factor-pair model. -/
def ZeroOneOffAxisHistoryParameters.firstProduct
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF 0 p.ell 0 *
    quadraticCoordinateANF 0 p.m (targetTwo rZeroCoeff)

/-- The equal-high comparison product, obtained by shifting both linear
parts without changing their quadratic parts. -/
def ZeroOneOffAxisHistoryParameters.shiftedProduct
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF 0 (p.ell + p.leftShift) 0 *
    quadraticCoordinateANF 0 (p.m + p.rightShift)
      (targetTwo rZeroCoeff)

/-- The quadratic return candidate is the sum of the two equal-high
products. -/
def ZeroOneOffAxisHistoryParameters.returned
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  p.firstProduct + p.shiftedProduct

/-- The eight-coordinate correction in the first-order target envelope. -/
def ZeroOneOffAxisHistoryParameters.correctionTwo
    (p : ZeroOneOffAxisHistoryParameters) : TwoForm :=
  ∑ i : Fin 8, p.correctionTarget i •
    targetTwo (returnHistoryCorrectionDirections i)

/-- The single target word encoded by the eight correction coordinates. -/
def ZeroOneOffAxisHistoryParameters.correctionCoeff
    (p : ZeroOneOffAxisHistoryParameters) : TargetCoeff :=
  ∑ i : Fin 8, p.correctionTarget i •
    returnHistoryCorrectionDirections i

theorem ZeroOneOffAxisHistoryParameters.correctionTwo_eq_targetTwo
    (p : ZeroOneOffAxisHistoryParameters) :
    p.correctionTwo = targetTwo p.correctionCoeff := by
  change (∑ i : Fin 8, p.correctionTarget i •
      targetTwoLinear (returnHistoryCorrectionDirections i)) =
    targetTwoLinear
      (∑ i : Fin 8, p.correctionTarget i •
        returnHistoryCorrectionDirections i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul]

/-- The most general low correction allowed by the history certificate,
including one optional copy of the returned quadratic section. -/
def ZeroOneOffAxisHistoryParameters.correction
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF p.correctionConstant p.correctionLinear
      p.correctionTwo +
    p.correctionReturn • p.returned

/-- The retained old high representative after its admissible correction. -/
def ZeroOneOffAxisHistoryParameters.correctedHighFactor
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  p.firstProduct + p.correction

/-- The normalized off-axis rational feedback factor. -/
def ZeroOneOffAxisHistoryParameters.feedbackFactor
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF p.feedbackConstant p.feedbackLinear
    (targetTwo rOneCoeff)

/-- The literal feedback product whose high coefficients and quadratic
quotient supply the remaining 24 equations of the raw certificate. -/
def ZeroOneOffAxisHistoryParameters.feedbackProduct
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  p.correctedHighFactor * p.feedbackFactor

theorem ZeroOneOffAxisHistoryParameters.quadraticANFOfForm_correctionTwo
    (p : ZeroOneOffAxisHistoryParameters) :
    quadraticANFOfForm p.correctionTwo =
      ∑ i : Fin 8, p.correctionTarget i •
        targetANF (returnHistoryCorrectionDirections i) := by
  change quadraticANFOfFormLinear p.correctionTwo = _
  rw [ZeroOneOffAxisHistoryParameters.correctionTwo, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul]
  change p.correctionTarget i •
      quadraticANFOfForm
        (targetTwo (returnHistoryCorrectionDirections i)) = _
  rw [quadraticANFOfForm_targetTwo]

theorem ZeroOneOffAxisHistoryParameters.quadraticANFOfForm_correctionTwo_eq_targetANF
    (p : ZeroOneOffAxisHistoryParameters) :
    quadraticANFOfForm p.correctionTwo = targetANF p.correctionCoeff := by
  rw [p.correctionTwo_eq_targetTwo, quadraticANFOfForm_targetTwo]

/-- The cubic part of the retained old high representative. -/
def ZeroOneOffAxisHistoryParameters.cubicCore
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  linearANFTen p.ell * targetANF rZeroCoeff +
    p.correctionReturn •
      (linearANFTen p.ell * targetANF rZeroCoeff +
        linearANFTen (p.ell + p.leftShift) * targetANF rZeroCoeff)

theorem targetANF_degreeLE_two (c : TargetCoeff) :
    N4.DegreeLE 2 (targetANF c) :=
  pureQuadraticANFSpace_le_quadraticANFSpace
    (targetANF_mem_pure c)

@[simp] theorem quadraticANFOfForm_zero :
    quadraticANFOfForm (0 : TwoForm) = 0 :=
  map_zero quadraticANFOfFormLinear

theorem Mul_five_eq_double_sum (s : Fin 9) :
    Mul 5 s = ∑ i : Fin 5, ∑ j : Fin 5,
      if i.val + j.val = s.val then
        X (aCoord i) * X (bCoord j) else 0 := by
  simp [Mul, mulCoefficient, aVar_five_eq_X_aCoord,
    bVar_five_eq_X_bCoord]

theorem targetANF_eq_double_sum (c : TargetCoeff) :
    targetANF c = ∑ i : Fin 5, ∑ j : Fin 5,
      c (hankelIndex i j) • (X (aCoord i) * X (bCoord j)) := by
  classical
  rw [targetANF]
  calc
    (∑ s : Fin 9, c s • Mul 5 s) =
        ∑ s : Fin 9, ∑ i : Fin 5, ∑ j : Fin 5,
          if i.val + j.val = s.val then
            c s • (X (aCoord i) * X (bCoord j)) else 0 := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Mul_five_eq_double_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases h : i.val + j.val = s.val <;> simp [h]
    _ = ∑ i : Fin 5, ∑ j : Fin 5, ∑ s : Fin 9,
          if i.val + j.val = s.val then
            c s • (X (aCoord i) * X (bCoord j)) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 5, ∑ j : Fin 5,
        c (hankelIndex i j) • (X (aCoord i) * X (bCoord j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Fintype.sum_eq_single (hankelIndex i j)]
      · simp [hankelIndex]
      · intro s hs
        have hne : i.val + j.val ≠ s.val := by
          intro h
          apply hs
          exact Fin.ext h.symm
        simp [hne]

@[simp] theorem evalHom_targetANF (c : TargetCoeff) (x : Fin 10 → F₂) :
    evalHom x (targetANF c) =
      ∑ i : Fin 5, ∑ j : Fin 5,
        c (hankelIndex i j) * x (aCoord i) * x (bCoord j) := by
  rw [targetANF_eq_double_sum]
  simp [map_sum, mul_assoc]

/-- The six terms of a quadratic coordinate word that can contribute to a
coefficient supported inside `{0,1,5}`. -/
def quadraticCoordinateANF015
    (a : F₂) (ell : LinearForm) (c : TargetCoeff) : ANF 10 :=
  a • (1 : ANF 10) + ell 0 • X 0 + ell 1 • X 1 + ell 5 • X 5 +
    c 0 • (X 0 * X 5) + c 1 • (X 1 * X 5)

/-- Equality on every monomial supported inside `{0,1,5}`. -/
structure EqualOn015 (x y : ANF 10) : Prop where
  coeff_eq : ∀ m : Monomial 10,
    m.vars ⊆ ({0, 1, 5} : Finset (Fin 10)) →
      x.coeff m = y.coeff m

theorem EqualOn015.add {x x' y y' : ANF 10}
    (hx : EqualOn015 x x') (hy : EqualOn015 y y') :
    EqualOn015 (x + y) (x' + y') := by
  constructor
  intro m hm
  simp [hx.coeff_eq m hm, hy.coeff_eq m hm]

theorem EqualOn015.smul (a : F₂) {x y : ANF 10}
    (h : EqualOn015 x y) : EqualOn015 (a • x) (a • y) := by
  constructor
  intro m hm
  simp [h.coeff_eq m hm]

theorem EqualOn015.mul {x x' y y' : ANF 10}
    (hx : EqualOn015 x x') (hy : EqualOn015 y y') :
    EqualOn015 (x * y) (x' * y') := by
  constructor
  intro m hm
  rw [coeff_mul_monomialUnionPairs, coeff_mul_monomialUnionPairs]
  apply Finset.sum_congr rfl
  intro p hp
  have hpair : p.1 * p.2 = m := (Finset.mem_filter.mp hp).2
  have hleft : p.1.vars ⊆ m.vars := by
    intro i hi
    have hi' : i ∈ (p.1 * p.2).vars := by simp [hi]
    rw [hpair] at hi'
    exact hi'
  have hright : p.2.vars ⊆ m.vars := by
    intro i hi
    have hi' : i ∈ (p.1 * p.2).vars := by simp [hi]
    rw [hpair] at hi'
    exact hi'
  rw [hx.coeff_eq p.1 (hleft.trans hm),
    hy.coeff_eq p.2 (hright.trans hm)]

private theorem quadraticCoordinateANF_target_equalOn015
    (a : F₂) (ell : LinearForm) (c : TargetCoeff) :
    EqualOn015 (quadraticCoordinateANF a ell (targetTwo c))
      (quadraticCoordinateANF015 a ell c) := by
  constructor
  intro m hm
  have hmPow : m.vars ∈ ({0, 1, 5} : Finset (Fin 10)).powerset :=
    Finset.mem_powerset.mpr hm
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by
    decide
  rw [hpowerset] at hmPow
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmPow
  rcases hmPow with h | h | h | h | h | h | h | h
  all_goals
    first
    | have hmm : m = ⟨∅⟩ := Monomial.ext h; subst m
    | have hmm : m = ⟨{0}⟩ := Monomial.ext h; subst m
    | have hmm : m = ⟨{1}⟩ := Monomial.ext h; subst m
    | have hmm : m = ⟨{0, 1}⟩ := Monomial.ext h; subst m
    | have hmm : m = ⟨{5}⟩ := Monomial.ext h; subst m
    | have hmm : m = ⟨{0, 5}⟩ := Monomial.ext h; subst m
    | have hmm : m = ⟨{1, 5}⟩ := Monomial.ext h; subst m
    | have hmm : m = ⟨{0, 1, 5}⟩ := Monomial.ext h; subst m
  all_goals
    simp +decide [quadraticCoordinateANF, quadraticCoordinateANF015,
      linearANFTen, quadraticANFOfForm_targetTwo,
      targetANF_eq_double_sum, aCoord, bCoord, hankelIndex,
      X, monomial,
      Fin.sum_univ_succ]

private theorem quadraticCoordinateANF_zero_equalOn015
    (a : F₂) (ell : LinearForm) :
    EqualOn015 (quadraticCoordinateANF a ell 0)
      (quadraticCoordinateANF015 a ell 0) := by
  have h := quadraticCoordinateANF_target_equalOn015 a ell
    (0 : TargetCoeff)
  have hz : targetTwo (0 : TargetCoeff) = (0 : TwoForm) := by
    change targetTwoLinear 0 = 0
    exact map_zero targetTwoLinear
  rw [hz] at h
  exact h

def ZeroOneOffAxisHistoryParameters.firstProduct015
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF015 0 p.ell 0 *
    quadraticCoordinateANF015 0 p.m rZeroCoeff

def ZeroOneOffAxisHistoryParameters.shiftedProduct015
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF015 0 (p.ell + p.leftShift) 0 *
    quadraticCoordinateANF015 0 (p.m + p.rightShift) rZeroCoeff

def ZeroOneOffAxisHistoryParameters.returned015
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  p.firstProduct015 + p.shiftedProduct015

def ZeroOneOffAxisHistoryParameters.correction015
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF015 p.correctionConstant p.correctionLinear
      p.correctionCoeff +
    p.correctionReturn • p.returned015

def ZeroOneOffAxisHistoryParameters.correctedHighFactor015
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  p.firstProduct015 + p.correction015

def ZeroOneOffAxisHistoryParameters.feedbackFactor015
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  quadraticCoordinateANF015 p.feedbackConstant p.feedbackLinear rOneCoeff

def ZeroOneOffAxisHistoryParameters.feedbackProduct015
    (p : ZeroOneOffAxisHistoryParameters) : ANF 10 :=
  p.correctedHighFactor015 * p.feedbackFactor015

set_option maxHeartbeats 600000 in
theorem ZeroOneOffAxisHistoryParameters.feedbackProduct_equalOn015
    (p : ZeroOneOffAxisHistoryParameters) :
    EqualOn015 p.feedbackProduct p.feedbackProduct015 := by
  have hfirstLeft :=
    quadraticCoordinateANF_zero_equalOn015 0 p.ell
  have hfirstRight :=
    quadraticCoordinateANF_target_equalOn015 0 p.m rZeroCoeff
  have hfirst : EqualOn015 p.firstProduct p.firstProduct015 :=
    EqualOn015.mul hfirstLeft hfirstRight
  have hshiftLeft :=
    quadraticCoordinateANF_zero_equalOn015 0
      (p.ell + p.leftShift)
  have hshiftRight :=
    quadraticCoordinateANF_target_equalOn015 0
      (p.m + p.rightShift) rZeroCoeff
  have hshift : EqualOn015 p.shiftedProduct p.shiftedProduct015 :=
    EqualOn015.mul hshiftLeft hshiftRight
  have hreturned : EqualOn015 p.returned p.returned015 :=
    EqualOn015.add hfirst hshift
  have hcorrectionBase : EqualOn015
      (quadraticCoordinateANF p.correctionConstant p.correctionLinear
        p.correctionTwo)
      (quadraticCoordinateANF015 p.correctionConstant p.correctionLinear
        p.correctionCoeff) := by
    rw [p.correctionTwo_eq_targetTwo]
    exact quadraticCoordinateANF_target_equalOn015 _ _ _
  have hcorrection : EqualOn015 p.correction p.correction015 :=
    EqualOn015.add hcorrectionBase
      (EqualOn015.smul p.correctionReturn hreturned)
  have hcorrected : EqualOn015 p.correctedHighFactor
      p.correctedHighFactor015 :=
    EqualOn015.add hfirst hcorrection
  have hfeedback :=
    quadraticCoordinateANF_target_equalOn015 p.feedbackConstant
      p.feedbackLinear rOneCoeff
  exact EqualOn015.mul hcorrected hfeedback

theorem degreeLE_add {m d : Nat} {p q : ANF m}
    (hp : N4.DegreeLE d p) (hq : N4.DegreeLE d q) :
    N4.DegreeLE d (p + q) := by
  intro s hs
  simp [hp s hs, hq s hs]

theorem degreeLE_smul {m d : Nat} {p : ANF m}
    (hp : N4.DegreeLE d p) (a : F₂) : N4.DegreeLE d (a • p) := by
  intro s hs
  simp [hp s hs]

/-- Sum of the five variables on the left side of the multiplication
tensor. -/
def aLinearSumTen : ANF 10 :=
  X (0 : Fin 10) + X 1 + X 2 + X 3 + X 4

/-- Sum of the five variables on the right side of the multiplication
tensor. -/
def bLinearSumTen : ANF 10 :=
  X (5 : Fin 10) + X 6 + X 7 + X 8 + X 9

@[simp] theorem targetANF_rZeroCoeff :
    targetANF rZeroCoeff = X (0 : Fin 10) * X (5 : Fin 10) := by
  simp [targetANF, rZeroCoeff, Mul, mulCoefficient,
    Fin.sum_univ_succ, aVar, bVar]

theorem targetANF_rOneCoeff :
    targetANF rOneCoeff = aLinearSumTen * bLinearSumTen := by
  simp [targetANF, rOneCoeff, Mul, mulCoefficient,
    aLinearSumTen, bLinearSumTen, Fin.sum_univ_succ, aVar, bVar]
  ring

theorem ZeroOneOffAxisHistoryParameters.firstProduct_add_cubicPart
    (p : ZeroOneOffAxisHistoryParameters) :
    p.firstProduct + linearANFTen p.ell * targetANF rZeroCoeff =
      linearANFTen p.ell * linearANFTen p.m := by
  have hzero : quadraticANFOfForm (0 : TwoForm) = 0 :=
    map_zero quadraticANFOfFormLinear
  simp [ZeroOneOffAxisHistoryParameters.firstProduct,
    quadraticCoordinateANF, hzero, quadraticANFOfForm_targetTwo]
  ring_nf
  simp

theorem ZeroOneOffAxisHistoryParameters.shiftedProduct_add_cubicPart
    (p : ZeroOneOffAxisHistoryParameters) :
    p.shiftedProduct +
        linearANFTen (p.ell + p.leftShift) * targetANF rZeroCoeff =
      linearANFTen (p.ell + p.leftShift) *
        linearANFTen (p.m + p.rightShift) := by
  have hzero : quadraticANFOfForm (0 : TwoForm) = 0 :=
    map_zero quadraticANFOfFormLinear
  simp [ZeroOneOffAxisHistoryParameters.shiftedProduct,
    quadraticCoordinateANF, hzero, quadraticANFOfForm_targetTwo]
  ring_nf
  simp

theorem ZeroOneOffAxisHistoryParameters.cubicCore_degreeLE_three
    (p : ZeroOneOffAxisHistoryParameters) :
    N4.DegreeLE 3 p.cubicCore := by
  have hfirst : N4.DegreeLE 3
      (linearANFTen p.ell * targetANF rZeroCoeff) :=
    (linearANFTen_degreeLE_one p.ell).mul
      (targetANF_degreeLE_two rZeroCoeff)
  have hshift : N4.DegreeLE 3
      (linearANFTen (p.ell + p.leftShift) * targetANF rZeroCoeff) :=
    (linearANFTen_degreeLE_one (p.ell + p.leftShift)).mul
      (targetANF_degreeLE_two rZeroCoeff)
  exact degreeLE_add hfirst
    (degreeLE_smul (degreeLE_add hfirst hshift) p.correctionReturn)

/-- Removing the displayed cubic core from the corrected old factor leaves
only degree-at-most-two terms. -/
theorem ZeroOneOffAxisHistoryParameters.correctedHighFactor_add_cubicCore_degreeLE_two
    (p : ZeroOneOffAxisHistoryParameters) :
    N4.DegreeLE 2 (p.correctedHighFactor + p.cubicCore) := by
  have hrewrite :
      p.correctedHighFactor + p.cubicCore =
        (p.firstProduct + linearANFTen p.ell * targetANF rZeroCoeff) +
          quadraticCoordinateANF p.correctionConstant p.correctionLinear
            p.correctionTwo +
          p.correctionReturn •
            ((p.firstProduct + linearANFTen p.ell * targetANF rZeroCoeff) +
              (p.shiftedProduct +
                linearANFTen (p.ell + p.leftShift) * targetANF rZeroCoeff)) := by
    simp [ZeroOneOffAxisHistoryParameters.correctedHighFactor,
      ZeroOneOffAxisHistoryParameters.correction,
      ZeroOneOffAxisHistoryParameters.returned,
      ZeroOneOffAxisHistoryParameters.cubicCore]
    module
  rw [hrewrite, p.firstProduct_add_cubicPart,
    p.shiftedProduct_add_cubicPart]
  have hfirst : N4.DegreeLE 2
      (linearANFTen p.ell * linearANFTen p.m) :=
    (linearANFTen_degreeLE_one p.ell).mul
      (linearANFTen_degreeLE_one p.m)
  have hshift : N4.DegreeLE 2
      (linearANFTen (p.ell + p.leftShift) *
        linearANFTen (p.m + p.rightShift)) :=
    (linearANFTen_degreeLE_one (p.ell + p.leftShift)).mul
      (linearANFTen_degreeLE_one (p.m + p.rightShift))
  have hcorrection : N4.DegreeLE 2
      (quadraticCoordinateANF p.correctionConstant p.correctionLinear
        p.correctionTwo) :=
    quadraticCoordinateANF_mem_quadraticANFSpace _ _ _
  exact degreeLE_add (degreeLE_add hfirst hcorrection)
    (degreeLE_smul (degreeLE_add hfirst hshift) p.correctionReturn)

theorem ZeroOneOffAxisHistoryParameters.feedbackFactor_degreeLE_two
    (p : ZeroOneOffAxisHistoryParameters) :
    N4.DegreeLE 2 p.feedbackFactor :=
  quadraticCoordinateANF_mem_quadraticANFSpace _ _ _

theorem ZeroOneOffAxisHistoryParameters.feedbackFactor_add_target_degreeLE_one
    (p : ZeroOneOffAxisHistoryParameters) :
    N4.DegreeLE 1 (p.feedbackFactor + targetANF rOneCoeff) := by
  have heq : p.feedbackFactor + targetANF rOneCoeff =
      p.feedbackConstant • (1 : ANF 10) +
        linearANFTen p.feedbackLinear := by
    simp [ZeroOneOffAxisHistoryParameters.feedbackFactor,
      quadraticCoordinateANF, quadraticANFOfForm_targetTwo]
    ring_nf
    simp
  rw [heq]
  have haffine : p.feedbackConstant • (1 : ANF 10) +
      linearANFTen p.feedbackLinear ∈ affine 10 :=
    (affine 10).add_mem
      ((affine 10).smul_mem p.feedbackConstant (one_mem_affine 10))
      (linearANFTen_mem_affine p.feedbackLinear)
  intro s hs
  exact N4.affine_coeff_zero_of_two_le haffine s (by omega)

/-- The literal feedback product differs from the cubic-core product only
in degree at most four. -/
theorem ZeroOneOffAxisHistoryParameters.feedbackProduct_add_coreProduct_degreeLE_four
    (p : ZeroOneOffAxisHistoryParameters) :
    N4.DegreeLE 4
      (p.feedbackProduct + p.cubicCore * targetANF rOneCoeff) := by
  have heq :
      p.feedbackProduct + p.cubicCore * targetANF rOneCoeff =
        (p.correctedHighFactor + p.cubicCore) * p.feedbackFactor +
          p.cubicCore * (p.feedbackFactor + targetANF rOneCoeff) := by
    simp [ZeroOneOffAxisHistoryParameters.feedbackProduct]
    ring_nf
    simp
  rw [heq]
  exact degreeLE_add
    (p.correctedHighFactor_add_cubicCore_degreeLE_two.mul
      p.feedbackFactor_degreeLE_two)
    (p.cubicCore_degreeLE_three.mul
      p.feedbackFactor_add_target_degreeLE_one)

/- The first degree-five feedback equation is computed from the small cubic
core on its 32-point support cube. -/
set_option maxRecDepth 8192 in
theorem ZeroOneOffAxisHistoryParameters.constraint_twenty_six_eq_core_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 26 =
      (p.cubicCore * targetANF rOneCoeff).coeff
        ⟨({0, 1, 5, 6, 7} : Finset (Fin 10))⟩ := by
  rw [targetANF_rOneCoeff]
  simp (config := { maxSteps := 5000000 }) +decide
    [zeroOneRawConstraint,
    ZeroOneOffAxisHistoryParameters.vector,
    ZeroOneOffAxisHistoryParameters.cubicCore,
    linearANFTen, aLinearSumTen, bLinearSumTen,
    Fin.sum_univ_succ, add_mul, mul_add, X, monomial_mul,
    coeff_monomial]
  ring_nf
  have htwo : (2 : F₂) = 0 := CharTwo.two_eq_zero
  rw [htwo]
  simp

/-- The first degree-five raw equation is exactly the matching literal
feedback coefficient. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_twenty_six_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 26 =
      p.feedbackProduct.coeff ⟨({0, 1, 5, 6, 7} : Finset (Fin 10))⟩ := by
  rw [p.constraint_twenty_six_eq_core_coeff]
  apply Eq.symm
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  exact p.feedbackProduct_add_coreProduct_degreeLE_four
    ⟨({0, 1, 5, 6, 7} : Finset (Fin 10))⟩ (by decide)

/- The second degree-five feedback equation is the symmetric sparse core
coefficient on support `0x073`. -/
set_option maxRecDepth 8192 in
theorem ZeroOneOffAxisHistoryParameters.constraint_twenty_seven_eq_core_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 27 =
      (p.cubicCore * targetANF rOneCoeff).coeff
        ⟨({0, 1, 4, 5, 6} : Finset (Fin 10))⟩ := by
  rw [targetANF_rOneCoeff]
  simp +decide [zeroOneRawConstraint,
    ZeroOneOffAxisHistoryParameters.vector,
    ZeroOneOffAxisHistoryParameters.cubicCore,
    linearANFTen, aLinearSumTen, bLinearSumTen,
    Fin.sum_univ_succ, add_mul, mul_add, X, monomial_mul,
    coeff_monomial]
  ring_nf
  have htwo : (2 : F₂) = 0 := CharTwo.two_eq_zero
  rw [htwo]
  simp

/-- The second degree-five raw equation is exactly the matching literal
feedback coefficient. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_twenty_seven_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 27 =
      p.feedbackProduct.coeff ⟨({0, 1, 4, 5, 6} : Finset (Fin 10))⟩ := by
  rw [p.constraint_twenty_seven_eq_core_coeff]
  apply Eq.symm
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  exact p.feedbackProduct_add_coreProduct_degreeLE_four
    ⟨({0, 1, 4, 5, 6} : Finset (Fin 10))⟩ (by decide)

/-- A literal quadratic feedback product supplies both terminal
degree-five equations of the raw history certificate. -/
theorem ZeroOneOffAxisHistoryParameters.degreeFiveFeedbackConstraints_eq_zero
    (p : ZeroOneOffAxisHistoryParameters)
    (hquadratic : p.feedbackProduct ∈ N4.quadraticANFSpace 10) :
    zeroOneRawConstraint p.vector 26 = 0 ∧
      zeroOneRawConstraint p.vector 27 = 0 := by
  constructor
  · rw [p.constraint_twenty_six_eq_feedback_coeff]
    exact hquadratic ⟨({0, 1, 5, 6, 7} : Finset (Fin 10))⟩ (by decide)
  · rw [p.constraint_twenty_seven_eq_feedback_coeff]
    exact hquadratic ⟨({0, 1, 4, 5, 6} : Finset (Fin 10))⟩ (by decide)

/- The first selected cubic feedback coordinate.  Every factor is projected
to the six terms supported inside `{0,1,5}` before multiplication. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
theorem ZeroOneOffAxisHistoryParameters.constraint_four_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 4 =
      p.feedbackProduct.coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [p.feedbackProduct_equalOn015.coeff_eq ⟨{0, 1, 5}⟩ (by simp)]
  rw [coeff_zero_one_five_eq_eval_sum]
  simp +decide [zeroOneRawConstraint,
    ZeroOneOffAxisHistoryParameters.vector,
    ZeroOneOffAxisHistoryParameters.feedbackProduct015,
    ZeroOneOffAxisHistoryParameters.correctedHighFactor015,
    ZeroOneOffAxisHistoryParameters.feedbackFactor015,
    ZeroOneOffAxisHistoryParameters.correction015,
    ZeroOneOffAxisHistoryParameters.returned015,
    ZeroOneOffAxisHistoryParameters.firstProduct015,
    ZeroOneOffAxisHistoryParameters.shiftedProduct015,
    quadraticCoordinateANF015,
    ZeroOneOffAxisHistoryParameters.correctionCoeff,
    returnHistoryCorrectionDirections, historyJOneCoeff,
    historyJInfinityCoeff,
    rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
    dStarZeroCoeff, dStarOneCoeff,
    eval_add', eval_mul', eval_smul', eval_one', eval_X,
    supportAssignmentTen, Fin.sum_univ_succ]
  ring_nf
  have htwo : (2 : F₂) = 0 := by decide
  have hthree : (3 : F₂) = 1 := by decide
  have hfour : (4 : F₂) = 0 := by decide
  have hsix : (6 : F₂) = 0 := by decide
  have height : (8 : F₂) = 0 := by decide
  simp only [htwo, hthree, hfour, hsix, height, mul_zero, mul_one,
    add_zero]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
theorem ZeroOneOffAxisHistoryParameters.constraint_five_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 5 =
      p.feedbackProduct.coeff
        ⟨({0, 4, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}} := by
    decide
  rw [hpowerset]
  simp +decide [zeroOneRawConstraint,
    ZeroOneOffAxisHistoryParameters.vector,
    ZeroOneOffAxisHistoryParameters.feedbackProduct,
    ZeroOneOffAxisHistoryParameters.correctedHighFactor,
    ZeroOneOffAxisHistoryParameters.feedbackFactor,
    ZeroOneOffAxisHistoryParameters.correction,
    ZeroOneOffAxisHistoryParameters.returned,
    ZeroOneOffAxisHistoryParameters.firstProduct,
    ZeroOneOffAxisHistoryParameters.shiftedProduct,
    quadraticCoordinateANF,
    p.quadraticANFOfForm_correctionTwo_eq_targetANF,
    ZeroOneOffAxisHistoryParameters.correctionCoeff,
    returnHistoryCorrectionDirections, historyJOneCoeff,
    historyJInfinityCoeff,
    rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
    dStarZeroCoeff, dStarOneCoeff,
    quadraticANFOfForm_targetTwo, quadraticANFOfForm_zero,
    linearANFTen, aCoord, bCoord, hankelIndex,
    eval_eq_evalHom, supportAssignmentTen, Fin.sum_univ_succ]
  ring_nf
  have htwo : (2 : F₂) = 0 := by decide
  have hthree : (3 : F₂) = 1 := by decide
  have hfour : (4 : F₂) = 0 := by decide
  have hsix : (6 : F₂) = 0 := by decide
  have height : (8 : F₂) = 0 := by decide
  simp only [htwo, hthree, hfour, hsix, height, mul_zero, mul_one,
    add_zero]

/-- The complete cubic projection of the returned product depends only on
the left linear shift: the original linear part occurs twice and cancels. -/
theorem ZeroOneOffAxisHistoryParameters.returned_cubic_eq
    (p : ZeroOneOffAxisHistoryParameters) :
    anfThreeProjectionTen p.returned =
      ambientVectorWedgeTwo p.leftShift (targetTwo rZeroCoeff) := by
  have hzero (i j : Fin 10) :
      ambientTwoCoeff (0 : TwoForm) i j = 0 := by
    simp [ambientTwoCoeff]
  rw [ZeroOneOffAxisHistoryParameters.returned, map_add,
    ZeroOneOffAxisHistoryParameters.firstProduct,
    ZeroOneOffAxisHistoryParameters.shiftedProduct,
    anfThreeProjectionTen_quadraticCoordinateANF_mul,
    anfThreeProjectionTen_quadraticCoordinateANF_mul]
  funext i j k
  simp [exactLowProductCubic, quadraticOverlapCubic, factorPlaneCubic,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN, quadraticANFOfForm, hzero]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The first selected return-high polynomial is exactly the `0x023` cubic
coefficient of the literal returned product. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_zero_eq_returned_cubic
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 0 =
      anfThreeProjectionTen p.returned 0 1 5 := by
  have h15 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (1 : Fin 10) 5 = 0 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 1) (bCoord 0) = 0
    simp [rZeroCoeff, hankelIndex]
  have h05 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 5 = 1 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 0) = 1
    simp [rZeroCoeff, hankelIndex]
  have h01 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 1 = 0 := by
    rw [ambientTwoCoeff,
      dif_neg (show (0 : Fin 10) ≠ 1 by decide)]
    change targetTwo rZeroCoeff
      (quadraticPair (aCoord 0) (aCoord 1) (by decide)) = 0
    exact targetTwo_sameA rZeroCoeff 0 1 (by decide)
  rw [p.returned_cubic_eq]
  simp [zeroOneRawConstraint, ZeroOneOffAxisHistoryParameters.vector,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    h15, h05, h01]

/-- The second selected return-high polynomial is the `0x031` cubic
coefficient of the literal returned product. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_one_eq_returned_cubic
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 1 =
      anfThreeProjectionTen p.returned 0 4 5 := by
  have h45 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (4 : Fin 10) 5 = 0 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 4) (bCoord 0) = 0
    simp [rZeroCoeff, hankelIndex]
  have h05 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 5 = 1 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 0) = 1
    simp [rZeroCoeff, hankelIndex]
  have h04 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 4 = 0 := by
    rw [ambientTwoCoeff,
      dif_neg (show (0 : Fin 10) ≠ 4 by decide)]
    change targetTwo rZeroCoeff
      (quadraticPair (aCoord 0) (aCoord 4) (by decide)) = 0
    exact targetTwo_sameA rZeroCoeff 0 4 (by decide)
  rw [p.returned_cubic_eq]
  simp [zeroOneRawConstraint, ZeroOneOffAxisHistoryParameters.vector,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    h45, h05, h04]

/-- The third selected return-high polynomial is the `0x061` cubic
coefficient of the literal returned product. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_two_eq_returned_cubic
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 2 =
      anfThreeProjectionTen p.returned 0 5 6 := by
  have h56 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (5 : Fin 10) 6 = 0 := by
    rw [ambientTwoCoeff,
      dif_neg (show (5 : Fin 10) ≠ 6 by decide)]
    change targetTwo rZeroCoeff
      (quadraticPair (bCoord 0) (bCoord 1) (by decide)) = 0
    exact targetTwo_sameB rZeroCoeff 0 1 (by decide)
  have h06 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 6 = 0 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 1) = 0
    simp [rZeroCoeff, hankelIndex]
  have h05 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 5 = 1 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 0) = 1
    simp [rZeroCoeff, hankelIndex]
  rw [p.returned_cubic_eq]
  simp [zeroOneRawConstraint, ZeroOneOffAxisHistoryParameters.vector,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    h56, h06, h05]

/-- The fourth selected return-high polynomial is the `0x0a1` cubic
coefficient of the literal returned product. -/
theorem ZeroOneOffAxisHistoryParameters.constraint_three_eq_returned_cubic
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRawConstraint p.vector 3 =
      anfThreeProjectionTen p.returned 0 5 7 := by
  have h57 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (5 : Fin 10) 7 = 0 := by
    rw [ambientTwoCoeff,
      dif_neg (show (5 : Fin 10) ≠ 7 by decide)]
    change targetTwo rZeroCoeff
      (quadraticPair (bCoord 0) (bCoord 2) (by decide)) = 0
    exact targetTwo_sameB rZeroCoeff 0 2 (by decide)
  have h07 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 7 = 0 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 2) = 0
    simp [rZeroCoeff, hankelIndex]
  have h05 : ambientTwoCoeff (targetTwo rZeroCoeff)
      (0 : Fin 10) 5 = 1 := by
    change ambientTwoCoeff (targetTwo rZeroCoeff)
      (aCoord 0) (bCoord 0) = 1
    simp [rZeroCoeff, hankelIndex]
  rw [p.returned_cubic_eq]
  simp [zeroOneRawConstraint, ZeroOneOffAxisHistoryParameters.vector,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    h57, h07, h05]

/-- A literal quadratic return supplies the first four equations consumed by
the raw history certificate. -/
theorem ZeroOneOffAxisHistoryParameters.returnHighConstraints_eq_zero
    (p : ZeroOneOffAxisHistoryParameters)
    (hquadratic : p.returned ∈ N4.quadraticANFSpace 10) :
    zeroOneRawConstraint p.vector 0 = 0 ∧
    zeroOneRawConstraint p.vector 1 = 0 ∧
    zeroOneRawConstraint p.vector 2 = 0 ∧
    zeroOneRawConstraint p.vector 3 = 0 := by
  have hcubic := anfThreeProjectionTen_eq_zero_of_quadratic hquadratic
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p.constraint_zero_eq_returned_cubic]
    exact congrFun (congrFun (congrFun hcubic 0) 1) 5
  · rw [p.constraint_one_eq_returned_cubic]
    exact congrFun (congrFun (congrFun hcubic 0) 4) 5
  · rw [p.constraint_two_eq_returned_cubic]
    exact congrFun (congrFun (congrFun hcubic 0) 5) 6
  · rw [p.constraint_three_eq_returned_cubic]
    exact congrFun (congrFun (congrFun hcubic 0) 5) 7

end
end N5
end UnrestrictedBooleanMul
