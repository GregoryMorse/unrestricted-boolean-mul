import UnrestrictedBooleanMul.N5.ShadowRecovery
import UnrestrictedBooleanMul.N5.EffectiveFibers

/-!
# Local evaluation frames for shadow recovery

The four closed-place charts use four displayed local linear coordinates.
This module supplies six explicit complementary coordinates for each chart
and proves that every local exterior two-form annihilates them.  It is the
concrete bridge from the basis-free cubic shadow theorem to the rational and
degree-two local planes in manuscript Lemma 11.2.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Six complementary coordinates for each local four-space.  The rows are
ordered by `2P₀, 2P₁, 2P∞, Pₙ`; within a row the first three coordinates
belong to the `a` side and the last three to the `b` side. -/
def closedPlaceExternalBasis : Fin 4 → Fin 6 → LinearForm :=
  ![
    ![aLinear 2, aLinear 3, aLinear 4,
      bLinear 2, bLinear 3, bLinear 4],
    ![aLinear 0 + aLinear 2, aLinear 2 + aLinear 4,
      aLinear 1 + aLinear 3,
      bLinear 0 + bLinear 2, bLinear 2 + bLinear 4,
      bLinear 1 + bLinear 3],
    ![aLinear 0, aLinear 1, aLinear 2,
      bLinear 0, bLinear 1, bLinear 2],
    ![aLinear 0 + aLinear 1 + aLinear 2,
      aLinear 0 + aLinear 3, aLinear 1 + aLinear 4,
      bLinear 0 + bLinear 1 + bLinear 2,
      bLinear 0 + bLinear 3, bLinear 1 + bLinear 4]
  ]

/-- Rational value vectors on the two input sides, ordered by
`0, 1, ∞`. -/
def rationalValueA : Fin 3 → LinearForm :=
  ![aLinear 0, aOneEval, aLinear 4]

def rationalValueB : Fin 3 → LinearForm :=
  ![bLinear 0, bOneEval, bLinear 4]

def rationalValueCoeff : Fin 3 → TargetCoeff :=
  ![rZeroCoeff, rOneCoeff, rInfinityCoeff]

/-- The three unordered pairs of distinct rational places. -/
def rationalPairLeft : Fin 3 → Fin 3 := ![0, 0, 1]
def rationalPairRight : Fin 3 → Fin 3 := ![1, 2, 2]

/-- Ordered four-frame for a pair of rational value places. -/
def rationalPairLocalBasis (pair : Fin 3) : Fin 4 → LinearForm :=
  ![rationalValueA (rationalPairLeft pair),
    rationalValueA (rationalPairRight pair),
    rationalValueB (rationalPairLeft pair),
    rationalValueB (rationalPairRight pair)]

/-- Six complementary coordinates for the three rational-pair frames
`01, 0∞, 1∞`. -/
def rationalPairExternalBasis : Fin 3 → Fin 6 → LinearForm :=
  ![
    ![aLinear 1 + aLinear 2, aLinear 2 + aLinear 3,
      aLinear 3 + aLinear 4,
      bLinear 1 + bLinear 2, bLinear 2 + bLinear 3,
      bLinear 3 + bLinear 4],
    ![aLinear 1, aLinear 2, aLinear 3,
      bLinear 1, bLinear 2, bLinear 3],
    ![aLinear 0 + aLinear 1, aLinear 1 + aLinear 2,
      aLinear 2 + aLinear 3,
      bLinear 0 + bLinear 1, bLinear 1 + bLinear 2,
      bLinear 2 + bLinear 3]
  ]

@[simp] theorem ambientLinearPair_add_left
    (x y u : LinearForm) :
    ambientLinearPair (x + y) u =
      ambientLinearPair x u + ambientLinearPair y u := by
  simp only [ambientLinearPair, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

@[simp] theorem ambientLinearPair_add_right
    (x u v : LinearForm) :
    ambientLinearPair x (u + v) =
      ambientLinearPair x u + ambientLinearPair x v := by
  simp only [ambientLinearPair, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

@[simp] theorem ambientLinearPair_sum_left
    {I : Type*} [Fintype I] (x : I → LinearForm) (u : LinearForm) :
    ambientLinearPair (∑ i, x i) u =
      ∑ i, ambientLinearPair (x i) u := by
  simp only [ambientLinearPair, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

@[simp] theorem ambientLinearPair_basis (i j : Fin 10) :
    ambientLinearPair ((Pi.basisFun F₂ (Fin 10)) i)
      ((Pi.basisFun F₂ (Fin 10)) j) = if i = j then 1 else 0 := by
  unfold ambientLinearPair
  rw [Fintype.sum_eq_single i]
  · simp [Pi.basisFun, Pi.single_apply]
  · intro k hki
    simp [Pi.basisFun, Pi.single_apply, hki]

@[simp] theorem ambientLinearPair_aLinear_aLinear (i j : Fin 5) :
    ambientLinearPair (aLinear i) (aLinear j) = if i = j then 1 else 0 := by
  change ambientLinearPair ((Pi.basisFun F₂ (Fin 10)) (aCoord i))
    ((Pi.basisFun F₂ (Fin 10)) (aCoord j)) = _
  rw [ambientLinearPair_basis]
  simp

@[simp] theorem ambientLinearPair_bLinear_bLinear (i j : Fin 5) :
    ambientLinearPair (bLinear i) (bLinear j) = if i = j then 1 else 0 := by
  change ambientLinearPair ((Pi.basisFun F₂ (Fin 10)) (bCoord i))
    ((Pi.basisFun F₂ (Fin 10)) (bCoord j)) = _
  rw [ambientLinearPair_basis]
  simp

@[simp] theorem ambientLinearPair_aLinear_bLinear (i j : Fin 5) :
    ambientLinearPair (aLinear i) (bLinear j) = 0 := by
  change ambientLinearPair ((Pi.basisFun F₂ (Fin 10)) (aCoord i))
    ((Pi.basisFun F₂ (Fin 10)) (bCoord j)) = 0
  rw [ambientLinearPair_basis]
  simp [aCoord_ne_bCoord]

@[simp] theorem ambientLinearPair_bLinear_aLinear (i j : Fin 5) :
    ambientLinearPair (bLinear i) (aLinear j) = 0 := by
  change ambientLinearPair ((Pi.basisFun F₂ (Fin 10)) (bCoord i))
    ((Pi.basisFun F₂ (Fin 10)) (aCoord j)) = 0
  rw [ambientLinearPair_basis]
  simp

/-- The displayed external coordinates are orthogonal to every displayed
local coordinate. -/
theorem ambientLinearPair_closedPlaceLocal_external
    (place : Fin 4) (i : Fin 4) (e : Fin 6) :
    ambientLinearPair (closedPlaceLocalBasis place i)
      (closedPlaceExternalBasis place e) = 0 := by
  fin_cases place <;> fin_cases i <;> fin_cases e <;>
    simp [closedPlaceLocalBasis,
      closedPlaceExternalBasis, aOneEval, aOneJet, bOneEval, bOneJet,
      aStarZero, aStarOne, bStarZero, bStarOne,
      Fin.sum_univ_succ]

/-- Orthogonality of every rational-pair local frame and its displayed
external frame. -/
theorem ambientLinearPair_rationalPairLocal_external
    (pair : Fin 3) (i : Fin 4) (e : Fin 6) :
    ambientLinearPair (rationalPairLocalBasis pair i)
      (rationalPairExternalBasis pair e) = 0 := by
  fin_cases pair <;> fin_cases i <;> fin_cases e <;>
    simp [rationalPairLocalBasis, rationalPairExternalBasis,
      rationalPairLeft, rationalPairRight, rationalValueA, rationalValueB,
      aOneEval, bOneEval, Fin.sum_univ_succ]

/-- Each rational value target is the wedge of its two evaluation vectors. -/
theorem targetTwo_rationalValueCoeff (place : Fin 3) :
    targetTwo (rationalValueCoeff place) =
      squarefreeWedge (rationalValueA place) (rationalValueB place) := by
  fin_cases place
  · simpa [rationalValueCoeff, rationalValueA, rationalValueB,
      targetPairTwo] using targetTwo_rZero
  · simpa [rationalValueCoeff, rationalValueA, rationalValueB,
      aOneEval, bOneEval] using targetTwo_rOne
  · simpa [rationalValueCoeff, rationalValueA, rationalValueB,
      targetPairTwo] using targetTwo_rInfinity

/-- Two-forms annihilating a fixed vector form a linear subspace. -/
def ambientRadicalTwoSpace (u : LinearForm) : Submodule F₂ TwoForm where
  carrier := {q | AmbientRadicalVector q u}
  zero_mem' := by
    intro j
    apply Finset.sum_eq_zero
    intro i _
    by_cases hij : i = j <;> simp [ambientTwoCoeff, hij]
  add_mem' := by
    intro q c hq hc j
    simp_rw [ambientTwoCoeff_add, mul_add, Finset.sum_add_distrib,
      hq j, hc j, add_zero]
  smul_mem' := by
    intro a q hq j
    simp_rw [ambientTwoCoeff_smul]
    calc
      ∑ i : Fin 10, u i * (a * ambientTwoCoeff q i j) =
          a * ∑ i : Fin 10, u i * ambientTwoCoeff q i j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 0 := by rw [hq j, mul_zero]

/-- A vector orthogonal to both factors of a decomposable two-form lies in
its radical. -/
theorem squarefreeWedge_mem_ambientRadicalTwoSpace
    (x y u : LinearForm)
    (hx : ambientLinearPair x u = 0)
    (hy : ambientLinearPair y u = 0) :
    squarefreeWedge x y ∈ ambientRadicalTwoSpace u := by
  intro j
  simp_rw [ambientTwoCoeff_squarefreeWedge, mul_add,
    Finset.sum_add_distrib]
  calc
    (∑ i : Fin 10, u i * (x i * y j)) +
        ∑ i : Fin 10, u i * (x j * y i) =
        ambientLinearPair x u * y j +
          x j * ambientLinearPair y u := by
            unfold ambientLinearPair
            congr 1
            · rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
            · rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
    _ = 0 := by rw [hx, hy]; simp

/-- Every local two-form annihilates every one of the six complementary
coordinates of its closed-place frame. -/
theorem localTwoForm_external_radical
    (place : Fin 4) (p : LocalKleinCoord) (e : Fin 6) :
    AmbientRadicalVector (localTwoForm place p)
      (closedPlaceExternalBasis place e) := by
  change localTwoForm place p ∈
    ambientRadicalTwoSpace (closedPlaceExternalBasis place e)
  rw [localTwoForm]
  apply Submodule.sum_mem
  intro s _
  apply Submodule.smul_mem
  apply squarefreeWedge_mem_ambientRadicalTwoSpace
  · exact ambientLinearPair_closedPlaceLocal_external
      place (localKleinPair s).1 e
  · exact ambientLinearPair_closedPlaceLocal_external
      place (localKleinPair s).2 e

/-- An arbitrary two-dimensional coefficient combination in one of the
three rational-pair planes. -/
def rationalPairTwo (pair : Fin 3) (s : Fin 2 → F₂) : TwoForm :=
  s 0 • targetTwo (rationalValueCoeff (rationalPairLeft pair)) +
    s 1 • targetTwo (rationalValueCoeff (rationalPairRight pair))

/-- Every rational-pair combination annihilates the corresponding six
external coordinates. -/
theorem rationalPairTwo_external_radical
    (pair : Fin 3) (s : Fin 2 → F₂) (e : Fin 6) :
    AmbientRadicalVector (rationalPairTwo pair s)
      (rationalPairExternalBasis pair e) := by
  change rationalPairTwo pair s ∈
    ambientRadicalTwoSpace (rationalPairExternalBasis pair e)
  rw [rationalPairTwo]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    rw [targetTwo_rationalValueCoeff]
    apply squarefreeWedge_mem_ambientRadicalTwoSpace
    · simpa [rationalPairLocalBasis] using
        ambientLinearPair_rationalPairLocal_external pair 0 e
    · simpa [rationalPairLocalBasis] using
        ambientLinearPair_rationalPairLocal_external pair 2 e
  · apply Submodule.smul_mem
    rw [targetTwo_rationalValueCoeff]
    apply squarefreeWedge_mem_ambientRadicalTwoSpace
    · simpa [rationalPairLocalBasis] using
        ambientLinearPair_rationalPairLocal_external pair 1 e
    · simpa [rationalPairLocalBasis] using
        ambientLinearPair_rationalPairLocal_external pair 3 e

/-- Independent cubic presentations through two local quadratic directions
have identical exterior quadratic shadows on the full six-dimensional
external frame. -/
theorem localIndependentPlane_cubic_recovers_external_shadow
    (place : Fin 4) (p r : LocalKleinCoord)
    (hind : LinearIndependent F₂
      (quadraticPlaneDirections (localTwoForm place p)
        (localTwoForm place r)))
    (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m (localTwoForm place p)
        (localTwoForm place r) =
      factorPlaneCubic ell' m' (localTwoForm place p)
        (localTwoForm place r))
    (i j : Fin 6) :
    externalShadowValue ell m (closedPlaceExternalBasis place i)
        (closedPlaceExternalBasis place j) =
      externalShadowValue ell' m' (closedPlaceExternalBasis place i)
        (closedPlaceExternalBasis place j) := by
  apply independentPlane_cubic_recovers_radical_shadow
    (localTwoForm place p) (localTwoForm place r) hind
      ell m ell' m' hcubic
  · exact localTwoForm_external_radical place p i
  · exact localTwoForm_external_radical place r i
  · exact localTwoForm_external_radical place p j
  · exact localTwoForm_external_radical place r j

/-- Rank-one local cubic presentations have zero exterior shadow on the
full six-dimensional external frame. -/
theorem localSingleDirection_cubic_forces_external_shadow_zero
    (place : Fin 4) (p : LocalKleinCoord)
    (hp : localTwoForm place p ≠ 0)
    (ell m : LinearForm)
    (hcubic : ambientVectorWedgeTwo ell (localTwoForm place p) =
      ambientVectorWedgeTwo m (localTwoForm place p))
    (i j : Fin 6) :
    externalShadowValue ell m (closedPlaceExternalBasis place i)
      (closedPlaceExternalBasis place j) = 0 := by
  apply singleDirection_cubic_forces_radical_shadow_zero
    (localTwoForm place p) hp ell m hcubic
  · exact localTwoForm_external_radical place p i
  · exact localTwoForm_external_radical place p j

/-- Concrete closed-place target-plane wrapper.  The global Hankel target
directions are converted to their exact local Pluecker coordinates before
applying cubic shadow recovery. -/
theorem closedPlaceTargetPlane_cubic_recovers_external_shadow
    (place : Fin 4) (z w : LocalTargetParam)
    (hind : LinearIndependent F₂
      (quadraticPlaneDirections
        (targetTwo (closedPlaceTargetCoeff place z))
        (targetTwo (closedPlaceTargetCoeff place w))))
    (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m
        (targetTwo (closedPlaceTargetCoeff place z))
        (targetTwo (closedPlaceTargetCoeff place w)) =
      factorPlaneCubic ell' m'
        (targetTwo (closedPlaceTargetCoeff place z))
        (targetTwo (closedPlaceTargetCoeff place w)))
    (i j : Fin 6) :
    externalShadowValue ell m (closedPlaceExternalBasis place i)
        (closedPlaceExternalBasis place j) =
      externalShadowValue ell' m' (closedPlaceExternalBasis place i)
        (closedPlaceExternalBasis place j) := by
  rw [targetTwo_closedPlaceTargetCoeff,
    targetTwo_closedPlaceTargetCoeff] at hind hcubic
  exact localIndependentPlane_cubic_recovers_external_shadow
    place (closedPlaceTargetCoord place z) (closedPlaceTargetCoord place w)
      hind ell m ell' m' hcubic i j

/-- Concrete rank-one closed-place target wrapper. -/
theorem closedPlaceTargetDirection_cubic_forces_external_shadow_zero
    (place : Fin 4) (z : LocalTargetParam)
    (hz : targetTwo (closedPlaceTargetCoeff place z) ≠ 0)
    (ell m : LinearForm)
    (hcubic : ambientVectorWedgeTwo ell
        (targetTwo (closedPlaceTargetCoeff place z)) =
      ambientVectorWedgeTwo m
        (targetTwo (closedPlaceTargetCoeff place z)))
    (i j : Fin 6) :
    externalShadowValue ell m (closedPlaceExternalBasis place i)
      (closedPlaceExternalBasis place j) = 0 := by
  rw [targetTwo_closedPlaceTargetCoeff] at hz hcubic
  exact localSingleDirection_cubic_forces_external_shadow_zero
    place (closedPlaceTargetCoord place z) hz ell m hcubic i j

/-- Cubic shadow recovery on each of the three rational-pair exceptional
planes. -/
theorem rationalPairPlane_cubic_recovers_external_shadow
    (pair : Fin 3) (s t : Fin 2 → F₂)
    (hind : LinearIndependent F₂
      (quadraticPlaneDirections (rationalPairTwo pair s)
        (rationalPairTwo pair t)))
    (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m (rationalPairTwo pair s)
        (rationalPairTwo pair t) =
      factorPlaneCubic ell' m' (rationalPairTwo pair s)
        (rationalPairTwo pair t))
    (i j : Fin 6) :
    externalShadowValue ell m (rationalPairExternalBasis pair i)
        (rationalPairExternalBasis pair j) =
      externalShadowValue ell' m' (rationalPairExternalBasis pair i)
        (rationalPairExternalBasis pair j) := by
  apply independentPlane_cubic_recovers_radical_shadow
    (rationalPairTwo pair s) (rationalPairTwo pair t) hind
      ell m ell' m' hcubic
  · exact rationalPairTwo_external_radical pair s i
  · exact rationalPairTwo_external_radical pair t i
  · exact rationalPairTwo_external_radical pair s j
  · exact rationalPairTwo_external_radical pair t j

/-- Rank-one companion on a rational-pair plane. -/
theorem rationalPairDirection_cubic_forces_external_shadow_zero
    (pair : Fin 3) (s : Fin 2 → F₂)
    (hs : rationalPairTwo pair s ≠ 0)
    (ell m : LinearForm)
    (hcubic : ambientVectorWedgeTwo ell (rationalPairTwo pair s) =
      ambientVectorWedgeTwo m (rationalPairTwo pair s))
    (i j : Fin 6) :
    externalShadowValue ell m (rationalPairExternalBasis pair i)
      (rationalPairExternalBasis pair j) = 0 := by
  apply singleDirection_cubic_forces_radical_shadow_zero
    (rationalPairTwo pair s) hs ell m hcubic
  · exact rationalPairTwo_external_radical pair s i
  · exact rationalPairTwo_external_radical pair s j

end
end N5
end UnrestrictedBooleanMul
