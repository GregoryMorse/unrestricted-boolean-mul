import UnrestrictedBooleanMul.N5.RankTwoSecants

/-!
# Exact classification of effective five-term quadratic fibers

This module turns the closed-place atlas into a classification theorem.  The
first layer below gives each of the nine non-rational rank-two Hankel words a
four-factor secant presentation and proves that its contraction support is
exactly the corresponding closed-place four-space.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Pluecker coordinates of a decomposable local two-form satisfy the Klein
equation. -/
theorem localWedgeCoord_satisfiesKlein (u v : LocalKleinParam) :
    SatisfiesKlein (localWedgeCoord u v) := by
  have htwo : (2 : F₂) = 0 := by decide
  simp [SatisfiesKlein, localWedgeCoord, localKleinPair]
  ring_nf
  simp [htwo]

/-- A decomposable form with factors in a closed-place four-space has local
Pluecker coordinates satisfying the Klein equation. -/
theorem exists_satisfiesKlein_of_factors_mem (place : Fin 4)
    (u v : LinearForm) (hu : u ∈ closedPlaceLinearSpace place)
    (hv : v ∈ closedPlaceLinearSpace place) :
    ∃ p : LocalKleinCoord,
      SatisfiesKlein p ∧ localTwoForm place p = squarefreeWedge u v := by
  let u' : closedPlaceLinearSpace place := ⟨u, hu⟩
  let v' : closedPlaceLinearSpace place := ⟨v, hv⟩
  let cu := closedPlaceVectorCoordinates place u'
  let cv := closedPlaceVectorCoordinates place v'
  refine ⟨localWedgeCoord cu cv, localWedgeCoord_satisfiesKlein cu cv, ?_⟩
  rw [localTwoForm_localWedgeCoord,
    closedPlaceVector_reconstruction place u',
    closedPlaceVector_reconstruction place v']

/-- Six ambient coefficient probes for each local exterior square. -/
def localTwoFormProbe : Fin 4 → Fin 6 → QuadraticIndex 10 :=
  ![![quadraticPair 0 1 (by decide), quadraticPair 0 5 (by decide),
      quadraticPair 0 6 (by decide), quadraticPair 1 5 (by decide),
      quadraticPair 1 6 (by decide), quadraticPair 5 6 (by decide)],
    ![quadraticPair 0 1 (by decide), quadraticPair 0 5 (by decide),
      quadraticPair 0 6 (by decide), quadraticPair 1 5 (by decide),
      quadraticPair 1 6 (by decide), quadraticPair 5 6 (by decide)],
    ![quadraticPair 3 4 (by decide), quadraticPair 3 8 (by decide),
      quadraticPair 3 9 (by decide), quadraticPair 4 8 (by decide),
      quadraticPair 4 9 (by decide), quadraticPair 8 9 (by decide)],
    ![quadraticPair 0 1 (by decide), quadraticPair 0 5 (by decide),
      quadraticPair 0 6 (by decide), quadraticPair 1 5 (by decide),
      quadraticPair 1 6 (by decide), quadraticPair 5 6 (by decide)]]

/-- The six local Pluecker directions remain independent in the ambient
45-dimensional squarefree quadratic space. -/
theorem localTwoForm_injective (place : Fin 4) :
    Function.Injective (localTwoForm place) := by
  intro p q h
  have h0 := congrFun h (localTwoFormProbe place 0)
  have h1 := congrFun h (localTwoFormProbe place 1)
  have h2 := congrFun h (localTwoFormProbe place 2)
  have h3 := congrFun h (localTwoFormProbe place 3)
  have h4 := congrFun h (localTwoFormProbe place 4)
  have h5 := congrFun h (localTwoFormProbe place 5)
  funext s
  fin_cases place <;>
    simp [localTwoFormProbe, localTwoForm, localKleinPair,
      closedPlaceLocalBasis, aOneEval, aOneJet, bOneEval, bOneJet,
      aStarZero, aStarOne, bStarZero, bStarOne, aLinear, bLinear,
      aCoord, bCoord, squarefreeWedge_pair, Pi.basisFun,
      Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
  all_goals fin_cases s <;> simp_all

/-- Quotient and target-plane coordinates of an arbitrary rational local
Pluecker vector. -/
def rationalQuotientParam (p : LocalKleinCoord) : LocalKleinParam :=
  ![p 0, p 2 + p 3, p 4, p 5]

def rationalTargetParam (p : LocalKleinCoord) : LocalTargetParam :=
  ![p 1, p 3]

/-- Quotient and target-plane coordinates at the degree-two place. -/
def degreeTwoQuotientParam (p : LocalKleinCoord) : LocalKleinParam :=
  ![p 0, p 3 + p 2, p 4 + p 1 + p 2, p 5]

def degreeTwoTargetParam (p : LocalKleinCoord) : LocalTargetParam :=
  ![p 1, p 2]

/-- Uniform coordinate extraction for the three rational charts and the
degree-two chart. -/
def closedPlaceQuotientParam (place : Fin 4) (p : LocalKleinCoord) :
    LocalKleinParam :=
  ![rationalQuotientParam p, rationalQuotientParam p,
    rationalQuotientParam p, degreeTwoQuotientParam p] place

def closedPlaceTargetParam (place : Fin 4) (p : LocalKleinCoord) :
    LocalTargetParam :=
  ![rationalTargetParam p, rationalTargetParam p,
    rationalTargetParam p, degreeTwoTargetParam p] place

def closedPlaceLocalPoint (place : Fin 4) (q : LocalKleinParam)
    (z : LocalTargetParam) : LocalKleinCoord :=
  ![rationalLocalPoint q z, rationalLocalPoint q z,
    rationalLocalPoint q z, degreeTwoLocalPoint q z] place

/-- Local target-plane coordinates inside the six Pluecker coordinates. -/
def closedPlaceTargetCoord (place : Fin 4) (z : LocalTargetParam) :
    LocalKleinCoord :=
  ![![0, z 0, z 1, z 1, 0, 0],
    ![0, z 0, z 1, z 1, 0, 0],
    ![0, z 0, z 1, z 1, 0, 0],
    ![0, z 0, z 1, z 1, z 0 + z 1, 0]] place

/-- Extraction followed by reconstruction is the identity in every local
chart. -/
theorem closedPlaceLocalPoint_extracted (place : Fin 4)
    (p : LocalKleinCoord) :
    closedPlaceLocalPoint place (closedPlaceQuotientParam place p)
      (closedPlaceTargetParam place p) = p := by
  have htwo : (2 : F₂) = 0 := by decide
  funext s
  fin_cases place <;> fin_cases s <;>
    simp [closedPlaceLocalPoint, closedPlaceQuotientParam,
      closedPlaceTargetParam, rationalLocalPoint, degreeTwoLocalPoint,
      rationalQuotientParam, rationalTargetParam,
      degreeTwoQuotientParam, degreeTwoTargetParam] <;>
    ring_nf <;> simp [htwo]

/-- A local point is its canonical quotient section plus its target-plane
translation. -/
theorem closedPlaceLocalPoint_eq_canonical_add_target
    (place : Fin 4) (q : LocalKleinParam) (z : LocalTargetParam) :
    closedPlaceLocalPoint place q z =
      closedPlaceCanonicalCoord place q + closedPlaceTargetCoord place z := by
  funext s
  fin_cases place <;> fin_cases s <;>
    simp [closedPlaceLocalPoint, closedPlaceCanonicalCoord,
      rationalLocalPoint, degreeTwoLocalPoint, rationalCanonicalCoord,
      degreeTwoCanonicalCoord, closedPlaceTargetCoord]
  all_goals ring

/-- Adding a local target direction preserves quotient coordinates. -/
theorem closedPlaceQuotientParam_add_target (place : Fin 4)
    (p : LocalKleinCoord) (z : LocalTargetParam) :
    closedPlaceQuotientParam place (p + closedPlaceTargetCoord place z) =
      closedPlaceQuotientParam place p := by
  have htwo : (2 : F₂) = 0 := by decide
  funext s
  fin_cases place <;> fin_cases s <;>
    simp [closedPlaceQuotientParam, rationalQuotientParam,
      degreeTwoQuotientParam, closedPlaceTargetCoord] <;>
    ring_nf <;> simp [htwo]

/-- Target coordinates translate by the added target-plane vector. -/
theorem closedPlaceTargetParam_add_target (place : Fin 4)
    (p : LocalKleinCoord) (z : LocalTargetParam) :
    closedPlaceTargetParam place (p + closedPlaceTargetCoord place z) =
      closedPlaceTargetParam place p + z := by
  funext s
  fin_cases place <;> fin_cases s <;>
    simp [closedPlaceTargetParam, rationalTargetParam,
      degreeTwoTargetParam, closedPlaceTargetCoord]

/-- Target-plane coordinate of each of the nine non-rational normal forms. -/
def outsideHankelTargetParam : Fin 9 → LocalTargetParam :=
  ![![0, 1], ![1, 1], ![1, 1], ![0, 1], ![1, 1],
    ![0, 1], ![1, 1], ![0, 1], ![1, 0]]

theorem outsideHankelLocalCoord_eq_targetCoord (k : Fin 9) :
    outsideHankelLocalCoord k =
      closedPlaceTargetCoord (outsideHankelPlace k)
        (outsideHankelTargetParam k) := by
  funext s
  fin_cases k <;> fin_cases s <;> decide

/-- A degree-two local fiber is effective exactly when it contains two
different Klein points. -/
def DegreeTwoHasDifference (q : LocalKleinParam) : Prop :=
  ∃ z ∈ degreeTwoKleinFiber q, ∃ w ∈ degreeTwoKleinFiber q, z ≠ w

theorem degreeTwoHasDifference_iff (q : LocalKleinParam) :
    DegreeTwoHasDifference q ↔ DegreeTwoLocalEffective q := by
  rcases f2_eq_zero_or_one (q 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (q 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (q 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (q 3) with h3 | h3 <;>
          simp [DegreeTwoHasDifference, degreeTwoKleinFiber,
            degreeTwoLocalPoint_klein_iff, DegreeTwoLocalEffective,
            h0, h1, h2, h3] <;> decide

theorem rationalLocalPoint_extracted (p : LocalKleinCoord) :
    rationalLocalPoint (rationalQuotientParam p) (rationalTargetParam p) = p := by
  simpa [closedPlaceLocalPoint, closedPlaceQuotientParam,
    closedPlaceTargetParam] using closedPlaceLocalPoint_extracted 0 p

theorem degreeTwoLocalPoint_extracted (p : LocalKleinCoord) :
    degreeTwoLocalPoint (degreeTwoQuotientParam p)
      (degreeTwoTargetParam p) = p := by
  simpa [closedPlaceLocalPoint, closedPlaceQuotientParam,
    closedPlaceTargetParam] using closedPlaceLocalPoint_extracted 3 p

/-- Characteristic two solves `p+p'=d` as `p'=p+d`. -/
theorem right_eq_add_of_add_eq {α : Type*} [AddCommGroup α] [Module F₂ α]
    (p p' d : α) (h : p + p' = d) : p' = p + d := by
  have hself : p + p = 0 := by
    calc
      p + p = (1 : F₂) • p + (1 : F₂) • p := by simp
      _ = ((1 : F₂) + 1) • p := (add_smul 1 1 p).symm
      _ = 0 := by
        have htwo : (1 : F₂) + 1 = 0 := by decide
        rw [htwo, zero_smul]
  calc
    p' = 0 + p' := (zero_add p').symm
    _ = (p + p) + p' := by rw [hself]
    _ = p + (p + p') := by rw [add_assoc]
    _ = p + d := by rw [h]

theorem ne_of_eq_add_of_ne_zero {α : Type*} [AddCommGroup α]
    {z w d : α} (h : w = z + d) (hd : d ≠ 0) : z ≠ w := by
  intro hzw
  apply hd
  have hz : z + 0 = z + d := by rw [add_zero, ← h, hzw]
  exact (add_left_cancel hz).symm

/-- Two rational local Klein points separated by a target vector with
nonzero jet coordinate determine one of the eleven effective parameters. -/
theorem rationalLocalEffective_of_difference (p p' : LocalKleinCoord)
    (d : LocalTargetParam) (hp : SatisfiesKlein p)
    (hp' : SatisfiesKlein p')
    (hadd : p + p' = closedPlaceTargetCoord 0 d) (hd : d 1 = 1) :
    RationalLocalEffective (rationalQuotientParam p) := by
  let q := rationalQuotientParam p
  let z := rationalTargetParam p
  let w := rationalTargetParam p'
  have hp'eq : p' = p + closedPlaceTargetCoord 0 d :=
    right_eq_add_of_add_eq p p' _ hadd
  have hq : rationalQuotientParam p' = q := by
    change closedPlaceQuotientParam 0 p' = _
    rw [hp'eq, closedPlaceQuotientParam_add_target]
    rfl
  have hw : w = z + d := by
    change closedPlaceTargetParam 0 p' =
      closedPlaceTargetParam 0 p + d
    rw [hp'eq, closedPlaceTargetParam_add_target]
  have hzmem : z ∈ rationalKleinFiber q := by
    simp only [rationalKleinFiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [q, z, rationalLocalPoint_extracted] using hp
  have hwmem : w ∈ rationalKleinFiber q := by
    simp only [rationalKleinFiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    have hpoint := rationalLocalPoint_extracted p'
    rw [hq] at hpoint
    simpa [q, w, hpoint] using hp'
  have hdne : d ≠ 0 := by
    intro hd0
    have := congrFun hd0 (1 : Fin 2)
    simp [hd] at this
  have hzw : z ≠ w := ne_of_eq_add_of_ne_zero hw hdne
  exact (rationalHasJetDifference_iff q).1 ⟨z, hzmem, w, hwmem, by
    intro hjet
    have hw1 := congrFun hw (1 : Fin 2)
    simp only [Pi.add_apply] at hw1
    have hz : z 1 + 0 = z 1 + d 1 := by
      rw [add_zero, ← hw1, hjet]
    have hd0 : (0 : F₂) = d 1 := add_left_cancel hz
    exact zero_ne_one (hd0.trans hd)⟩

/-- Two distinct degree-two local Klein points determine one of the ten
effective parameters. -/
theorem degreeTwoLocalEffective_of_difference (p p' : LocalKleinCoord)
    (d : LocalTargetParam) (hp : SatisfiesKlein p)
    (hp' : SatisfiesKlein p')
    (hadd : p + p' = closedPlaceTargetCoord 3 d) (hd : d ≠ 0) :
    DegreeTwoLocalEffective (degreeTwoQuotientParam p) := by
  let q := degreeTwoQuotientParam p
  let z := degreeTwoTargetParam p
  let w := degreeTwoTargetParam p'
  have hp'eq : p' = p + closedPlaceTargetCoord 3 d :=
    right_eq_add_of_add_eq p p' _ hadd
  have hq : degreeTwoQuotientParam p' = q := by
    change closedPlaceQuotientParam 3 p' = _
    rw [hp'eq, closedPlaceQuotientParam_add_target]
    rfl
  have hw : w = z + d := by
    change closedPlaceTargetParam 3 p' =
      closedPlaceTargetParam 3 p + d
    rw [hp'eq, closedPlaceTargetParam_add_target]
  have hzmem : z ∈ degreeTwoKleinFiber q := by
    simp only [degreeTwoKleinFiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [q, z, degreeTwoLocalPoint_extracted] using hp
  have hwmem : w ∈ degreeTwoKleinFiber q := by
    simp only [degreeTwoKleinFiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    have hpoint := degreeTwoLocalPoint_extracted p'
    rw [hq] at hpoint
    simpa [q, w, hpoint] using hp'
  exact (degreeTwoHasDifference_iff q).1
    ⟨z, hzmem, w, hwmem, ne_of_eq_add_of_ne_zero hw hd⟩

/-- The local quotient parameter extracted from either endpoint of a
non-rational Hankel secant belongs to the appropriate effective chart. -/
theorem outsideHankel_localEffectiveParam (k : Fin 9)
    (p p' : LocalKleinCoord) (hp : SatisfiesKlein p)
    (hp' : SatisfiesKlein p')
    (hadd : p + p' = outsideHankelLocalCoord k) :
    closedPlaceQuotientParam (outsideHankelPlace k) p ∈
      effectiveParamsAt (outsideHankelPlace k) := by
  have htarget : p + p' =
      closedPlaceTargetCoord (outsideHankelPlace k)
        (outsideHankelTargetParam k) := by
    rw [← outsideHankelLocalCoord_eq_targetCoord]
    exact hadd
  fin_cases k
  · have h := rationalLocalEffective_of_difference p p'
      (outsideHankelTargetParam 0) hp hp'
      (by simpa [outsideHankelPlace, closedPlaceTargetCoord] using htarget)
      (by decide)
    simpa [effectiveParamsAt, rationalEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h
  · have h := rationalLocalEffective_of_difference p p'
      (outsideHankelTargetParam 1) hp hp'
      (by simpa [outsideHankelPlace, closedPlaceTargetCoord] using htarget)
      (by decide)
    simpa [effectiveParamsAt, rationalEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h
  · have h := rationalLocalEffective_of_difference p p'
      (outsideHankelTargetParam 2) hp hp'
      (by simpa [outsideHankelPlace, closedPlaceTargetCoord] using htarget)
      (by decide)
    simpa [effectiveParamsAt, rationalEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h
  · have h := rationalLocalEffective_of_difference p p'
      (outsideHankelTargetParam 3) hp hp'
      (by simpa [outsideHankelPlace, closedPlaceTargetCoord] using htarget)
      (by decide)
    simpa [effectiveParamsAt, rationalEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h
  · have h := rationalLocalEffective_of_difference p p'
      (outsideHankelTargetParam 4) hp hp'
      (by simpa [outsideHankelPlace, closedPlaceTargetCoord] using htarget)
      (by decide)
    simpa [effectiveParamsAt, rationalEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h
  · have h := rationalLocalEffective_of_difference p p'
      (outsideHankelTargetParam 5) hp hp'
      (by simpa [outsideHankelPlace, closedPlaceTargetCoord] using htarget)
      (by decide)
    simpa [effectiveParamsAt, rationalEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h
  · have h := degreeTwoLocalEffective_of_difference p p'
      (outsideHankelTargetParam 6) hp hp' (by simpa [outsideHankelPlace] using htarget)
      (by decide)
    simpa [effectiveParamsAt, degreeTwoEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h
  · have h := degreeTwoLocalEffective_of_difference p p'
      (outsideHankelTargetParam 7) hp hp' (by simpa [outsideHankelPlace] using htarget)
      (by decide)
    simpa [effectiveParamsAt, degreeTwoEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h
  · have h := degreeTwoLocalEffective_of_difference p p'
      (outsideHankelTargetParam 8) hp hp' (by simpa [outsideHankelPlace] using htarget)
      (by decide)
    simpa [effectiveParamsAt, degreeTwoEffectiveParams,
      closedPlaceQuotientParam, outsideHankelPlace] using h

/-- The local coordinate `b` is the rational evaluation direction. -/
def rationalEvaluationLocalCoord : LocalKleinCoord :=
  ![0, 1, 0, 0, 0, 0]

theorem targetTwo_rZero_eq_local :
    targetTwo rZeroCoeff = localTwoForm 0 rationalEvaluationLocalCoord := by
  rw [targetTwo_rZero]
  simp [localTwoForm, rationalEvaluationLocalCoord, localKleinPair,
    closedPlaceLocalBasis, targetPairTwo, Fin.sum_univ_succ]

theorem targetTwo_rOne_eq_local :
    targetTwo rOneCoeff = localTwoForm 1 rationalEvaluationLocalCoord := by
  rw [targetTwo_rOne]
  simp [localTwoForm, rationalEvaluationLocalCoord, localKleinPair,
    closedPlaceLocalBasis, aOneEval, bOneEval, Fin.sum_univ_succ]

theorem targetTwo_rInfinity_eq_local :
    targetTwo rInfinityCoeff =
      localTwoForm 2 rationalEvaluationLocalCoord := by
  rw [targetTwo_rInfinity]
  simp [localTwoForm, rationalEvaluationLocalCoord, localKleinPair,
    closedPlaceLocalBasis, targetPairTwo, Fin.sum_univ_succ]

/-- Coefficient word of a local target-plane translation. -/
def closedPlaceTargetCoeff (place : Fin 4) (z : LocalTargetParam) :
    TargetCoeff :=
  ![z 0 • rZeroCoeff + z 1 • outsideHankelWord 0,
    z 0 • rOneCoeff + z 1 • outsideHankelWord 3,
    z 0 • rInfinityCoeff + z 1 • outsideHankelWord 5,
    z 0 • outsideHankelWord 8 + z 1 • outsideHankelWord 7] place

/-- Every local target-plane translation is an actual multiplication-target
two-form. -/
theorem targetTwo_closedPlaceTargetCoeff (place : Fin 4)
    (z : LocalTargetParam) :
    targetTwo (closedPlaceTargetCoeff place z) =
      localTwoForm place (closedPlaceTargetCoord place z) := by
  fin_cases place
  · calc
      targetTwo (closedPlaceTargetCoeff 0 z) =
          z 0 • targetTwo rZeroCoeff +
            z 1 • targetTwo (outsideHankelWord 0) := by
        change targetTwoLinear (z 0 • rZeroCoeff +
          z 1 • outsideHankelWord 0) = _
        simp [targetTwo]
      _ = z 0 • localTwoForm 0 rationalEvaluationLocalCoord +
          z 1 • localTwoForm 0 (outsideHankelLocalCoord 0) := by
        rw [targetTwo_rZero_eq_local, targetTwo_outsideHankelWord]
        rfl
      _ = localTwoForm 0
          (z 0 • rationalEvaluationLocalCoord +
            z 1 • outsideHankelLocalCoord 0) := by
        change z 0 • localTwoFormLinear 0 rationalEvaluationLocalCoord +
          z 1 • localTwoFormLinear 0 (outsideHankelLocalCoord 0) = _
        rw [← (localTwoFormLinear 0).map_smul,
          ← (localTwoFormLinear 0).map_smul,
          ← (localTwoFormLinear 0).map_add]
        rfl
      _ = localTwoForm 0 (closedPlaceTargetCoord 0 z) := by
        congr 1
        funext s
        fin_cases s <;>
          simp [rationalEvaluationLocalCoord, outsideHankelLocalCoord,
            closedPlaceTargetCoord]
  · calc
      targetTwo (closedPlaceTargetCoeff 1 z) =
          z 0 • targetTwo rOneCoeff +
            z 1 • targetTwo (outsideHankelWord 3) := by
        change targetTwoLinear (z 0 • rOneCoeff +
          z 1 • outsideHankelWord 3) = _
        simp [targetTwo]
      _ = z 0 • localTwoForm 1 rationalEvaluationLocalCoord +
          z 1 • localTwoForm 1 (outsideHankelLocalCoord 3) := by
        rw [targetTwo_rOne_eq_local, targetTwo_outsideHankelWord]
        rfl
      _ = localTwoForm 1
          (z 0 • rationalEvaluationLocalCoord +
            z 1 • outsideHankelLocalCoord 3) := by
        change z 0 • localTwoFormLinear 1 rationalEvaluationLocalCoord +
          z 1 • localTwoFormLinear 1 (outsideHankelLocalCoord 3) = _
        rw [← (localTwoFormLinear 1).map_smul,
          ← (localTwoFormLinear 1).map_smul,
          ← (localTwoFormLinear 1).map_add]
        rfl
      _ = localTwoForm 1 (closedPlaceTargetCoord 1 z) := by
        congr 1
        funext s
        fin_cases s <;>
          simp [rationalEvaluationLocalCoord, outsideHankelLocalCoord,
            closedPlaceTargetCoord]
  · calc
      targetTwo (closedPlaceTargetCoeff 2 z) =
          z 0 • targetTwo rInfinityCoeff +
            z 1 • targetTwo (outsideHankelWord 5) := by
        change targetTwoLinear (z 0 • rInfinityCoeff +
          z 1 • outsideHankelWord 5) = _
        simp [targetTwo]
      _ = z 0 • localTwoForm 2 rationalEvaluationLocalCoord +
          z 1 • localTwoForm 2 (outsideHankelLocalCoord 5) := by
        rw [targetTwo_rInfinity_eq_local, targetTwo_outsideHankelWord]
        rfl
      _ = localTwoForm 2
          (z 0 • rationalEvaluationLocalCoord +
            z 1 • outsideHankelLocalCoord 5) := by
        change z 0 • localTwoFormLinear 2 rationalEvaluationLocalCoord +
          z 1 • localTwoFormLinear 2 (outsideHankelLocalCoord 5) = _
        rw [← (localTwoFormLinear 2).map_smul,
          ← (localTwoFormLinear 2).map_smul,
          ← (localTwoFormLinear 2).map_add]
        rfl
      _ = localTwoForm 2 (closedPlaceTargetCoord 2 z) := by
        congr 1
        funext s
        fin_cases s <;>
          simp [rationalEvaluationLocalCoord, outsideHankelLocalCoord,
            closedPlaceTargetCoord]
  · calc
      targetTwo (closedPlaceTargetCoeff 3 z) =
          z 0 • targetTwo (outsideHankelWord 8) +
            z 1 • targetTwo (outsideHankelWord 7) := by
        change targetTwoLinear (z 0 • outsideHankelWord 8 +
          z 1 • outsideHankelWord 7) = _
        simp [targetTwo]
      _ = z 0 • localTwoForm 3 (outsideHankelLocalCoord 8) +
          z 1 • localTwoForm 3 (outsideHankelLocalCoord 7) := by
        rw [targetTwo_outsideHankelWord, targetTwo_outsideHankelWord]
        rfl
      _ = localTwoForm 3
          (z 0 • outsideHankelLocalCoord 8 +
            z 1 • outsideHankelLocalCoord 7) := by
        change z 0 • localTwoFormLinear 3 (outsideHankelLocalCoord 8) +
          z 1 • localTwoFormLinear 3 (outsideHankelLocalCoord 7) = _
        rw [← (localTwoFormLinear 3).map_smul,
          ← (localTwoFormLinear 3).map_smul,
          ← (localTwoFormLinear 3).map_add]
        rfl
      _ = localTwoForm 3 (closedPlaceTargetCoord 3 z) := by
        congr 1
        funext s
        fin_cases s <;>
          simp [outsideHankelLocalCoord, closedPlaceTargetCoord]

/-- The global quotient of a local Klein point is its extracted canonical
closed-place quotient parameter. -/
theorem quadraticQuotientProjection_localTwoForm (place : Fin 4)
    (p : LocalKleinCoord) :
    quadraticQuotientProjection (localTwoForm place p) =
      closedPlaceQuotientPoint place (closedPlaceQuotientParam place p) := by
  let q := closedPlaceQuotientParam place p
  let z := closedPlaceTargetParam place p
  calc
    quadraticQuotientProjection (localTwoForm place p) =
        quadraticQuotientProjection
          (localTwoForm place (closedPlaceLocalPoint place q z)) := by
      rw [closedPlaceLocalPoint_extracted]
    _ = quadraticQuotientProjection
        (localTwoForm place
          (closedPlaceCanonicalCoord place q +
            closedPlaceTargetCoord place z)) := by
      rw [closedPlaceLocalPoint_eq_canonical_add_target]
    _ = quadraticQuotientProjection
        (closedPlaceLift place q + targetTwo (closedPlaceTargetCoeff place z)) := by
      apply congrArg quadraticQuotientProjection
      change localTwoFormLinear place
          (closedPlaceCanonicalCoord place q +
            closedPlaceTargetCoord place z) = _
      rw [(localTwoFormLinear place).map_add]
      change localTwoForm place (closedPlaceCanonicalCoord place q) +
          localTwoForm place (closedPlaceTargetCoord place z) = _
      rw [← targetTwo_closedPlaceTargetCoeff]
      rfl
    _ = closedPlaceQuotientPoint place q := by
      simp [closedPlaceQuotientPoint]

/-- The Klein equation is also sufficient for decomposability in the local
four-space.  This certificate ranges only over the six local Pluecker bits and
four-coordinate factors; it does not enumerate ambient forms or circuits. -/
theorem exists_localWedgeCoord_of_satisfiesKlein (p : LocalKleinCoord)
    (hp : SatisfiesKlein p) :
    ∃ u v : LocalKleinParam, p = localWedgeCoord u v := by
  letI : DecidableEq LocalKleinCoord := Fintype.decidablePiFintype
  letI : DecidablePred (fun p : LocalKleinCoord =>
      SatisfiesKlein p →
        ∃ u v : LocalKleinParam, p = localWedgeCoord u v) :=
    fun _ => inferInstance
  have hall : ∀ p : LocalKleinCoord, SatisfiesKlein p →
      ∃ u v : LocalKleinParam, p = localWedgeCoord u v :=
    @of_decide_eq_true _ Fintype.decidableForallFintype rfl
  exact hall p hp

/-- A local point on the Klein quadric gives an honest decomposable ambient
two-form after synthesis in the displayed closed-place basis. -/
theorem localTwoForm_decomposable_of_satisfiesKlein (place : Fin 4)
    (p : LocalKleinCoord) (hp : SatisfiesKlein p) :
    IsDecomposableTwo (localTwoForm place p) := by
  rcases exists_localWedgeCoord_of_satisfiesKlein p hp with ⟨u, v, huv⟩
  refine ⟨∑ i : Fin 4, u i • closedPlaceLocalBasis place i,
    ∑ i : Fin 4, v i • closedPlaceLocalBasis place i, ?_⟩
  rw [huv, localTwoForm_localWedgeCoord]

theorem closedPlaceQuotientParam_localPoint (place : Fin 4)
    (q : LocalKleinParam) (z : LocalTargetParam) :
    closedPlaceQuotientParam place (closedPlaceLocalPoint place q z) = q := by
  funext i
  fin_cases place <;> fin_cases i <;>
    simp [closedPlaceQuotientParam, closedPlaceLocalPoint,
      rationalQuotientParam, degreeTwoQuotientParam,
      rationalLocalPoint, degreeTwoLocalPoint]
  all_goals ring_nf
  all_goals simp [N3Certificate.two_eq_zero_f2]

/-- Two points in one local affine fiber differ by the corresponding target
translation. -/
theorem closedPlaceLocalPoint_add (place : Fin 4) (q : LocalKleinParam)
    (z w : LocalTargetParam) :
    closedPlaceLocalPoint place q z + closedPlaceLocalPoint place q w =
      closedPlaceTargetCoord place (z + w) := by
  funext i
  fin_cases place <;> fin_cases i <;>
    simp [closedPlaceLocalPoint, closedPlaceTargetCoord,
      rationalLocalPoint, degreeTwoLocalPoint]
  all_goals ring_nf
  all_goals simp [N3Certificate.two_eq_zero_f2]

/-- Every rational evaluation word has constant coordinates from positions
one through seven.  Three coordinates suffice below to certify that each
non-rational local target displacement is genuinely outside `R`. -/
theorem rationalCoeffSpace_selected_coordinates {c : TargetCoeff}
    (hc : c ∈ rationalCoeffSpace) :
    c 1 = c 2 ∧ c 1 = c 3 ∧ c 1 = c 7 := by
  refine Submodule.span_induction
    (p := fun c _ => c 1 = c 2 ∧ c 1 = c 3 ∧ c 1 = c 7)
    ?_ ?_ ?_ ?_ hc
  · intro d hd
    rcases hd with rfl | rfl | rfl <;>
      simp [rZeroCoeff, rOneCoeff, rInfinityCoeff]
  · simp
  · rintro x y _ _ ⟨h12x, h13x, h17x⟩ ⟨h12y, h13y, h17y⟩
    simp only [Pi.add_apply]
    exact ⟨by rw [h12x, h12y], by rw [h13x, h13y],
      by rw [h17x, h17y]⟩
  · rintro a x _ ⟨h12, h13, h17⟩
    simp only [Pi.smul_apply]
    exact ⟨by rw [h12], by rw [h13], by rw [h17]⟩

/-- A rational-place local displacement with nonzero jet coordinate is not a
rational evaluation word. -/
theorem rational_closedPlaceTargetCoeff_not_mem (place : Fin 3)
    (z : LocalTargetParam) (hz : z 1 ≠ 0) :
    closedPlaceTargetCoeff place.castSucc z ∉ rationalCoeffSpace := by
  intro hmem
  rcases rationalCoeffSpace_selected_coordinates hmem with
    ⟨h12, h13, h17⟩
  fin_cases place
  · have hzero : z 1 = 0 := by
      simpa [closedPlaceTargetCoeff, outsideHankelWord,
        rankTwoHankelWord, jZeroCoeff, rZeroCoeff, rOneCoeff,
        rInfinityCoeff, N3Certificate.two_eq_zero_f2,
        CharTwo.add_self_eq_zero, eq_comm] using h12
    exact hz hzero
  · have hzero : z 1 = 0 := by
      simpa [closedPlaceTargetCoeff, outsideHankelWord,
        rankTwoHankelWord, jOneCoeff, rZeroCoeff, rOneCoeff,
        rInfinityCoeff, N3Certificate.two_eq_zero_f2,
        CharTwo.add_self_eq_zero, eq_comm] using h12
    exact hz hzero
  · have hzero : z 1 = 0 := by
      simpa [closedPlaceTargetCoeff, outsideHankelWord,
        rankTwoHankelWord, jInfinityCoeff, rZeroCoeff, rOneCoeff,
        rInfinityCoeff, N3Certificate.two_eq_zero_f2,
        CharTwo.add_self_eq_zero, eq_comm] using h17
    exact hz hzero

/-- Every nonzero degree-two target displacement is outside the rational
evaluation space. -/
theorem degreeTwo_closedPlaceTargetCoeff_not_mem (z : LocalTargetParam)
    (hz : z ≠ 0) :
    closedPlaceTargetCoeff 3 z ∉ rationalCoeffSpace := by
  intro hmem
  rcases rationalCoeffSpace_selected_coordinates hmem with
    ⟨h12, h13, _h17⟩
  have hz0 : z 0 = 0 := by
    simpa [closedPlaceTargetCoeff, outsideHankelWord,
      rankTwoHankelWord, dStarZeroCoeff, dStarOneCoeff,
      rZeroCoeff, rOneCoeff, rInfinityCoeff,
      N3Certificate.two_eq_zero_f2, CharTwo.add_self_eq_zero,
      eq_comm] using h12
  have hz1 : z 1 = 0 := by
    simpa [closedPlaceTargetCoeff, outsideHankelWord,
      rankTwoHankelWord, dStarZeroCoeff, dStarOneCoeff,
      rZeroCoeff, rOneCoeff, rInfinityCoeff, hz0,
      N3Certificate.two_eq_zero_f2, CharTwo.add_self_eq_zero,
      eq_comm] using h13
  apply hz
  funext i
  fin_cases i <;> assumption

/-- Four independent coordinate factors for the doubled-point jet form. -/
def jetFactorCoord : Fin 4 → LocalKleinParam :=
  ![![1, 0, 0, 0], ![0, 0, 0, 1],
    ![0, 1, 0, 0], ![0, 0, 1, 0]]

/-- Four independent coordinate factors for `b+c+d`. -/
def mixedFactorCoord : Fin 4 → LocalKleinParam :=
  ![![1, 0, 0, 0], ![0, 0, 1, 1],
    ![0, 1, 0, 0], ![0, 0, 1, 0]]

/-- Four independent coordinate factors for `c+d+e`. -/
def degreeTwoOneFactorCoord : Fin 4 → LocalKleinParam :=
  ![![1, 0, 0, 0], ![0, 0, 0, 1],
    ![0, 1, 0, 0], ![0, 0, 1, 1]]

/-- Four independent coordinate factors for `b+e`. -/
def degreeTwoZeroFactorCoord : Fin 4 → LocalKleinParam :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0],
    ![0, 1, 0, 0], ![0, 0, 0, 1]]

/-- Coordinate factors for all nine non-rational Hankel normal forms. -/
def outsideHankelFactorCoord : Fin 9 → Fin 4 → LocalKleinParam :=
  ![jetFactorCoord, mixedFactorCoord, mixedFactorCoord,
    jetFactorCoord, mixedFactorCoord, jetFactorCoord,
    mixedFactorCoord, degreeTwoOneFactorCoord,
    degreeTwoZeroFactorCoord]

/-- The four coordinate factors are independent in every row. -/
theorem outsideHankelFactorCoord_linearIndependent (k : Fin 9) :
    LinearIndependent F₂ (outsideHankelFactorCoord k) := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  fin_cases k <;>
    simp [outsideHankelFactorCoord, jetFactorCoord, mixedFactorCoord,
      degreeTwoOneFactorCoord, degreeTwoZeroFactorCoord,
      Fin.sum_univ_succ] at h0 h1 h2 h3
  all_goals fin_cases i <;> simp_all

/-- Synthesis from displayed local coordinates into the ambient linear
space. -/
def closedPlaceSynthesis (place : Fin 4) :
    LocalKleinParam →ₗ[F₂] LinearForm :=
  (closedPlaceLinearSpace place).subtype.comp
    (closedPlaceBasis place).equivFun.symm.toLinearMap

theorem closedPlaceSynthesis_apply (place : Fin 4) (u : LocalKleinParam) :
    closedPlaceSynthesis place u =
      ∑ i : Fin 4, u i • closedPlaceLocalBasis place i := by
  calc
    closedPlaceSynthesis place u =
        ∑ i : Fin 4, u i •
          ((closedPlaceBasis place i : closedPlaceLinearSpace place) :
            LinearForm) := by
      simp [closedPlaceSynthesis, Module.Basis.equivFun_symm_apply]
    _ = ∑ i : Fin 4, u i • closedPlaceLocalBasis place i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact Module.Basis.coe_span_apply
        (closedPlaceLocalBasis_linearIndependent place) i

theorem closedPlaceSynthesis_injective (place : Fin 4) :
    Function.Injective (closedPlaceSynthesis place) := by
  intro u v h
  apply (closedPlaceBasis place).equivFun.symm.injective
  apply Subtype.ext
  exact h

/-- Ambient linear factors of one non-rational Hankel normal form. -/
def outsideHankelFactor (k : Fin 9) : Fin 4 → LinearForm :=
  fun r => closedPlaceSynthesis (outsideHankelPlace k)
    (outsideHankelFactorCoord k r)

theorem outsideHankelFactor_linearIndependent (k : Fin 9) :
    LinearIndependent F₂ (outsideHankelFactor k) := by
  have h := (outsideHankelFactorCoord_linearIndependent k).map'
    (closedPlaceSynthesis (outsideHankelPlace k))
    (LinearMap.ker_eq_bot_of_injective
      (closedPlaceSynthesis_injective (outsideHankelPlace k)))
  change LinearIndependent F₂ (fun x =>
    closedPlaceSynthesis (outsideHankelPlace k)
      (outsideHankelFactorCoord k x))
  exact h

/-- The tabulated local two-form is the sum of the wedges of its first and
second pair of factors. -/
theorem outsideHankelLocalCoord_secant (k : Fin 9) :
    outsideHankelLocalCoord k =
      localWedgeCoord (outsideHankelFactorCoord k 0)
          (outsideHankelFactorCoord k 1) +
        localWedgeCoord (outsideHankelFactorCoord k 2)
          (outsideHankelFactorCoord k 3) := by
  funext s
  fin_cases k <;> fin_cases s <;>
    decide

/-- Secant presentation of a non-rational Hankel normal form in its local
four-space. -/
theorem localTwoForm_outsideHankelLocalCoord (k : Fin 9) :
    localTwoForm (outsideHankelPlace k) (outsideHankelLocalCoord k) =
      squarefreeWedge (outsideHankelFactor k 0)
          (outsideHankelFactor k 1) +
        squarefreeWedge (outsideHankelFactor k 2)
          (outsideHankelFactor k 3) := by
  rw [outsideHankelLocalCoord_secant]
  calc
    localTwoForm (outsideHankelPlace k)
        (localWedgeCoord (outsideHankelFactorCoord k 0)
            (outsideHankelFactorCoord k 1) +
          localWedgeCoord (outsideHankelFactorCoord k 2)
            (outsideHankelFactorCoord k 3)) =
        localTwoForm (outsideHankelPlace k)
            (localWedgeCoord (outsideHankelFactorCoord k 0)
              (outsideHankelFactorCoord k 1)) +
          localTwoForm (outsideHankelPlace k)
            (localWedgeCoord (outsideHankelFactorCoord k 2)
              (outsideHankelFactorCoord k 3)) :=
      (localTwoFormLinear (outsideHankelPlace k)).map_add _ _
    _ = _ := by
      rw [localTwoForm_localWedgeCoord,
        localTwoForm_localWedgeCoord]
      simp only [outsideHankelFactor, closedPlaceSynthesis_apply]

/-- Secant presentation of the corresponding global target word. -/
theorem targetTwo_outsideHankelWord_secant (k : Fin 9) :
    targetTwo (outsideHankelWord k) =
      squarefreeWedge (outsideHankelFactor k 0)
          (outsideHankelFactor k 1) +
        squarefreeWedge (outsideHankelFactor k 2)
          (outsideHankelFactor k 3) :=
  (targetTwo_outsideHankelWord k).trans
    (localTwoForm_outsideHankelLocalCoord k)

theorem closedPlaceSynthesis_mem (place : Fin 4) (u : LocalKleinParam) :
    closedPlaceSynthesis place u ∈ closedPlaceLinearSpace place := by
  change ((closedPlaceLinearSpace place).subtype
    ((closedPlaceBasis place).equivFun.symm u)) ∈
      closedPlaceLinearSpace place
  exact ((closedPlaceBasis place).equivFun.symm u).property

/-- The four secant factors span the whole local four-space. -/
theorem outsideHankelFactor_span (k : Fin 9) :
    Submodule.span F₂ (Set.range (outsideHankelFactor k)) =
      closedPlaceLinearSpace (outsideHankelPlace k) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    exact closedPlaceSynthesis_mem _ _
  · rw [finrank_span_eq_card (outsideHankelFactor_linearIndependent k),
      closedPlaceLinearSpace_finrank]
    rfl

/-- Every non-rational rank-two Hankel normal form has exactly the displayed
four-dimensional closed-place support. -/
theorem quadraticSupport_outsideHankelWord (k : Fin 9) :
    quadraticSupport (targetTwo (outsideHankelWord k)) =
      closedPlaceLinearSpace (outsideHankelPlace k) := by
  have hvec :
      (![outsideHankelFactor k 0, outsideHankelFactor k 1,
          outsideHankelFactor k 2, outsideHankelFactor k 3] :
        Fin 4 → LinearForm) = outsideHankelFactor k := by
    funext r
    fin_cases r <;> rfl
  have hlin : LinearIndependent F₂
      (![outsideHankelFactor k 0, outsideHankelFactor k 1,
          outsideHankelFactor k 2, outsideHankelFactor k 3] :
        Fin 4 → LinearForm) := by
    rw [hvec]
    exact outsideHankelFactor_linearIndependent k
  have hsupport :
      quadraticSupport
          (squarefreeWedge (outsideHankelFactor k 0)
              (outsideHankelFactor k 1) +
            squarefreeWedge (outsideHankelFactor k 2)
              (outsideHankelFactor k 3)) =
        Submodule.span F₂ (Set.range (outsideHankelFactor k)) := by
    rw [quadraticSupport_two_wedges _ _ _ _ hlin, hvec]
  calc
    quadraticSupport (targetTwo (outsideHankelWord k)) =
        quadraticSupport
          (squarefreeWedge (outsideHankelFactor k 0)
              (outsideHankelFactor k 1) +
            squarefreeWedge (outsideHankelFactor k 2)
              (outsideHankelFactor k 3)) :=
      congrArg quadraticSupport (targetTwo_outsideHankelWord_secant k)
    _ = Submodule.span F₂ (Set.range (outsideHankelFactor k)) :=
      hsupport
    _ = closedPlaceLinearSpace (outsideHankelPlace k) :=
      outsideHankelFactor_span k

/-- If a two-wedge secant has a four-dimensional support, all four factors
belong to that support. -/
theorem secant_factors_mem_support (K : Submodule F₂ LinearForm)
    (hK : Module.finrank F₂ K = 4) (u v x y : LinearForm)
    (hsupport :
      quadraticSupport (squarefreeWedge u v + squarefreeWedge x y) = K) :
    u ∈ K ∧ v ∈ K ∧ x ∈ K ∧ y ∈ K := by
  have hrank : Module.finrank F₂
      (quadraticSupport (squarefreeWedge u v + squarefreeWedge x y)) = 4 := by
    rw [hsupport, hK]
  have hlin := linearIndependent_of_two_wedge_support_finrank_four
    u v x y hrank
  have hspan :
      Submodule.span F₂ (Set.range ![u, v, x, y]) = K := by
    rw [← quadraticSupport_two_wedges u v x y hlin, hsupport]
  have hu : u ∈ Submodule.span F₂ (Set.range ![u, v, x, y]) :=
    Submodule.subset_span ⟨0, rfl⟩
  have hv : v ∈ Submodule.span F₂ (Set.range ![u, v, x, y]) :=
    Submodule.subset_span ⟨1, rfl⟩
  have hx : x ∈ Submodule.span F₂ (Set.range ![u, v, x, y]) :=
    Submodule.subset_span ⟨2, rfl⟩
  have hy : y ∈ Submodule.span F₂ (Set.range ![u, v, x, y]) :=
    Submodule.subset_span ⟨3, rfl⟩
  rw [hspan] at hu hv hx hy
  exact ⟨hu, hv, hx, hy⟩

/-- Both endpoints of a secant with one of the nine non-rational Hankel
differences acquire Pluecker coordinates in the corresponding local
four-space. -/
theorem outsideHankel_secant_localizes (k : Fin 9) (u v x y : LinearForm)
    (hsecant : targetTwo (outsideHankelWord k) =
      squarefreeWedge u v + squarefreeWedge x y) :
    ∃ p p' : LocalKleinCoord,
      SatisfiesKlein p ∧ SatisfiesKlein p' ∧
      p + p' = outsideHankelLocalCoord k ∧
      localTwoForm (outsideHankelPlace k) p = squarefreeWedge u v ∧
      localTwoForm (outsideHankelPlace k) p' = squarefreeWedge x y := by
  have hsupport :
      quadraticSupport (squarefreeWedge u v + squarefreeWedge x y) =
        closedPlaceLinearSpace (outsideHankelPlace k) := by
    rw [← hsecant, quadraticSupport_outsideHankelWord]
  rcases secant_factors_mem_support
      (closedPlaceLinearSpace (outsideHankelPlace k))
      (closedPlaceLinearSpace_finrank (outsideHankelPlace k))
      u v x y hsupport with ⟨hu, hv, hx, hy⟩
  rcases exists_satisfiesKlein_of_factors_mem
      (outsideHankelPlace k) u v hu hv with ⟨p, hkp, hp⟩
  rcases exists_satisfiesKlein_of_factors_mem
      (outsideHankelPlace k) x y hx hy with ⟨p', hkp', hp'⟩
  have hcoord : outsideHankelLocalCoord k = p + p' :=
    localTwoForm_injective (outsideHankelPlace k) (by
      calc
        localTwoForm (outsideHankelPlace k) (outsideHankelLocalCoord k) =
            targetTwo (outsideHankelWord k) :=
          (targetTwo_outsideHankelWord k).symm
        _ = squarefreeWedge u v + squarefreeWedge x y := hsecant
        _ = localTwoForm (outsideHankelPlace k) p +
            localTwoForm (outsideHankelPlace k) p' := by rw [hp, hp']
        _ = localTwoForm (outsideHankelPlace k) (p + p') :=
          ((localTwoFormLinear (outsideHankelPlace k)).map_add p p').symm)
  exact ⟨p, p', hkp, hkp', hcoord.symm, hp, hp'⟩

/-! ## Exact effective-fiber classification -/

/-- A populated quotient fiber is effective when two decomposable points in
it differ by a target word outside the rational evaluation space. -/
def IsEffectiveFiber (q : QuadraticQuotient) : Prop :=
  ∃ p p' : TwoForm, p ∈ decomposableFiber q ∧
    p' ∈ decomposableFiber q ∧
    ∃ c : TargetCoeff, c ∉ rationalCoeffSpace ∧
      targetTwo c = p + p'

/-- Package the nine-way outside-rational Hankel classification with the
local normal-form index used by the atlas. -/
theorem exists_outsideHankelWord_of_rankTwo {c : TargetCoeff}
    (hrank : HankelRankLETwo c) (hc : c ∉ rationalCoeffSpace) :
    ∃ k : Fin 9, c = outsideHankelWord k := by
  rcases rankTwoHankel_outside_rational_classification hrank hc with
    h | h | h | h | h | h | h | h | h
  · exact ⟨0, by simpa [outsideHankelWord] using h⟩
  · exact ⟨1, by simpa [outsideHankelWord] using h⟩
  · exact ⟨2, by simpa [outsideHankelWord] using h⟩
  · exact ⟨3, by simpa [outsideHankelWord] using h⟩
  · exact ⟨4, by simpa [outsideHankelWord] using h⟩
  · exact ⟨5, by simpa [outsideHankelWord] using h⟩
  · exact ⟨6, by simpa [outsideHankelWord] using h⟩
  · exact ⟨7, by simpa [outsideHankelWord] using h⟩
  · exact ⟨8, by simpa [outsideHankelWord] using h⟩

/-- Exhaustiveness: every effective fiber localizes to one of the 43
closed-place atlas points. -/
theorem effectiveFiber_mem_atlas {q : QuadraticQuotient}
    (hq : IsEffectiveFiber q) : q ∈ effectiveFiberAtlas := by
  classical
  rcases hq with ⟨p, p', hp, hp', c, hc, hsum⟩
  rcases hp with ⟨⟨u, v, huv⟩, hpq⟩
  rcases hp' with ⟨⟨x, y, hxy⟩, hp'q⟩
  rw [huv, hxy] at hsum
  have hrank : HankelRankLETwo c :=
    target_sum_two_decomposable_rankTwo hsum
  rcases exists_outsideHankelWord_of_rankTwo hrank hc with ⟨k, rfl⟩
  rcases outsideHankel_secant_localizes k u v x y hsum with
    ⟨r, r', hr, hr', hadd, hlocal, hlocal'⟩
  have heffective :
      closedPlaceQuotientParam (outsideHankelPlace k) r ∈
        effectiveParamsAt (outsideHankelPlace k) :=
    outsideHankel_localEffectiveParam k r r' hr hr' hadd
  have hqeq : q = closedPlaceQuotientPoint (outsideHankelPlace k)
      (closedPlaceQuotientParam (outsideHankelPlace k) r) := by
    calc
      q = quadraticQuotientProjection p := hpq.symm
      _ = quadraticQuotientProjection (localTwoForm
          (outsideHankelPlace k) r) := by rw [huv, hlocal]
      _ = closedPlaceQuotientPoint (outsideHankelPlace k)
          (closedPlaceQuotientParam (outsideHankelPlace k) r) :=
        quadraticQuotientProjection_localTwoForm _ _
  rw [effectiveFiberAtlas, Finset.mem_image]
  refine ⟨⟨outsideHankelPlace k,
    ⟨closedPlaceQuotientParam (outsideHankelPlace k) r, heffective⟩⟩,
    Finset.mem_univ _, ?_⟩
  exact hqeq.symm

/-- Turn two local Klein points in one affine chart into two decomposable
ambient points in the same global quotient fiber. -/
theorem closedPlace_effective_of_local_difference (place : Fin 4)
    (q : LocalKleinParam) (z w : LocalTargetParam)
    (hz : SatisfiesKlein (closedPlaceLocalPoint place q z))
    (hw : SatisfiesKlein (closedPlaceLocalPoint place q w))
    (hout : closedPlaceTargetCoeff place (z + w) ∉ rationalCoeffSpace) :
    IsEffectiveFiber (closedPlaceQuotientPoint place q) := by
  let p := localTwoForm place (closedPlaceLocalPoint place q z)
  let p' := localTwoForm place (closedPlaceLocalPoint place q w)
  refine ⟨p, p', ?_, ?_, closedPlaceTargetCoeff place (z + w), hout, ?_⟩
  · refine ⟨localTwoForm_decomposable_of_satisfiesKlein _ _ hz, ?_⟩
    rw [quadraticQuotientProjection_localTwoForm,
      closedPlaceQuotientParam_localPoint]
  · refine ⟨localTwoForm_decomposable_of_satisfiesKlein _ _ hw, ?_⟩
    rw [quadraticQuotientProjection_localTwoForm,
      closedPlaceQuotientParam_localPoint]
  · calc
      targetTwo (closedPlaceTargetCoeff place (z + w)) =
          localTwoForm place (closedPlaceTargetCoord place (z + w)) :=
        targetTwo_closedPlaceTargetCoeff place (z + w)
      _ = localTwoForm place
          (closedPlaceLocalPoint place q z +
            closedPlaceLocalPoint place q w) := by
        rw [closedPlaceLocalPoint_add]
      _ = p + p' := (localTwoFormLinear place).map_add _ _

theorem rational_closedPlaceQuotientPoint_effective (place : Fin 3)
    (q : LocalKleinParam) (hq : RationalLocalEffective q) :
    IsEffectiveFiber (closedPlaceQuotientPoint place.castSucc q) := by
  rcases (rationalHasJetDifference_iff q).2 hq with
    ⟨z, hz, w, hw, hzw⟩
  have hzK : SatisfiesKlein (rationalLocalPoint q z) := by
    simpa [rationalKleinFiber] using hz
  have hwK : SatisfiesKlein (rationalLocalPoint q w) := by
    simpa [rationalKleinFiber] using hw
  have hd : (z + w) 1 ≠ 0 := by
    intro hzero
    apply hzw
    rw [← sub_eq_zero]
    simpa only [Pi.add_apply, CharTwo.sub_eq_add] using hzero
  fin_cases place
  · exact closedPlace_effective_of_local_difference 0 q z w
      (by simpa [closedPlaceLocalPoint] using hzK)
      (by simpa [closedPlaceLocalPoint] using hwK)
      (rational_closedPlaceTargetCoeff_not_mem 0 (z + w) hd)
  · exact closedPlace_effective_of_local_difference 1 q z w
      (by simpa [closedPlaceLocalPoint] using hzK)
      (by simpa [closedPlaceLocalPoint] using hwK)
      (rational_closedPlaceTargetCoeff_not_mem 1 (z + w) hd)
  · exact closedPlace_effective_of_local_difference 2 q z w
      (by simpa [closedPlaceLocalPoint] using hzK)
      (by simpa [closedPlaceLocalPoint] using hwK)
      (rational_closedPlaceTargetCoeff_not_mem 2 (z + w) hd)

theorem degreeTwo_closedPlaceQuotientPoint_effective (q : LocalKleinParam)
    (hq : DegreeTwoLocalEffective q) :
    IsEffectiveFiber (closedPlaceQuotientPoint 3 q) := by
  rcases (degreeTwoHasDifference_iff q).2 hq with
    ⟨z, hz, w, hw, hzw⟩
  have hzK : SatisfiesKlein (degreeTwoLocalPoint q z) := by
    simpa [degreeTwoKleinFiber] using hz
  have hwK : SatisfiesKlein (degreeTwoLocalPoint q w) := by
    simpa [degreeTwoKleinFiber] using hw
  have hd : z + w ≠ 0 := by
    intro hzero
    apply hzw
    apply sub_eq_zero.mp
    funext i
    have hi := congrFun hzero i
    simpa only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply,
      CharTwo.sub_eq_add] using hi
  exact closedPlace_effective_of_local_difference 3 q z w
    (by simpa [closedPlaceLocalPoint] using hzK)
    (by simpa [closedPlaceLocalPoint] using hwK)
    (degreeTwo_closedPlaceTargetCoeff_not_mem (z + w) hd)

/-- Every point of the displayed atlas is effective. -/
theorem effectiveFiber_of_mem_atlas {q : QuadraticQuotient}
    (hq : q ∈ effectiveFiberAtlas) : IsEffectiveFiber q := by
  classical
  rw [effectiveFiberAtlas, Finset.mem_image] at hq
  rcases hq with ⟨⟨place, ⟨r, hr⟩⟩, _, rfl⟩
  fin_cases place
  · apply rational_closedPlaceQuotientPoint_effective 0 r
    simpa [effectiveParamsAt, rationalEffectiveParams] using hr
  · apply rational_closedPlaceQuotientPoint_effective 1 r
    simpa [effectiveParamsAt, rationalEffectiveParams] using hr
  · apply rational_closedPlaceQuotientPoint_effective 2 r
    simpa [effectiveParamsAt, rationalEffectiveParams] using hr
  · apply degreeTwo_closedPlaceQuotientPoint_effective r
    simpa [effectiveParamsAt, degreeTwoEffectiveParams] using hr

/-- Exact pointwise classification of effective quotient fibers. -/
theorem isEffectiveFiber_iff_mem_atlas (q : QuadraticQuotient) :
    IsEffectiveFiber q ↔ q ∈ effectiveFiberAtlas :=
  ⟨effectiveFiber_mem_atlas, effectiveFiber_of_mem_atlas⟩

/-- The actual finite set of effective quotient fibers. -/
noncomputable def effectiveFibers : Finset QuadraticQuotient := by
  classical
  exact Finset.univ.filter IsEffectiveFiber

/-- Manuscript Theorem 5.3: the effective fibers are exactly the four
closed-place charts displayed by the atlas. -/
theorem effectiveFibers_eq : effectiveFibers = effectiveFiberAtlas := by
  classical
  ext q
  simp [effectiveFibers, isEffectiveFiber_iff_mem_atlas]

/-- In particular, there are exactly 43 effective nonzero quotient points. -/
theorem effectiveFibers_card : effectiveFibers.card = 43 := by
  rw [effectiveFibers_eq, effectiveFiberAtlas_card]

end

end N5
end UnrestrictedBooleanMul
