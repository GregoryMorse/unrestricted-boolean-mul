import UnrestrictedBooleanMul.N5.TargetClean

/-!
# The target-clean retained cross matrix

This module isolates the small symbolic matrix contradiction in manuscript
Lemma 11.4.  After deleting the zero-place extension row and column, every
member of the affine target family `tau + U` has the displayed symmetric
`4 x 4` form.  The form is never a symmetric rank-one matrix.

The proof follows the two manuscript branches `a = 0` and `a = 1`; it is not
a finite table lookup.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Exact first jet at the rational place one, before the harmless rational
adjustment used by the closed-place atlas. -/
def exactJOneCoeff : TargetCoeff :=
  ![0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- Exact first jet at infinity. -/
def exactJInfinityCoeff : TargetCoeff :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- The exact eight directions in the manuscript definition of `U`. -/
def exactFirstOrderDirections : Fin 8 → TargetCoeff :=
  ![rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
    exactJOneCoeff, exactJInfinityCoeff, dStarZeroCoeff, dStarOneCoeff]

theorem exactFirstOrderDirection_mem (i : Fin 8) :
    exactFirstOrderDirections i ∈ firstOrderEnvelopeCoeffSpace := by
  rw [mem_firstOrderEnvelopeCoeffSpace]
  fin_cases i <;>
    decide

theorem exactFirstOrderDirections_linearIndependent :
    LinearIndependent F₂ exactFirstOrderDirections := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  have h0 := congrFun h (0 : Fin 9)
  have h1 := congrFun h (1 : Fin 9)
  have h2 := congrFun h (2 : Fin 9)
  have h3 := congrFun h (3 : Fin 9)
  have h4 := congrFun h (4 : Fin 9)
  have h5 := congrFun h (5 : Fin 9)
  have h6 := congrFun h (6 : Fin 9)
  have h7 := congrFun h (7 : Fin 9)
  have h8 := congrFun h (8 : Fin 9)
  simp [exactFirstOrderDirections, exactJOneCoeff, exactJInfinityCoeff,
    rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
    dStarZeroCoeff, dStarOneCoeff, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hf1 : f 1 = 0 := h4
  have hf0 : f 0 = 0 := by simpa [hf1] using h0
  have hf2 : f 2 = 0 := by simpa [hf1] using h8
  have hf6 : f 6 = 0 := by simpa [hf1] using h2
  have hf7 : f 7 = 0 := by simpa [hf1] using h6
  have hf4 : f 4 = 0 := by simpa [hf1, hf6] using h5
  have hf3 : f 3 = 0 := by simpa [hf1, hf4] using h1
  have hf5 : f 5 = 0 := by simpa [hf1, hf4] using h7
  fin_cases i <;> assumption

/-- The exact manuscript directions span the previously defined
first-order envelope. -/
theorem span_exactFirstOrderDirections_eq :
    Submodule.span F₂ (Set.range exactFirstOrderDirections) =
      firstOrderEnvelopeCoeffSpace := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro c ⟨i, rfl⟩
    exact exactFirstOrderDirection_mem i
  · rw [finrank_span_eq_card exactFirstOrderDirections_linearIndependent,
      closedPlaceCoeffSpace_finrank]
    simp

/-- Seven visible parameters on the retained cross block, ordered as
`a,b,c,d,e,f,g` in the manuscript.  The eighth direction `j_0` disappears
after deleting its row and column. -/
def targetCleanProjectedMatrix (s : Fin 7 → F₂) :
    Fin 4 → Fin 4 → F₂ :=
  ![![s 5 + s 0, 1 + s 0 + s 1, s 0 + s 2 + s 3, s 0],
    ![1 + s 0 + s 1, s 0, s 0 + s 1 + s 3, s 0 + s 2],
    ![s 0 + s 2 + s 3, s 0 + s 1 + s 3, s 0 + s 2,
      s 0 + s 4 + s 3],
    ![s 0, s 0 + s 2, s 0 + s 4 + s 3, s 6 + s 0]]

/-- A symmetric rank-one matrix over `F_2`, written in its intrinsic form
`v v^T`. -/
def IsSymmetricRankOne (M : Fin 4 → Fin 4 → F₂) : Prop :=
  ∃ v : Fin 4 → F₂, ∀ i j, M i j = v i * v j

/-- The explicit `4 x 4` contradiction in manuscript display (11.8). -/
theorem targetCleanProjectedMatrix_not_symmetricRankOne
    (s : Fin 7 → F₂) :
    ¬ IsSymmetricRankOne (targetCleanProjectedMatrix s) := by
  rintro ⟨v, hv⟩
  let a := s 0
  let b := s 1
  let c := s 2
  let d := s 3
  let e := s 4
  let f := s 5
  let g := s 6
  have h00 := hv 0 0
  have h01 := hv 0 1
  have h02 := hv 0 2
  have h03 := hv 0 3
  have h11 := hv 1 1
  have h12 := hv 1 2
  have h13 := hv 1 3
  have h22 := hv 2 2
  have h33 := hv 3 3
  simp only [targetCleanProjectedMatrix] at h00 h01 h02 h03 h11 h12 h13 h22 h33
  change f + a = v 0 * v 0 at h00
  change 1 + a + b = v 0 * v 1 at h01
  change a + c + d = v 0 * v 2 at h02
  change a = v 0 * v 3 at h03
  change a = v 1 * v 1 at h11
  change a + b + d = v 1 * v 2 at h12
  change a + c = v 1 * v 3 at h13
  change a + c = v 2 * v 2 at h22
  change g + a = v 3 * v 3 at h33
  simp only [N3Certificate.mul_self_f2] at h00 h11 h22 h33
  rcases f2_eq_zero_or_one a with ha | ha
  · have hv1 : v 1 = 0 := by simpa [ha] using h11.symm
    have hc : c = 0 := by simpa [ha, hv1] using h13
    have hbd : b + d = 0 := by simpa [ha, hv1] using h12
    have hd : d = b := by
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      simpa [add_comm] using hbd
    have hb : b = 1 := by
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      simpa [ha, hv1, add_comm] using h01
    have hv2 : v 2 = 0 := by simpa [ha, hc] using h22.symm
    have : (1 : F₂) = 0 := by
      simpa [ha, hc, hd, hb, hv2] using h02
    norm_num at this
  · have hv1 : v 1 = 1 := by simpa [ha] using h11.symm
    have hv0 : v 0 = f + 1 := by simpa [ha] using h00.symm
    have hv2 : v 2 = c + 1 := by
      simpa [ha, add_comm] using h22.symm
    have hv3 : v 3 = c + 1 := by
      simpa [ha, hv1, add_comm] using h13.symm
    have hg : g + 1 = v 3 := by simpa [ha] using h33
    have hcg : c = g := by
      have hgc : g + 1 = c + 1 := hg.trans hv3
      exact (add_right_cancel hgc).symm
    have h12' : 1 + b + d = c + 1 := by
      simpa [ha, hv1, hv2, add_comm] using h12
    have h12'' : 1 + (b + d) = 1 + c := by
      simpa [add_assoc, add_comm] using h12'
    have hbdc : b + d = c := add_left_cancel h12''
    have hd : d = b + c := by
      calc
        d = 0 + d := (zero_add d).symm
        _ = (b + b) + d := by rw [CharTwo.add_self_eq_zero]
        _ = b + (b + d) := add_assoc b b d
        _ = b + c := congrArg (b + ·) hbdc
    have hb : b = f + 1 := by
      simpa [ha, hv0, hv1, add_assoc, add_comm, add_left_comm,
        CharTwo.add_self_eq_zero] using h01
    have hF : f = (f + 1) * (c + 1) := by
      rw [hv0, hv2] at h02
      have hlhs : a + c + d = f := by
        rw [ha, hd, hb]
        ring_nf
        simp [N3Certificate.two_eq_zero_f2]
      rwa [hlhs] at h02
    have hOne : (1 : F₂) = (f + 1) * (c + 1) := by
      rw [hv0, hv3] at h03
      simpa [ha] using h03
    have hf : f = 1 := hF.trans hOne.symm
    rw [hf, CharTwo.add_self_eq_zero, zero_mul] at hOne
    norm_num at hOne

/-! ## Retained cross projection -/

/-- The indices retained after deleting the zero-place extension row and
column. -/
def targetCleanRetainedIndex : Fin 4 → Fin 5 :=
  ![0, 2, 3, 4]

/-- Cross block on the retained indices. -/
def targetCleanRetainedCrossMap :
    TwoForm →ₗ[F₂] (Fin 4 → Fin 4 → F₂) where
  toFun p i j := p (quadraticPair
    (aCoord (targetCleanRetainedIndex i))
    (bCoord (targetCleanRetainedIndex j))
    (aCoord_ne_bCoord _ _))
  map_add' p q := by
    ext i j
    simp
  map_smul' a p := by
    ext i j
    simp

/-- Linear combination of the exact first-order basis. -/
def exactFirstOrderCombination (s : Fin 8 → F₂) : TargetCoeff :=
  ∑ i : Fin 8, s i • exactFirstOrderDirections i

/-- Coordinate normal form for the exact first-order combination.  Keeping
this nine-coordinate calculation separate prevents the retained `4 × 4`
proof from repeatedly expanding the same eight-term sum. -/
def exactFirstOrderCombinationFormula (s : Fin 8 → F₂) : TargetCoeff :=
  ![s 0 + s 1,
    s 1 + s 3 + s 4,
    s 1 + s 6,
    s 1 + s 4 + s 7,
    s 1,
    s 1 + s 4 + s 6,
    s 1 + s 7,
    s 1 + s 4 + s 5,
    s 2 + s 1]

theorem exactFirstOrderCombination_eq_formula (s : Fin 8 → F₂) :
    exactFirstOrderCombination s = exactFirstOrderCombinationFormula s := by
  ext k
  fin_cases k <;>
    simp [exactFirstOrderCombination, exactFirstOrderCombinationFormula,
      exactFirstOrderDirections, exactJOneCoeff, exactJInfinityCoeff,
      rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
      dStarZeroCoeff, dStarOneCoeff, Fin.sum_univ_succ,
      add_assoc, add_comm] <;> exact add_comm _ _

/-- Remove the invisible `j_0` coordinate and reorder the remaining
coordinates as the manuscript parameters `a,b,c,d,e,f,g`. -/
def visibleTargetCleanParams (s : Fin 8 → F₂) : Fin 7 → F₂ :=
  ![s 1, s 6, s 7, s 4, s 5, s 0, s 2]

/-- Direct verification that the retained projection of `tau + U` is the
displayed matrix (11.8). -/
theorem targetCleanRetainedCross_exactCombination (s : Fin 8 → F₂) :
    targetCleanRetainedCrossMap
        (targetTwo (firstOrderMissingCoeff + exactFirstOrderCombination s)) =
      targetCleanProjectedMatrix (visibleTargetCleanParams s) := by
  rw [exactFirstOrderCombination_eq_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [targetCleanRetainedCrossMap, targetCleanRetainedIndex,
      exactFirstOrderCombinationFormula,
      visibleTargetCleanParams, targetCleanProjectedMatrix,
      firstOrderMissingCoeff,
      hankelIndex, add_assoc, add_comm, add_left_comm]

/-- Every first-order coefficient has exact-basis coordinates. -/
theorem exists_exactFirstOrderCombination
    (c : TargetCoeff) (hc : c ∈ firstOrderEnvelopeCoeffSpace) :
    ∃ s : Fin 8 → F₂, exactFirstOrderCombination s = c := by
  rw [← span_exactFirstOrderDirections_eq,
    ← coefficientSum_range] at hc
  rcases hc with ⟨s, hs⟩
  exact ⟨s, hs⟩

/-! ## Removing the local second-jet summands -/

/-- A core wedge has only its `(a_0,b_0)` entry visible in the retained
cross block.  That entry is a scalar multiple of the rational zero-place
direction, hence can be absorbed into `U`. -/
theorem targetCleanRetainedCross_core
    (p : TwoForm) (hp : p ∈ quadraticExterior secondJetCoreSpace) :
    targetCleanRetainedCrossMap p =
      p (quadraticPair (aCoord 0) (bCoord 0) (aCoord_ne_bCoord 0 0)) •
        targetCleanRetainedCrossMap (targetTwo rZeroCoeff) := by
  refine Submodule.span_induction (p := fun p _ =>
      targetCleanRetainedCrossMap p =
        p (quadraticPair (aCoord 0) (bCoord 0) (aCoord_ne_bCoord 0 0)) •
          targetCleanRetainedCrossMap (targetTwo rZeroCoeff)) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨u, hu, v, hv, rfl⟩
    change ∀ i, i ∉ secondJetCoreSet → u i = 0 at hu
    change ∀ i, i ∉ secondJetCoreSet → v i = 0 at hv
    have hua2 : u (aCoord 2) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hua3 : u (aCoord 3) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hua4 : u (aCoord 4) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hub2 : u (bCoord 2) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hub3 : u (bCoord 3) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hub4 : u (bCoord 4) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hva2 : v (aCoord 2) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hva3 : v (aCoord 3) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hva4 : v (aCoord 4) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hvb2 : v (bCoord 2) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hvb3 : v (bCoord 3) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hvb4 : v (bCoord 4) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [targetCleanRetainedCrossMap, targetCleanRetainedIndex,
        squarefreeWedge_pair, rZeroCoeff, hankelIndex,
        hua2, hua3, hua4, hub2, hub3, hub4,
        hva2, hva3, hva4, hvb2, hvb3, hvb4]
  · simp
  · intro p q _ _ hp hq
    simp only [map_add, Pi.add_apply, hp, hq, add_smul]
  · intro a p _ hp
    simp only [map_smul, Pi.smul_apply, hp, smul_smul, smul_eq_mul]

/-- Wedges with one factor in the deleted extension block have zero retained
cross block. -/
theorem targetCleanRetainedCross_extension
    (p : TwoForm) (hp : p ∈ leftWedgeSpace secondJetExtensionSpace) :
    targetCleanRetainedCrossMap p = 0 := by
  refine Submodule.span_induction (p := fun p _ =>
      targetCleanRetainedCrossMap p = 0) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨u, hu, v, rfl⟩
    change ∀ i, i ∉ secondJetExtensionSet → u i = 0 at hu
    have hua0 : u (aCoord 0) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hua2 : u (aCoord 2) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hua3 : u (aCoord 3) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hua4 : u (aCoord 4) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hub0 : u (bCoord 0) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hub2 : u (bCoord 2) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hub3 : u (bCoord 3) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hub4 : u (bCoord 4) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [targetCleanRetainedCrossMap, targetCleanRetainedIndex,
        squarefreeWedge_pair, hua0, hua2, hua3, hua4,
        hub0, hub2, hub3, hub4]
  · simp
  · intro p q _ _ hp hq
    simpa only [map_add, hp, hq, add_zero]
  · intro a p _ hp
    simpa only [map_smul, hp, smul_zero]

/-- Every second-jet element has the same retained cross block as some
member of the first-order target envelope. -/
theorem exists_firstOrderEnvelope_same_retainedCross
    (z : TwoForm) (hz : z ∈ targetCleanSecondJetSpace) :
    ∃ c ∈ firstOrderEnvelopeCoeffSpace,
      targetCleanRetainedCrossMap z = targetCleanRetainedCrossMap (targetTwo c) := by
  change z ∈ (firstOrderEnvelopeTwoSpace ⊔
    quadraticExterior secondJetCoreSpace) ⊔
      leftWedgeSpace secondJetExtensionSpace at hz
  rcases Submodule.mem_sup.mp hz with ⟨w, hw, e, he, rfl⟩
  rcases Submodule.mem_sup.mp hw with ⟨t, ht, q, hq, rfl⟩
  rcases ht with ⟨c, hc, rfl⟩
  let a := q (quadraticPair (aCoord 0) (bCoord 0)
    (aCoord_ne_bCoord 0 0))
  refine ⟨c + a • rZeroCoeff, ?_, ?_⟩
  · exact firstOrderEnvelopeCoeffSpace.add_mem hc
      (firstOrderEnvelopeCoeffSpace.smul_mem a
        (exactFirstOrderDirection_mem 0))
  · simp only [map_add]
    rw [targetCleanRetainedCross_core q hq,
      targetCleanRetainedCross_extension e he, add_zero]
    change targetCleanRetainedCrossMap (targetTwo c) +
        a • targetCleanRetainedCrossMap (targetTwo rZeroCoeff) =
      targetCleanRetainedCrossMap (targetTwo (c + a • rZeroCoeff))
    change targetCleanRetainedCrossMap (targetTwoLinear c) +
        a • targetCleanRetainedCrossMap (targetTwoLinear rZeroCoeff) =
      targetCleanRetainedCrossMap
        (targetTwoLinear (c + a • rZeroCoeff))
    rw [map_add targetTwoLinear, map_smul targetTwoLinear,
      map_add targetCleanRetainedCrossMap,
      map_smul targetCleanRetainedCrossMap]

/-- The retained cross block of every element of the affine family
`tau + Z_0` is one of the explicit matrices (11.8). -/
theorem exists_projectedMatrix_eq_retainedCross_affine
    (z : TwoForm) (hz : z ∈ targetCleanSecondJetSpace) :
    ∃ s : Fin 8 → F₂,
      targetCleanRetainedCrossMap (targetTwo firstOrderMissingCoeff + z) =
        targetCleanProjectedMatrix (visibleTargetCleanParams s) := by
  rcases exists_firstOrderEnvelope_same_retainedCross z hz with ⟨c, hc, hzc⟩
  rcases exists_exactFirstOrderCombination c hc with ⟨s, rfl⟩
  refine ⟨s, ?_⟩
  rw [map_add, hzc]
  change targetCleanRetainedCrossMap
      (targetTwoLinear firstOrderMissingCoeff +
        targetTwoLinear (exactFirstOrderCombination s)) = _
  rw [← map_add]
  change targetCleanRetainedCrossMap
      (targetTwo (firstOrderMissingCoeff + exactFirstOrderCombination s)) = _
  exact targetCleanRetainedCross_exactCombination s

/-! ## The retained same-side block and outer rank -/

/-- Alternating same-`A` block on the four retained indices. -/
def targetCleanRetainedSameAMap :
    TwoForm →ₗ[F₂] (Fin 4 → Fin 4 → F₂) where
  toFun p i j := ambientTwoCoeff p
    (aCoord (targetCleanRetainedIndex i))
    (aCoord (targetCleanRetainedIndex j))
  map_add' p q := by
    ext i j
    exact ambientTwoCoeff_add p q _ _
  map_smul' a p := by
    ext i j
    change ambientTwoCoeff (a • p)
        (aCoord (targetCleanRetainedIndex i))
        (aCoord (targetCleanRetainedIndex j)) =
      a • ambientTwoCoeff p
        (aCoord (targetCleanRetainedIndex i))
        (aCoord (targetCleanRetainedIndex j))
    by_cases h : aCoord (targetCleanRetainedIndex i) =
        aCoord (targetCleanRetainedIndex j)
    · simp only [ambientTwoCoeff, dif_pos h, smul_zero]
    · simp only [ambientTwoCoeff, dif_neg h, Pi.smul_apply,
        smul_eq_mul]

theorem targetCleanRetainedSameA_target (c : TargetCoeff) :
    targetCleanRetainedSameAMap (targetTwo c) = 0 := by
  ext i j
  change ambientTwoCoeff (targetTwo c)
      (aCoord (targetCleanRetainedIndex i))
      (aCoord (targetCleanRetainedIndex j)) = 0
  by_cases hij : targetCleanRetainedIndex i = targetCleanRetainedIndex j
  · have haij : aCoord (targetCleanRetainedIndex i) =
        aCoord (targetCleanRetainedIndex j) := congrArg aCoord hij
    simp only [ambientTwoCoeff, dif_pos haij]
  · have haij : aCoord (targetCleanRetainedIndex i) ≠
        aCoord (targetCleanRetainedIndex j) := by
      intro h
      exact hij (aCoord_injective h)
    simp only [ambientTwoCoeff, dif_neg haij]
    exact targetTwo_sameA c _ _ hij

theorem targetCleanRetainedSameA_core
    (p : TwoForm) (hp : p ∈ quadraticExterior secondJetCoreSpace) :
    targetCleanRetainedSameAMap p = 0 := by
  refine Submodule.span_induction (p := fun p _ =>
      targetCleanRetainedSameAMap p = 0) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨u, hu, v, hv, rfl⟩
    change ∀ i, i ∉ secondJetCoreSet → u i = 0 at hu
    change ∀ i, i ∉ secondJetCoreSet → v i = 0 at hv
    have hua2 : u (aCoord 2) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hua3 : u (aCoord 3) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hua4 : u (aCoord 4) = 0 := hu _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hva2 : v (aCoord 2) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hva3 : v (aCoord 3) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    have hva4 : v (aCoord 4) = 0 := hv _ (by
      simp [secondJetCoreSet, aCoord, bCoord])
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [targetCleanRetainedSameAMap, targetCleanRetainedIndex,
        ambientTwoCoeff_squarefreeWedge,
        hua2, hua3, hua4, hva2, hva3, hva4,
        CharTwo.add_self_eq_zero]
  · simp
  · intro p q _ _ hp hq
    simpa only [map_add, hp, hq, add_zero]
  · intro a p _ hp
    simpa only [map_smul, hp, smul_zero]

theorem targetCleanRetainedSameA_extension
    (p : TwoForm) (hp : p ∈ leftWedgeSpace secondJetExtensionSpace) :
    targetCleanRetainedSameAMap p = 0 := by
  refine Submodule.span_induction (p := fun p _ =>
      targetCleanRetainedSameAMap p = 0) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨u, hu, v, rfl⟩
    change ∀ i, i ∉ secondJetExtensionSet → u i = 0 at hu
    have hua0 : u (aCoord 0) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hua2 : u (aCoord 2) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hua3 : u (aCoord 3) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    have hua4 : u (aCoord 4) = 0 := hu _ (by
      simp [secondJetExtensionSet, aCoord, bCoord])
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [targetCleanRetainedSameAMap, targetCleanRetainedIndex,
        ambientTwoCoeff_squarefreeWedge,
        hua0, hua2, hua3, hua4]
  · simp
  · intro p q _ _ hp hq
    simpa only [map_add, hp, hq, add_zero]
  · intro a p _ hp
    simpa only [map_smul, hp, smul_zero]

theorem targetCleanRetainedSameA_secondJet
    (z : TwoForm) (hz : z ∈ targetCleanSecondJetSpace) :
    targetCleanRetainedSameAMap z = 0 := by
  change z ∈ (firstOrderEnvelopeTwoSpace ⊔
    quadraticExterior secondJetCoreSpace) ⊔
      leftWedgeSpace secondJetExtensionSpace at hz
  rcases Submodule.mem_sup.mp hz with ⟨w, hw, e, he, rfl⟩
  rcases Submodule.mem_sup.mp hw with ⟨t, ht, q, hq, rfl⟩
  rcases ht with ⟨c, hc, rfl⟩
  change targetCleanRetainedSameAMap (targetTwo c + q + e) = 0
  rw [map_add, map_add, targetCleanRetainedSameA_target,
    targetCleanRetainedSameA_core q hq,
    targetCleanRetainedSameA_extension e he, add_zero, zero_add]

/-- Retained restrictions of the two halves of a linear form. -/
def targetCleanRetainedAPart (u : LinearForm) : Fin 4 → F₂ :=
  fun i => u (aCoord (targetCleanRetainedIndex i))

def targetCleanRetainedBPart (u : LinearForm) : Fin 4 → F₂ :=
  fun i => u (bCoord (targetCleanRetainedIndex i))

/-- Ordinary (possibly zero) outer rank at most one. -/
def IsOuterRankOne (M : Fin 4 → Fin 4 → F₂) : Prop :=
  ∃ x y : Fin 4 → F₂, ∀ i j, M i j = x i * y j

theorem targetCleanRetainedCross_squarefreeWedge
    (u v : LinearForm) (i j : Fin 4) :
    targetCleanRetainedCrossMap (squarefreeWedge u v) i j =
      targetCleanRetainedAPart u i * targetCleanRetainedBPart v j +
      targetCleanRetainedAPart v i * targetCleanRetainedBPart u j := by
  simp [targetCleanRetainedCrossMap, targetCleanRetainedAPart,
    targetCleanRetainedBPart, squarefreeWedge_pair, mul_comm]

/-- If the retained same-`A` block of a decomposable form vanishes, its
retained cross block has outer rank at most one. -/
theorem targetCleanRetainedCross_outer_of_sameA_zero
    (u v : LinearForm)
    (hA : targetCleanRetainedSameAMap (squarefreeWedge u v) = 0) :
    IsOuterRankOne (targetCleanRetainedCrossMap (squarefreeWedge u v)) := by
  have hdep : targetCleanRetainedAPart u = 0 ∨
      targetCleanRetainedAPart v = 0 ∨
      targetCleanRetainedAPart u = targetCleanRetainedAPart v := by
    apply N4.dependent_of_vectorWedge_zero
    intro i j
    have hij := congrFun (congrFun hA i) j
    simpa [targetCleanRetainedSameAMap, targetCleanRetainedAPart,
      ambientTwoCoeff_squarefreeWedge] using hij
  rcases hdep with hu | hv | huv
  · refine ⟨targetCleanRetainedAPart v,
      targetCleanRetainedBPart u, ?_⟩
    intro i j
    rw [targetCleanRetainedCross_squarefreeWedge]
    have hui : targetCleanRetainedAPart u i = 0 := congrFun hu i
    simp [hui]
  · refine ⟨targetCleanRetainedAPart u,
      targetCleanRetainedBPart v, ?_⟩
    intro i j
    rw [targetCleanRetainedCross_squarefreeWedge]
    have hvi : targetCleanRetainedAPart v i = 0 := congrFun hv i
    simp [hvi]
  · refine ⟨targetCleanRetainedAPart u,
      fun j => targetCleanRetainedBPart v j +
        targetCleanRetainedBPart u j, ?_⟩
    intro i j
    rw [targetCleanRetainedCross_squarefreeWedge]
    have hvi : targetCleanRetainedAPart v i =
        targetCleanRetainedAPart u i := congrFun huv.symm i
    rw [hvi]
    ring

theorem targetCleanProjectedMatrix_symmetric (s : Fin 7 → F₂) :
    ∀ i j, targetCleanProjectedMatrix s i j =
      targetCleanProjectedMatrix s j i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [targetCleanProjectedMatrix]

/-- A symmetric outer product over `F₂` is intrinsically of the form
`v v^T`. -/
theorem symmetricRankOne_of_outerRankOne
    (M : Fin 4 → Fin 4 → F₂)
    (houter : IsOuterRankOne M)
    (hsymm : ∀ i j, M i j = M j i) :
    IsSymmetricRankOne M := by
  rcases houter with ⟨x, y, hxy⟩
  by_cases hx : x = 0
  · refine ⟨0, ?_⟩
    intro i j
    rw [hxy]
    simp [hx]
  by_cases hy : y = 0
  · refine ⟨0, ?_⟩
    intro i j
    rw [hxy]
    simp [hy]
  have hex : ∃ k, x k ≠ 0 := by
    by_contra hk
    push Not at hk
    exact hx (funext hk)
  rcases hex with ⟨k, hxk0⟩
  have hxk : x k = 1 := (f2_eq_zero_or_one (x k)).resolve_left hxk0
  have hyk0 : y k ≠ 0 := by
    intro hyk
    apply hy
    funext j
    have hs := hsymm k j
    rw [hxy, hxy] at hs
    simpa [hxk, hyk] using hs
  have hyk : y k = 1 := (f2_eq_zero_or_one (y k)).resolve_left hyk0
  have hyx : y = x := by
    funext j
    have hs := hsymm k j
    rw [hxy, hxy] at hs
    simpa [hxk, hyk] using hs
  refine ⟨x, ?_⟩
  intro i j
  rw [hxy, hyx]

/-- The affine target-clean family contains no decomposable two-form. -/
theorem firstOrderMissing_add_targetClean_not_decomposable
    (z : TwoForm) (hz : z ∈ targetCleanSecondJetSpace) :
    ¬ IsDecomposableTwo (targetTwo firstOrderMissingCoeff + z) := by
  rintro ⟨u, v, huv⟩
  have hsame : targetCleanRetainedSameAMap
      (targetTwo firstOrderMissingCoeff + z) = 0 := by
    rw [map_add, targetCleanRetainedSameA_target,
      targetCleanRetainedSameA_secondJet z hz, add_zero]
  have hsameWedge : targetCleanRetainedSameAMap
      (squarefreeWedge u v) = 0 := by
    rw [← huv]
    exact hsame
  have houter := targetCleanRetainedCross_outer_of_sameA_zero u v hsameWedge
  rcases exists_projectedMatrix_eq_retainedCross_affine z hz with ⟨s, hs⟩
  have houterM : IsOuterRankOne
      (targetCleanProjectedMatrix (visibleTargetCleanParams s)) := by
    rw [← hs, huv]
    exact houter
  have hrank := symmetricRankOne_of_outerRankOne
    (targetCleanProjectedMatrix (visibleTargetCleanParams s)) houterM
    (targetCleanProjectedMatrix_symmetric (visibleTargetCleanParams s))
  exact targetCleanProjectedMatrix_not_symmetricRankOne
    (visibleTargetCleanParams s) hrank

/-- Manuscript equation (11.7): adjoining one decomposable quadratic form
to the target-clean second jet still creates no new target direction. -/
theorem targetTwoSpace_inf_targetClean_sup_decomposable
    (q : TwoForm) (hqdec : IsDecomposableTwo q) :
    targetTwoSpace ⊓
        (targetCleanSecondJetSpace ⊔
          Submodule.span F₂ ({q} : Set TwoForm)) =
      firstOrderEnvelopeTwoSpace := by
  apply le_antisymm
  · rintro p ⟨hpT, hpSup⟩
    rcases hpT with ⟨c, rfl⟩
    rcases Submodule.mem_sup.mp hpSup with ⟨z, hz, r, hr, hzr⟩
    rcases Submodule.mem_span_singleton.mp hr with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with ha | ha
    · rw [ha, zero_smul, add_zero] at hzr
      have htargetZ : targetTwo c ∈ targetCleanSecondJetSpace := by
        change targetTwoLinear c ∈ targetCleanSecondJetSpace
        rw [← hzr]
        exact hz
      exact (target_mem_targetCleanSecondJetSpace_iff_firstOrder
        (targetTwo c) ⟨c, rfl⟩).1 htargetZ
    · rw [ha, one_smul] at hzr
      by_cases hcU : c ∈ firstOrderEnvelopeCoeffSpace
      · exact ⟨c, hcU, rfl⟩
      · have hfc0 : firstOrderMissingFunctional c ≠ 0 := by
          intro hfc
          exact hcU ((mem_firstOrderEnvelopeCoeffSpace c).2 hfc)
        have hfc : firstOrderMissingFunctional c = 1 :=
          (f2_eq_zero_or_one (firstOrderMissingFunctional c)).resolve_left hfc0
        let uCoeff := c + firstOrderMissingCoeff
        have huCoeff : uCoeff ∈ firstOrderEnvelopeCoeffSpace := by
          rw [mem_firstOrderEnvelopeCoeffSpace]
          simp [uCoeff, hfc, CharTwo.add_self_eq_zero]
        have hcSplit : c = firstOrderMissingCoeff + uCoeff := by
          change c = firstOrderMissingCoeff + (c + firstOrderMissingCoeff)
          ext i
          calc
            c i = c i + 0 := (add_zero (c i)).symm
            _ = c i +
                (firstOrderMissingCoeff i + firstOrderMissingCoeff i) := by
              rw [CharTwo.add_self_eq_zero]
            _ = firstOrderMissingCoeff i +
                (c i + firstOrderMissingCoeff i) := by
              ac_rfl
        have htargetSplit : targetTwo c =
            targetTwo firstOrderMissingCoeff + targetTwo uCoeff := by
          change targetTwoLinear c =
            targetTwoLinear firstOrderMissingCoeff + targetTwoLinear uCoeff
          rw [hcSplit, map_add]
        have htargetU : targetTwo uCoeff ∈ firstOrderEnvelopeTwoSpace :=
          ⟨uCoeff, huCoeff, rfl⟩
        have htargetZ : targetTwo uCoeff ∈ targetCleanSecondJetSpace :=
          (target_mem_targetCleanSecondJetSpace_iff_firstOrder
            (targetTwo uCoeff) ⟨uCoeff, rfl⟩).2 htargetU
        have hz' : z + targetTwo uCoeff ∈ targetCleanSecondJetSpace :=
          targetCleanSecondJetSpace.add_mem hz htargetZ
        have hqeq : q = targetTwo firstOrderMissingCoeff +
            (z + targetTwo uCoeff) := by
          ext idx
          have hzr' := congrFun hzr idx
          have htargetSplit' := congrFun htargetSplit idx
          change q idx = targetTwo firstOrderMissingCoeff idx +
            (z idx + targetTwo uCoeff idx)
          calc
            q idx = 0 + q idx := (zero_add (q idx)).symm
            _ = (z idx + z idx) + q idx := by
              rw [CharTwo.add_self_eq_zero]
            _ = z idx + (z idx + q idx) := add_assoc (z idx) (z idx) (q idx)
            _ = z idx + targetTwo c idx :=
              congrArg (z idx + ·) hzr'
            _ = z idx + (targetTwo firstOrderMissingCoeff idx +
                targetTwo uCoeff idx) :=
              congrArg (z idx + ·) htargetSplit'
            _ = targetTwo firstOrderMissingCoeff idx +
                (z idx + targetTwo uCoeff idx) := by
              rw [← add_assoc,
                add_comm (z idx) (targetTwo firstOrderMissingCoeff idx),
                add_assoc]
        have haffineDec : IsDecomposableTwo
            (targetTwo firstOrderMissingCoeff +
              (z + targetTwo uCoeff)) := by
          rw [← hqeq]
          exact hqdec
        exact (firstOrderMissing_add_targetClean_not_decomposable
          (z + targetTwo uCoeff) hz' haffineDec).elim
  · intro p hp
    have hpT : p ∈ targetTwoSpace :=
      firstOrderEnvelopeTwoSpace_le_targetTwoSpace hp
    have hpZ : p ∈ targetCleanSecondJetSpace :=
      (target_mem_targetCleanSecondJetSpace_iff_firstOrder p hpT).2 hp
    exact ⟨hpT, Submodule.mem_sup_left hpZ⟩

end

end N5
end UnrestrictedBooleanMul
