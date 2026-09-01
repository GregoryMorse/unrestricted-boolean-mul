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

end

end N5
end UnrestrictedBooleanMul
