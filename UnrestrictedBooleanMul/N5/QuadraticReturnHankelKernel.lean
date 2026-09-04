import UnrestrictedBooleanMul.N5.QuadraticReturnKernel

/-!
# Hankel classification of quadratic-return annihilators

The generic pivot theorem reduces every non-rational rank-at-most-two
Hankel annihilator to a populated translate of the returned section.  The
only possible annihilators of an unpopulated return are therefore zero and
the three rational rank-one directions.

The finite certificate below concerns only the sixteen target Hankel words.
It does not enumerate quadratic sections, circuits, or Boolean states.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem ambientWedgeTwo_comm_hankelKernel (p q : TwoForm) :
    ambientWedgeTwo p q = ambientWedgeTwo q p := by
  funext i j k l
  simp only [ambientWedgeTwo]
  ring

@[simp] private theorem ambientTwoCoeff_targetTwo_reverse
    (c : TargetCoeff) (i j : Fin 5) :
    ambientTwoCoeff (targetTwo c) (bCoord j) (aCoord i) =
      c (hankelIndex i j) := by
  rw [ambientTwoCoeff_comm]
  exact ambientTwoCoeff_targetTwo_cross c i j

@[simp] private theorem ambientTwoCoeff_targetTwo_sameA_local
    (c : TargetCoeff) (i j : Fin 5) :
    ambientTwoCoeff (targetTwo c) (aCoord i) (aCoord j) = 0 := by
  by_cases hij : i = j
  · subst j
    exact ambientTwoCoeff_same _ _
  · simp [ambientTwoCoeff, hij]

@[simp] private theorem ambientTwoCoeff_targetTwo_sameB_local
    (c : TargetCoeff) (i j : Fin 5) :
    ambientTwoCoeff (targetTwo c) (bCoord i) (bCoord j) = 0 := by
  by_cases hij : i = j
  · subst j
    exact ambientTwoCoeff_same _ _
  · simp [ambientTwoCoeff, hij]

/-- A ten-bit word interpreted as a linear form on the ambient input
coordinates. -/
private def binaryLinearFormTen (mask : Nat) : LinearForm :=
  fun i => if mask.testBit i.val then 1 else 0

private def rankFourPivotA : Fin 16 → Fin 5 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0]

private def rankFourPivotB : Fin 16 → Fin 5 :=
  ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 4, 4, 0, 1, 0]

private def rankFourResidualLeftMask : Fin 16 → Nat :=
  ![0, 0, 0, 30, 0, 16, 16, 2, 2, 10, 10, 16, 16, 22, 22, 22]

private def rankFourResidualRightMask : Fin 16 → Nat :=
  ![0, 0, 0, 32, 0, 512, 512, 32, 64, 320, 672, 256, 256, 704, 416, 704]

/-- The pivot, its decomposable residual, and a nonzero residual certificate
for one non-rational rank-at-most-two Hankel word. -/
private abbrev RankFourHankelPivotCertificate (i : Fin 16) : Prop :=
  let p := targetTwo (rankTwoHankelWord i)
  let left := aCoord (rankFourPivotA i)
  let right := bCoord (rankFourPivotB i)
  let u := binaryLinearFormTen (rankFourResidualLeftMask i)
  let v := binaryLinearFormTen (rankFourResidualRightMask i)
  ambientTwoCoeff p left right = 1 ∧
    ambientPivotResidual p left right = squarefreeWedge u v ∧
    squarefreeWedge u v ≠ 0

/- The twelve nonzero, non-rank-one words use the displayed pivot and
residual factors.  This is a bounded target-geometry certificate. -/
set_option maxRecDepth 100000 in
private theorem rankTwoHankelWord_pivotResidual_cases :
    ∀ i : Fin 16,
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 ∨
        RankFourHankelPivotCertificate i := by
  letI : DecidableEq TwoForm := Fintype.decidablePiFintype
  intro i
  fin_cases i
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | right; right; right; right
      dsimp [RankFourHankelPivotCertificate, rankFourPivotA,
        rankFourPivotB, rankFourResidualLeftMask,
        rankFourResidualRightMask]
      refine ⟨?_, ?_, ?_⟩
      · simp [rankTwoHankelWord, rZeroCoeff, rOneCoeff,
          rInfinityCoeff, jZeroCoeff, jOneCoeff, jInfinityCoeff,
          dStarZeroCoeff, dStarOneCoeff, hankelIndex]
      · apply twoForm_ext_blocks
        · intro r s hrs
          fin_cases r <;> fin_cases s <;>
            simp only [ambientPivotResidual, Pi.add_apply,
              targetTwo_sameA, ambientPivotPlane,
              squarefreeWedge_pair, ambientPivotRow,
              ambientTwoCoeff_targetTwo_sameA_local,
              ambientTwoCoeff_targetTwo_sameB_local,
              ambientTwoCoeff_targetTwo_cross,
              ambientTwoCoeff_targetTwo_reverse] <;>
            simp [binaryLinearFormTen,
              rankTwoHankelWord, rZeroCoeff, rOneCoeff,
              rInfinityCoeff, jZeroCoeff, jOneCoeff, jInfinityCoeff,
              dStarZeroCoeff, dStarOneCoeff,
              aCoord, bCoord] at hrs ⊢ <;> decide
        · intro r s hrs
          fin_cases r <;> fin_cases s <;>
            simp only [ambientPivotResidual, Pi.add_apply,
              targetTwo_sameB, ambientPivotPlane,
              squarefreeWedge_pair, ambientPivotRow,
              ambientTwoCoeff_targetTwo_sameA_local,
              ambientTwoCoeff_targetTwo_sameB_local,
              ambientTwoCoeff_targetTwo_cross,
              ambientTwoCoeff_targetTwo_reverse] <;>
            simp [binaryLinearFormTen,
              rankTwoHankelWord, rZeroCoeff, rOneCoeff,
              rInfinityCoeff, jZeroCoeff, jOneCoeff, jInfinityCoeff,
              dStarZeroCoeff, dStarOneCoeff,
              aCoord, bCoord] at hrs ⊢ <;> decide
        · intro r s
          fin_cases r <;> fin_cases s <;>
            simp only [ambientPivotResidual, Pi.add_apply,
              targetTwo_cross, ambientPivotPlane,
              squarefreeWedge_pair, ambientPivotRow,
              ambientTwoCoeff_targetTwo_sameA_local,
              ambientTwoCoeff_targetTwo_sameB_local,
              ambientTwoCoeff_targetTwo_cross,
              ambientTwoCoeff_targetTwo_reverse] <;>
            simp [binaryLinearFormTen,
              rankTwoHankelWord, rZeroCoeff, rOneCoeff,
              rInfinityCoeff, jZeroCoeff, jOneCoeff, jInfinityCoeff,
              dStarZeroCoeff, dStarOneCoeff,
              aCoord, bCoord] <;> decide
      · intro hzero
        first
        | have hcoefficient := congrFun hzero
            (quadraticPair 1 5 (by decide))
          simp [squarefreeWedge_pair, binaryLinearFormTen] at hcoefficient
        | have hcoefficient := congrFun hzero
            (quadraticPair 4 9 (by decide))
          simp [squarefreeWedge_pair, binaryLinearFormTen] at hcoefficient
        | have hcoefficient := congrFun hzero
            (quadraticPair 1 6 (by decide))
          simp [squarefreeWedge_pair, binaryLinearFormTen] at hcoefficient
        | have hcoefficient := congrFun hzero
            (quadraticPair 4 8 (by decide))
          simp [squarefreeWedge_pair, binaryLinearFormTen] at hcoefficient

/-- Every target annihilator of the affine missing coset translated by an
unpopulated section is zero or one of the three rational directions. -/
theorem unpopulatedSection_annihilator_eq_zero_or_rational
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (u c : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (hzero : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + u) + z)
      (targetTwo c) = 0) :
    c = 0 ∨ c = rZeroCoeff ∨ c = rOneCoeff ∨
      c = rInfinityCoeff := by
  have hrank : HankelRankLETwo c :=
    unpopulatedSection_annihilator_hankelRankLETwo
      z hunpopulated u c hu hzero
  rcases rankTwoHankel_classification hrank with ⟨i, hi⟩
  rcases rankTwoHankelWord_pivotResidual_cases i with
    h0 | h1 | h2 | hInfinity | hgeometry
  · left
    simpa [h0, rankTwoHankelWord] using hi
  · right; left
    simpa [h1, rankTwoHankelWord] using hi
  · right; right; left
    simpa [h2, rankTwoHankelWord] using hi
  · right; right; right
    simpa [hInfinity, rankTwoHankelWord] using hi
  · rw [hi] at hzero
    dsimp only [RankFourHankelPivotCertificate] at hgeometry
    rcases hgeometry with ⟨hpivot, hresidual, hresidualNe⟩
    have hcommuted : ambientWedgeTwo
        (targetTwo (rankTwoHankelWord i))
        (targetTwo (firstOrderMissingCoeff + u) + z) = 0 := by
      rw [ambientWedgeTwo_comm_hankelKernel]
      exact hzero
    rcases exists_decomposable_translate_of_pivotResidual
        (targetTwo (rankTwoHankelWord i))
        (targetTwo (firstOrderMissingCoeff + u) + z)
        (aCoord (rankFourPivotA i)) (bCoord (rankFourPivotB i)) hpivot
        (binaryLinearFormTen (rankFourResidualLeftMask i))
        (binaryLinearFormTen (rankFourResidualRightMask i))
        hresidual hresidualNe hcommuted with
      ⟨dform, hdform, scalar, hline⟩
    exfalso
    apply hunpopulated dform hdform
    have htranslated :
        (targetTwo (firstOrderMissingCoeff + u) + z) + dform ∈
          targetTwoSpace := by
      rw [hline]
      exact targetTwoSpace.smul_mem scalar
        (targetTwo_mem_targetTwoSpace (rankTwoHankelWord i))
    have hbase : targetTwo (firstOrderMissingCoeff + u) ∈
        targetTwoSpace := targetTwo_mem_targetTwoSpace _
    have hcancel := targetTwoSpace.add_mem htranslated hbase
    convert hcancel using 1
    funext s
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]

end
end N5
end UnrestrictedBooleanMul
