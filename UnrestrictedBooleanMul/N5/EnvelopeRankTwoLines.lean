import UnrestrictedBooleanMul.N5.EnvelopeRankTwoSyzygy

/-!
# Rank-two Hankel plane lines

Five selected Hankel minors classify which pairs among the sixteen
rank-at-most-two words close to a projective line.  The finite certificate is
only over the small word-index type; coefficient transport is checked by
separate linear identities.  No Boolean assignments or circuit states are
enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private def planeBasisChangeIndex : Fin 6 → PlaneBasisChange :=
  ![.identity, .swap, .rotateRight, .rotateLeft, .cycleRight, .cycleLeft]

private def rankTwoLineLeftIndex : Fin 8 → Fin 16 :=
  ![1, 2, 4, 1, 1, 2, 13, 3]

private def rankTwoLineRightIndex : Fin 8 → Fin 16 :=
  ![7, 10, 12, 2, 4, 4, 14, 5]

private def rankTwoLineSumIndex : Fin 8 → Fin 16 :=
  ![8, 9, 11, 3, 5, 6, 15, 6]

private def indexPlaneBasisPair (g : Fin 6)
    (x y z : Fin 16) : Fin 16 × Fin 16 :=
  match g with
  | 0 => (x, y)
  | 1 => (y, x)
  | 2 => (x, z)
  | 3 => (z, y)
  | 4 => (y, z)
  | 5 => (z, x)

private def RankTwoHankelWordLineConclusion
    (i j : Fin 16) : Prop :=
  ∃ p : Fin 8, ∃ g : Fin 6,
    (i, j) = indexPlaneBasisPair g
      (rankTwoLineLeftIndex p) (rankTwoLineRightIndex p)
      (rankTwoLineSumIndex p)

private def RankTwoHankelLineEquations (c : TargetCoeff) : Prop :=
  hankelMinorThree c 0 1 4 0 1 4 = 0 ∧
  hankelMinorThree c 0 3 4 0 3 4 = 0 ∧
  hankelMinorThree c 0 1 2 0 1 2 = 0 ∧
  hankelMinorThree c 0 1 3 0 1 4 = 0 ∧
  hankelMinorThree c 0 1 2 1 2 3 = 0

private theorem rankTwoHankelLineEquations_of_rankTwo
    (c : TargetCoeff) (h : HankelRankLETwo c) :
    RankTwoHankelLineEquations c :=
  ⟨h 0 1 4 0 1 4, h 0 3 4 0 3 4, h 0 1 2 0 1 2,
    h 0 1 3 0 1 4, h 0 1 2 1 2 3⟩

/- Five selected minors classify the projective lines contained in the
sixteen rank-two Hankel words. -/
set_option maxRecDepth 100000 in
private theorem rankTwoHankelWord_indexLine_certificate :
    ∀ ij : Fin 16 × Fin 16,
      rankTwoHankelWord ij.1 ≠ 0 →
      rankTwoHankelWord ij.2 ≠ 0 →
      rankTwoHankelWord ij.1 ≠ rankTwoHankelWord ij.2 →
      RankTwoHankelLineEquations
        (rankTwoHankelWord ij.1 + rankTwoHankelWord ij.2) →
      RankTwoHankelWordLineConclusion ij.1 ij.2 := by
  letI : DecidableEq TargetCoeff := Fintype.decidablePiFintype
  let decSelected (c : TargetCoeff) :
      Decidable (RankTwoHankelLineEquations c) := by
    unfold RankTwoHankelLineEquations
    infer_instance
  let decConclusion (i j : Fin 16) :
      Decidable (RankTwoHankelWordLineConclusion i j) := by
    unfold RankTwoHankelWordLineConclusion
    infer_instance
  letI : DecidablePred (fun ij : Fin 16 × Fin 16 =>
      rankTwoHankelWord ij.1 ≠ 0 →
      rankTwoHankelWord ij.2 ≠ 0 →
      rankTwoHankelWord ij.1 ≠ rankTwoHankelWord ij.2 →
      RankTwoHankelLineEquations
        (rankTwoHankelWord ij.1 + rankTwoHankelWord ij.2) →
      RankTwoHankelWordLineConclusion ij.1 ij.2) := fun ij => by
    letI : Decidable (RankTwoHankelLineEquations
        (rankTwoHankelWord ij.1 + rankTwoHankelWord ij.2)) :=
      decSelected _
    letI : Decidable (RankTwoHankelWordLineConclusion ij.1 ij.2) :=
      decConclusion _ _
    infer_instance
  exact @of_decide_eq_true _ Fintype.decidableForallFintype rfl

/-- Canonical bases for the eight rank-two Hankel lines: three rational
value--jet lines, three rational secant lines, the degree-two translate, and
the rational secant triangle. -/
def canonicalRankTwoLeftCoeff : Fin 8 → TargetCoeff :=
  ![rZeroCoeff, rOneCoeff, rInfinityCoeff,
    rZeroCoeff, rZeroCoeff, rOneCoeff,
    degreeTwoTranslateLeftCoeff, rZeroCoeff + rOneCoeff]

def canonicalRankTwoRightCoeff : Fin 8 → TargetCoeff :=
  ![jZeroCoeff, exactJOneCoeff, exactJInfinityCoeff,
    rOneCoeff, rInfinityCoeff, rInfinityCoeff,
    degreeTwoTranslateRightCoeff, rZeroCoeff + rInfinityCoeff]

private theorem rankTwoHankelWord_leftIndex (p : Fin 8) :
    rankTwoHankelWord (rankTwoLineLeftIndex p) =
      canonicalRankTwoLeftCoeff p := by
  fin_cases p <;> funext s <;> fin_cases s <;> decide

private theorem rankTwoHankelWord_rightIndex (p : Fin 8) :
    rankTwoHankelWord (rankTwoLineRightIndex p) =
      canonicalRankTwoRightCoeff p := by
  fin_cases p <;> funext s <;> fin_cases s <;> decide

private theorem rankTwoHankelWord_sumIndex (p : Fin 8) :
    rankTwoHankelWord (rankTwoLineSumIndex p) =
      canonicalRankTwoLeftCoeff p + canonicalRankTwoRightCoeff p := by
  fin_cases p <;> funext s <;> fin_cases s <;> decide

private theorem rankTwoHankelWord_indexPlaneBasisPair
    (p : Fin 8) (g : Fin 6) :
    (rankTwoHankelWord
        (indexPlaneBasisPair g
          (rankTwoLineLeftIndex p) (rankTwoLineRightIndex p)
          (rankTwoLineSumIndex p)).1,
      rankTwoHankelWord
        (indexPlaneBasisPair g
          (rankTwoLineLeftIndex p) (rankTwoLineRightIndex p)
          (rankTwoLineSumIndex p)).2) =
      (planeBasisChangeIndex g).basisPair
        (canonicalRankTwoLeftCoeff p) (canonicalRankTwoRightCoeff p) := by
  have hl := rankTwoHankelWord_leftIndex p
  have hr := rankTwoHankelWord_rightIndex p
  have hs := rankTwoHankelWord_sumIndex p
  fin_cases g <;>
    simp [indexPlaneBasisPair, planeBasisChangeIndex,
      PlaneBasisChange.basisPair, hl, hr, hs]

/-- Three nonzero distinct rank-two directions closing under addition form
one of the eight canonical rank-two planes. -/
theorem rankTwo_plane_canonical
    (d e : TargetCoeff)
    (hd : HankelRankLETwo d) (he : HankelRankLETwo e)
    (hde : HankelRankLETwo (d + e))
    (hd0 : d ≠ 0) (he0 : e ≠ 0) (hdeq : d ≠ e) :
    ∃ p : Fin 8, ∃ g : PlaneBasisChange,
      d = (g.basisPair (canonicalRankTwoLeftCoeff p)
        (canonicalRankTwoRightCoeff p)).1 ∧
      e = (g.basisPair (canonicalRankTwoLeftCoeff p)
        (canonicalRankTwoRightCoeff p)).2 := by
  rcases rankTwoHankel_classification hd with ⟨i, hi⟩
  rcases rankTwoHankel_classification he with ⟨j, hj⟩
  have hi0 : rankTwoHankelWord i ≠ 0 := hi ▸ hd0
  have hj0 : rankTwoHankelWord j ≠ 0 := hj ▸ he0
  have hij : rankTwoHankelWord i ≠ rankTwoHankelWord j := by
    simpa only [← hi, ← hj] using hdeq
  have hselected : RankTwoHankelLineEquations
      (rankTwoHankelWord i + rankTwoHankelWord j) := by
    apply rankTwoHankelLineEquations_of_rankTwo
    simpa only [← hi, ← hj] using hde
  rcases rankTwoHankelWord_indexLine_certificate (i, j)
      hi0 hj0 hij hselected with ⟨p, g, hindex⟩
  have hcoeff := rankTwoHankelWord_indexPlaneBasisPair p g
  rw [← hindex] at hcoeff
  exact ⟨p, planeBasisChangeIndex g,
    hi.trans (congrArg Prod.fst hcoeff),
    hj.trans (congrArg Prod.snd hcoeff)⟩

end
end N5
end UnrestrictedBooleanMul
