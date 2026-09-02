import UnrestrictedBooleanMul.N5.E2.FixedBlockRank

/-!
# Degree-two-place fixed-block certificate

Explicit rank-two completions and completion-independent nonzero minors prove
manuscript equation (10.6).  The kernel proof does not enumerate the seven
completion coordinates.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

private theorem two_f2 : (2 : F₂) = 0 := by decide
private theorem three_f2 : (3 : F₂) = 1 := by decide
private theorem four_f2 : (4 : F₂) = 0 := by decide
private theorem five_f2 : (5 : F₂) = 1 := by decide
private theorem six_f2 : (6 : F₂) = 0 := by decide
private theorem eleven_f2 : (11 : F₂) = 1 := by decide
private theorem seventeen_f2 : (17 : F₂) = 1 := by decide
private theorem fortyfive_f2 : (45 : F₂) = 1 := by decide

private theorem rank_wStar_0000 :
    RankLETwo (wStarMatrix (word 0 0 0 0) 0) := by
  decide

private theorem rank_wStar_0001 :
    RankLETwo (wStarMatrix (word 0 0 0 1) 0) := by
  decide

private theorem rank_wStar_1001 :
    RankLETwo (wStarMatrix (word 1 0 0 1) 0) := by
  decide

private theorem rank_wStar_1110 :
    RankLETwo (wStarMatrix (word 1 1 1 0) 0) := by
  decide

private theorem minor_wStar_0010 (z : Completion) :
    minorThree (wStarMatrix (word 0 0 1 0) z) 0 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]

private theorem minor_wStar_0011 (z : Completion) :
    minorThree (wStarMatrix (word 0 0 1 1) z) 0 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  exact N3Certificate.two_eq_zero_f2

private theorem minor_wStar_0100 (z : Completion) :
    minorThree (wStarMatrix (word 0 1 0 0) z) 2 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]

private theorem minor_wStar_0101 (z : Completion) :
    minorThree (wStarMatrix (word 0 1 0 1) z) 1 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  ring_nf
  simp [two_f2, three_f2]

private theorem minor_wStar_0110 (z : Completion) :
    minorThree (wStarMatrix (word 0 1 1 0) z) 0 5 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  ring_nf
  simp [two_f2, three_f2, four_f2]

private theorem minor_wStar_0111 (z : Completion) :
    minorThree (wStarMatrix (word 0 1 1 1) z) 1 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  ring_nf
  simp [six_f2, seventeen_f2]

private theorem minor_wStar_1000 (z : Completion) :
    minorThree (wStarMatrix (word 1 0 0 0) z) 0 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]

private theorem minor_wStar_1010 (z : Completion) :
    minorThree (wStarMatrix (word 1 0 1 0) z) 0 8 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  ring_nf
  simp [two_f2]

private theorem minor_wStar_1011 (z : Completion) :
    minorThree (wStarMatrix (word 1 0 1 1) z) 1 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  ring_nf
  simp [four_f2, five_f2]

private theorem minor_wStar_1100 (z : Completion) :
    minorThree (wStarMatrix (word 1 1 0 0) z) 0 5 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  ring_nf
  simp [two_f2, four_f2]

private theorem minor_wStar_1101 (z : Completion) :
    minorThree (wStarMatrix (word 1 1 0 1) z) 2 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  ring_nf
  simp [two_f2, eleven_f2]

private theorem minor_wStar_1111 (z : Completion) :
    minorThree (wStarMatrix (word 1 1 1 1) z) 0 9 = 1 := by
  simp [minorThree, indexTriple, wStarMatrix, word]
  ring_nf
  simp [four_f2, fortyfive_f2]

private theorem not_wStar_0010 : ¬ WStarCompletable (word 0 0 1 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_0010 z) hz

private theorem not_wStar_0011 : ¬ WStarCompletable (word 0 0 1 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_0011 z) hz

private theorem not_wStar_0100 : ¬ WStarCompletable (word 0 1 0 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_0100 z) hz

private theorem not_wStar_0101 : ¬ WStarCompletable (word 0 1 0 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_0101 z) hz

private theorem not_wStar_0110 : ¬ WStarCompletable (word 0 1 1 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_0110 z) hz

private theorem not_wStar_0111 : ¬ WStarCompletable (word 0 1 1 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_0111 z) hz

private theorem not_wStar_1000 : ¬ WStarCompletable (word 1 0 0 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_1000 z) hz

private theorem not_wStar_1010 : ¬ WStarCompletable (word 1 0 1 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_1010 z) hz

private theorem not_wStar_1011 : ¬ WStarCompletable (word 1 0 1 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_1011 z) hz

private theorem not_wStar_1100 : ¬ WStarCompletable (word 1 1 0 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_1100 z) hz

private theorem not_wStar_1101 : ¬ WStarCompletable (word 1 1 0 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_1101 z) hz

private theorem not_wStar_1111 : ¬ WStarCompletable (word 1 1 1 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wStar_1111 z) hz

private theorem comp_wStar_0000 : WStarCompletable (word 0 0 0 0) :=
  ⟨0, rank_wStar_0000⟩

private theorem comp_wStar_0001 : WStarCompletable (word 0 0 0 1) :=
  ⟨0, rank_wStar_0001⟩

private theorem comp_wStar_1001 : WStarCompletable (word 1 0 0 1) :=
  ⟨0, rank_wStar_1001⟩

private theorem comp_wStar_1110 : WStarCompletable (word 1 1 1 0) :=
  ⟨0, rank_wStar_1110⟩

private theorem low_wStar_0001 : WStarLowClass (word 0 0 0 1) := by
  simp [WStarLowClass, word]

private theorem low_wStar_1001 : WStarLowClass (word 1 0 0 1) := by
  simp [WStarLowClass, word]

private theorem low_wStar_1110 : WStarLowClass (word 1 1 1 0) := by
  simp [WStarLowClass, word]

private theorem zero_word : word 0 0 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

/-- Exact degree-two-place fixed-block certificate, equation (10.6), with the
zero target class shown separately. -/
theorem wStar_completable_iff (c : TargetClass) :
    WStarCompletable c ↔ c = 0 ∨ WStarLowClass c := by
  rcases f2_eq_zero_or_one (c 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (c 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (c 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (c 3) with h3 | h3
  all_goals
    have hc := targetClass_eq_word c
    simp only [h0, h1, h2, h3] at hc
    subst c
  · exact iff_of_true comp_wStar_0000 (Or.inl zero_word)
  · exact iff_of_false not_wStar_1000 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_0100 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_1100 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_0010 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_1010 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_0110 (by simp [WStarLowClass, word])
  · exact iff_of_true comp_wStar_1110 (Or.inr low_wStar_1110)
  · exact iff_of_true comp_wStar_0001 (Or.inr low_wStar_0001)
  · exact iff_of_true comp_wStar_1001 (Or.inr low_wStar_1001)
  · exact iff_of_false not_wStar_0101 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_1101 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_0011 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_1011 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_0111 (by simp [WStarLowClass, word])
  · exact iff_of_false not_wStar_1111 (by simp [WStarLowClass, word])

theorem wStar_nonzero_completable_iff (c : TargetClass) (hc : c ≠ 0) :
    WStarCompletable c ↔ WStarLowClass c := by
  rw [wStar_completable_iff]
  simp [hc]

end E2
end N5
end UnrestrictedBooleanMul
