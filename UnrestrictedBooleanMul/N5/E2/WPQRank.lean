import UnrestrictedBooleanMul.N5.E2.FixedBlockRank

/-!
# Two-rational fixed-block certificate

Explicit rank-two completions and fixed nonzero minors prove manuscript
equation (10.8) without an exhaustive search over completions.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

private theorem two_f2 : (2 : F₂) = 0 := by decide
private theorem four_f2 : (4 : F₂) = 0 := by decide
private theorem six_f2 : (6 : F₂) = 0 := by decide
private theorem seven_f2 : (7 : F₂) = 1 := by decide
private theorem eight_f2 : (8 : F₂) = 0 := by decide

private theorem rank_wPQ_0000 :
    RankLETwo (wPQMatrix (word 0 0 0 0) 0) := by
  decide

private theorem rank_wPQ_0010 :
    RankLETwo (wPQMatrix (word 0 0 1 0) ![0, 1, 0, 0, 1, 0, 0]) := by
  decide

private theorem rank_wPQ_0101 :
    RankLETwo (wPQMatrix (word 0 1 0 1) 0) := by
  decide

private theorem rank_wPQ_0111 :
    RankLETwo (wPQMatrix (word 0 1 1 1) ![0, 1, 0, 0, 1, 0, 0]) := by
  decide

private theorem rank_wPQ_1000 :
    RankLETwo (wPQMatrix (word 1 0 0 0) 0) := by
  decide

private theorem rank_wPQ_1001 :
    RankLETwo (wPQMatrix (word 1 0 0 1) ![0, 1, 1, 1, 1, 0, 1]) := by
  decide

private theorem rank_wPQ_1011 :
    RankLETwo (wPQMatrix (word 1 0 1 1) ![1, 1, 0, 0, 1, 1, 1]) := by
  decide

private theorem rank_wPQ_1111 :
    RankLETwo (wPQMatrix (word 1 1 1 1) 0) := by
  decide

private theorem minor_wPQ_0001 (z : Completion) :
    minorThree (wPQMatrix (word 0 0 0 1) z) 1 9 = 1 := by
  simp [minorThree, indexTriple, wPQMatrix, word]

private theorem minor_wPQ_0011 (z : Completion) :
    minorThree (wPQMatrix (word 0 0 1 1) z) 2 9 = 1 := by
  simp [minorThree, indexTriple, wPQMatrix, word]
  ring_nf
  simp [four_f2, seven_f2]

private theorem minor_wPQ_0100 (z : Completion) :
    minorThree (wPQMatrix (word 0 1 0 0) z) 2 6 = 1 := by
  simp [minorThree, indexTriple, wPQMatrix, word]

private theorem minor_wPQ_0110 (z : Completion) :
    minorThree (wPQMatrix (word 0 1 1 0) z) 2 9 = 1 := by
  simp [minorThree, indexTriple, wPQMatrix, word]
  ring_nf
  simp [four_f2, seven_f2]

private theorem minor_wPQ_1010 (z : Completion) :
    minorThree (wPQMatrix (word 1 0 1 0) z) 2 9 = 1 := by
  simp [minorThree, indexTriple, wPQMatrix, word]
  ring_nf
  simp [two_f2, four_f2]

private theorem minor_wPQ_1100 (z : Completion) :
    minorThree (wPQMatrix (word 1 1 0 0) z) 2 3 = 1 := by
  simp [minorThree, indexTriple, wPQMatrix, word]
  ring_nf
  exact two_f2

private theorem minor_wPQ_1101 (z : Completion) :
    minorThree (wPQMatrix (word 1 1 0 1) z) 2 9 = 1 := by
  simp [minorThree, indexTriple, wPQMatrix, word]
  ring_nf
  simp [two_f2, eight_f2]

private theorem minor_wPQ_1110 (z : Completion) :
    minorThree (wPQMatrix (word 1 1 1 0) z) 0 9 = 1 := by
  simp [minorThree, indexTriple, wPQMatrix, word]
  ring_nf
  simp [six_f2, seven_f2, eight_f2]

private theorem not_wPQ_0001 : ¬ WPQCompletable (word 0 0 0 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wPQ_0001 z) hz

private theorem not_wPQ_0011 : ¬ WPQCompletable (word 0 0 1 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wPQ_0011 z) hz

private theorem not_wPQ_0100 : ¬ WPQCompletable (word 0 1 0 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wPQ_0100 z) hz

private theorem not_wPQ_0110 : ¬ WPQCompletable (word 0 1 1 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wPQ_0110 z) hz

private theorem not_wPQ_1010 : ¬ WPQCompletable (word 1 0 1 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wPQ_1010 z) hz

private theorem not_wPQ_1100 : ¬ WPQCompletable (word 1 1 0 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wPQ_1100 z) hz

private theorem not_wPQ_1101 : ¬ WPQCompletable (word 1 1 0 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wPQ_1101 z) hz

private theorem not_wPQ_1110 : ¬ WPQCompletable (word 1 1 1 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wPQ_1110 z) hz

private theorem comp_wPQ_0000 : WPQCompletable (word 0 0 0 0) :=
  ⟨0, rank_wPQ_0000⟩

private theorem comp_wPQ_0010 : WPQCompletable (word 0 0 1 0) :=
  ⟨![0, 1, 0, 0, 1, 0, 0], rank_wPQ_0010⟩

private theorem comp_wPQ_0101 : WPQCompletable (word 0 1 0 1) :=
  ⟨0, rank_wPQ_0101⟩

private theorem comp_wPQ_0111 : WPQCompletable (word 0 1 1 1) :=
  ⟨![0, 1, 0, 0, 1, 0, 0], rank_wPQ_0111⟩

private theorem comp_wPQ_1000 : WPQCompletable (word 1 0 0 0) :=
  ⟨0, rank_wPQ_1000⟩

private theorem comp_wPQ_1001 : WPQCompletable (word 1 0 0 1) :=
  ⟨![0, 1, 1, 1, 1, 0, 1], rank_wPQ_1001⟩

private theorem comp_wPQ_1011 : WPQCompletable (word 1 0 1 1) :=
  ⟨![1, 1, 0, 0, 1, 1, 1], rank_wPQ_1011⟩

private theorem comp_wPQ_1111 : WPQCompletable (word 1 1 1 1) :=
  ⟨0, rank_wPQ_1111⟩

private theorem low_wPQ_0010 : WPQLowClass (word 0 0 1 0) := by
  simp [WPQLowClass, word]

private theorem low_wPQ_0101 : WPQLowClass (word 0 1 0 1) := by
  simp [WPQLowClass, word]

private theorem low_wPQ_0111 : WPQLowClass (word 0 1 1 1) := by
  simp [WPQLowClass, word]

private theorem low_wPQ_1000 : WPQLowClass (word 1 0 0 0) := by
  simp [WPQLowClass, word]

private theorem low_wPQ_1001 : WPQLowClass (word 1 0 0 1) := by
  simp [WPQLowClass, word]

private theorem low_wPQ_1011 : WPQLowClass (word 1 0 1 1) := by
  simp [WPQLowClass, word]

private theorem low_wPQ_1111 : WPQLowClass (word 1 1 1 1) := by
  simp [WPQLowClass, word]

private theorem zero_word : word 0 0 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

/-- Exact two-rational fixed-block certificate, equation (10.8), with the
zero target class shown separately. -/
theorem wPQ_completable_iff (c : TargetClass) :
    WPQCompletable c ↔ c = 0 ∨ WPQLowClass c := by
  rcases f2_eq_zero_or_one (c 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (c 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (c 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (c 3) with h3 | h3
  all_goals
    have hc := targetClass_eq_word c
    simp only [h0, h1, h2, h3] at hc
    subst c
  · exact iff_of_true comp_wPQ_0000 (Or.inl zero_word)
  · exact iff_of_true comp_wPQ_1000 (Or.inr low_wPQ_1000)
  · exact iff_of_false not_wPQ_0100 (by simp [WPQLowClass, word])
  · exact iff_of_false not_wPQ_1100 (by simp [WPQLowClass, word])
  · exact iff_of_true comp_wPQ_0010 (Or.inr low_wPQ_0010)
  · exact iff_of_false not_wPQ_1010 (by simp [WPQLowClass, word])
  · exact iff_of_false not_wPQ_0110 (by simp [WPQLowClass, word])
  · exact iff_of_false not_wPQ_1110 (by simp [WPQLowClass, word])
  · exact iff_of_false not_wPQ_0001 (by simp [WPQLowClass, word])
  · exact iff_of_true comp_wPQ_1001 (Or.inr low_wPQ_1001)
  · exact iff_of_true comp_wPQ_0101 (Or.inr low_wPQ_0101)
  · exact iff_of_false not_wPQ_1101 (by simp [WPQLowClass, word])
  · exact iff_of_false not_wPQ_0011 (by simp [WPQLowClass, word])
  · exact iff_of_true comp_wPQ_1011 (Or.inr low_wPQ_1011)
  · exact iff_of_true comp_wPQ_0111 (Or.inr low_wPQ_0111)
  · exact iff_of_true comp_wPQ_1111 (Or.inr low_wPQ_1111)

theorem wPQ_nonzero_completable_iff (c : TargetClass) (hc : c ≠ 0) :
    WPQCompletable c ↔ WPQLowClass c := by
  rw [wPQ_completable_iff]
  simp [hc]

end E2
end N5
end UnrestrictedBooleanMul
