import UnrestrictedBooleanMul.N5.E2.FixedBlockRank

/-!
# Length-three rational fixed-block certificate

Explicit rank-two completions and the six fixed minors from the manuscript
prove equation (10.11) without enumerating completion coordinates.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

private theorem two_f2 : (2 : F₂) = 0 := by decide
private theorem one_add_one_f2 : (1 + 1 : F₂) = 0 :=
  N3Certificate.two_eq_zero_f2
private theorem seven_f2 : (7 : F₂) = 1 := by decide
private theorem nine_f2 : (9 : F₂) = 1 := by decide
private theorem ten_f2 : (10 : F₂) = 0 := by decide

private theorem rank_wThreeP_0000 :
    RankLETwo (wThreePMatrix (word 0 0 0 0) 0) := by
  decide

private theorem rank_wThreeP_0001 :
    RankLETwo (wThreePMatrix (word 0 0 0 1) ![0, 0, 1, 1, 0, 0, 0]) := by
  decide

private theorem rank_wThreeP_0010 :
    RankLETwo (wThreePMatrix (word 0 0 1 0) ![0, 0, 0, 1, 0, 1, 1]) := by
  decide

private theorem rank_wThreeP_0101 :
    RankLETwo (wThreePMatrix (word 0 1 0 1) 0) := by
  decide

private theorem rank_wThreeP_0111 :
    RankLETwo (wThreePMatrix (word 0 1 1 1) ![0, 1, 1, 0, 1, 1, 0]) := by
  decide

private theorem rank_wThreeP_1001 :
    RankLETwo (wThreePMatrix (word 1 0 0 1) ![0, 0, 0, 1, 1, 0, 1]) := by
  decide

private theorem rank_wThreeP_1011 :
    RankLETwo (wThreePMatrix (word 1 0 1 1) 0) := by
  decide

private theorem rank_wThreeP_1100 :
    RankLETwo (wThreePMatrix (word 1 1 0 0) ![1, 1, 0, 0, 0, 1, 1]) := by
  decide

private theorem rank_wThreeP_1110 :
    RankLETwo (wThreePMatrix (word 1 1 1 0) ![1, 1, 1, 0, 0, 1, 1]) := by
  decide

private theorem rank_wThreeP_1111 :
    RankLETwo (wThreePMatrix (word 1 1 1 1) 0) := by
  decide

private theorem minor_wThreeP_1000 (z : Completion) :
    minorThree (wThreePMatrix (word 1 0 0 0) z) 1 4 = 1 := by
  simp [minorThree, indexTriple, wThreePMatrix, word]

private theorem minor_wThreeP_0100 (z : Completion) :
    minorThree (wThreePMatrix (word 0 1 0 0) z) 0 8 = 1 := by
  simp [minorThree, indexTriple, wThreePMatrix, word]

private theorem minor_wThreeP_1010 (z : Completion) :
    minorThree (wThreePMatrix (word 1 0 1 0) z) 2 9 = 1 := by
  simp [minorThree, indexTriple, wThreePMatrix, word]
  ring_nf
  simp [two_f2]

private theorem minor_wThreeP_0110 (z : Completion) :
    minorThree (wThreePMatrix (word 0 1 1 0) z) 1 9 = 1 := by
  simp [minorThree, indexTriple, wThreePMatrix, word]
  ring_nf
  simp [two_f2]

private theorem minor_wThreeP_1101 (z : Completion) :
    minorThree (wThreePMatrix (word 1 1 0 1) z) 0 9 = 1 := by
  simp [minorThree, indexTriple, wThreePMatrix, word]
  ring_nf
  simp [two_f2, nine_f2, ten_f2]

private theorem minor_wThreeP_0011 (z : Completion) :
    minorThree (wThreePMatrix (word 0 0 1 1) z) 8 9 = 1 := by
  simp [minorThree, indexTriple, wThreePMatrix, word]
  ring_nf
  simp [two_f2, seven_f2]

private theorem not_wThreeP_1000 :
    ¬ WThreePCompletable (word 1 0 0 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wThreeP_1000 z) hz

private theorem not_wThreeP_0100 :
    ¬ WThreePCompletable (word 0 1 0 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wThreeP_0100 z) hz

private theorem not_wThreeP_1010 :
    ¬ WThreePCompletable (word 1 0 1 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wThreeP_1010 z) hz

private theorem not_wThreeP_0110 :
    ¬ WThreePCompletable (word 0 1 1 0) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wThreeP_0110 z) hz

private theorem not_wThreeP_1101 :
    ¬ WThreePCompletable (word 1 1 0 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wThreeP_1101 z) hz

private theorem not_wThreeP_0011 :
    ¬ WThreePCompletable (word 0 0 1 1) := by
  rintro ⟨z, hz⟩
  exact not_rankLETwo_of_minor_eq_one (minor_wThreeP_0011 z) hz

private theorem comp_wThreeP_0000 : WThreePCompletable (word 0 0 0 0) :=
  ⟨0, rank_wThreeP_0000⟩

private theorem comp_wThreeP_0001 : WThreePCompletable (word 0 0 0 1) :=
  ⟨![0, 0, 1, 1, 0, 0, 0], rank_wThreeP_0001⟩

private theorem comp_wThreeP_0010 : WThreePCompletable (word 0 0 1 0) :=
  ⟨![0, 0, 0, 1, 0, 1, 1], rank_wThreeP_0010⟩

private theorem comp_wThreeP_0101 : WThreePCompletable (word 0 1 0 1) :=
  ⟨0, rank_wThreeP_0101⟩

private theorem comp_wThreeP_0111 : WThreePCompletable (word 0 1 1 1) :=
  ⟨![0, 1, 1, 0, 1, 1, 0], rank_wThreeP_0111⟩

private theorem comp_wThreeP_1001 : WThreePCompletable (word 1 0 0 1) :=
  ⟨![0, 0, 0, 1, 1, 0, 1], rank_wThreeP_1001⟩

private theorem comp_wThreeP_1011 : WThreePCompletable (word 1 0 1 1) :=
  ⟨0, rank_wThreeP_1011⟩

private theorem comp_wThreeP_1100 : WThreePCompletable (word 1 1 0 0) :=
  ⟨![1, 1, 0, 0, 0, 1, 1], rank_wThreeP_1100⟩

private theorem comp_wThreeP_1110 : WThreePCompletable (word 1 1 1 0) :=
  ⟨![1, 1, 1, 0, 0, 1, 1], rank_wThreeP_1110⟩

private theorem comp_wThreeP_1111 : WThreePCompletable (word 1 1 1 1) :=
  ⟨0, rank_wThreeP_1111⟩

private theorem low_wThreeP_0001 : WThreePLowClass (word 0 0 0 1) := by
  simp [WThreePLowClass, word]

private theorem low_wThreeP_0010 : WThreePLowClass (word 0 0 1 0) := by
  simp [WThreePLowClass, word]

private theorem low_wThreeP_0101 : WThreePLowClass (word 0 1 0 1) := by
  simp [WThreePLowClass, word, one_add_one_f2]

private theorem low_wThreeP_0111 : WThreePLowClass (word 0 1 1 1) := by
  simp [WThreePLowClass, word, one_add_one_f2]

private theorem low_wThreeP_1001 : WThreePLowClass (word 1 0 0 1) := by
  simp [WThreePLowClass, word, one_add_one_f2]

private theorem low_wThreeP_1011 : WThreePLowClass (word 1 0 1 1) := by
  simp [WThreePLowClass, word, one_add_one_f2]

private theorem low_wThreeP_1100 : WThreePLowClass (word 1 1 0 0) := by
  simp [WThreePLowClass, word, one_add_one_f2]

private theorem low_wThreeP_1110 : WThreePLowClass (word 1 1 1 0) := by
  simp [WThreePLowClass, word, one_add_one_f2]

private theorem low_wThreeP_1111 : WThreePLowClass (word 1 1 1 1) := by
  simp [WThreePLowClass, word]

private theorem zero_word : word 0 0 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

/-- Exact length-three fixed-block certificate, equation (10.11), with the
zero target class shown separately. -/
theorem wThreeP_completable_iff (c : TargetClass) :
    WThreePCompletable c ↔ c = 0 ∨ WThreePLowClass c := by
  rcases f2_eq_zero_or_one (c 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (c 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (c 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (c 3) with h3 | h3
  all_goals
    have hc := targetClass_eq_word c
    simp only [h0, h1, h2, h3] at hc
    subst c
  · exact iff_of_true comp_wThreeP_0000 (Or.inl zero_word)
  · exact iff_of_false not_wThreeP_1000 (by simp [WThreePLowClass, word])
  · exact iff_of_false not_wThreeP_0100 (by simp [WThreePLowClass, word])
  · exact iff_of_true comp_wThreeP_1100 (Or.inr low_wThreeP_1100)
  · exact iff_of_true comp_wThreeP_0010 (Or.inr low_wThreeP_0010)
  · exact iff_of_false not_wThreeP_1010 (by simp [WThreePLowClass, word])
  · exact iff_of_false not_wThreeP_0110 (by simp [WThreePLowClass, word])
  · exact iff_of_true comp_wThreeP_1110 (Or.inr low_wThreeP_1110)
  · exact iff_of_true comp_wThreeP_0001 (Or.inr low_wThreeP_0001)
  · exact iff_of_true comp_wThreeP_1001 (Or.inr low_wThreeP_1001)
  · exact iff_of_true comp_wThreeP_0101 (Or.inr low_wThreeP_0101)
  · exact iff_of_false not_wThreeP_1101
      (by simp [WThreePLowClass, word, one_add_one_f2])
  · exact iff_of_false not_wThreeP_0011 (by simp [WThreePLowClass, word])
  · exact iff_of_true comp_wThreeP_1011 (Or.inr low_wThreeP_1011)
  · exact iff_of_true comp_wThreeP_0111 (Or.inr low_wThreeP_0111)
  · exact iff_of_true comp_wThreeP_1111 (Or.inr low_wThreeP_1111)

theorem wThreeP_nonzero_completable_iff
    (c : TargetClass) (hc : c ≠ 0) :
    WThreePCompletable c ↔ WThreePLowClass c := by
  rw [wThreeP_completable_iff]
  simp [hc]

end E2
end N5
end UnrestrictedBooleanMul
