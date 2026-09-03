import UnrestrictedBooleanMul.N5.E2.FixedBlockRank

/-!
# The rational one-defect fixed-block certificate

This file checks the `5 × 5` cross-matrix calculation for the intrinsic
rational one-defect capacity block.  The five target bits are the classes of
`E₂, …, E₆`.  The five completion bits add `E₀`, `E₁`, the local term
`a₁b₁`, the all-one Hankel word, and `E₈`.

Rank at most two is expressed by the vanishing of the one hundred `3 × 3`
minors from `N5.E2.FixedBlockRank`.  The resulting six nonzero classes split
as a degree-two-place line and a three-element high-shadow set.  The latter
contains no projective line.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

abbrev RationalTargetClass := Fin 5 → F₂
abbrev RationalCompletion := Fin 5 → F₂

/-- A five-bit class in the manuscript's left-to-right order. -/
def rationalWord (a b c d e : F₂) : RationalTargetClass := ![e, d, c, b, a]

theorem rationalTargetClass_eq_word (c : RationalTargetClass) :
    c = rationalWord (c 4) (c 3) (c 2) (c 1) (c 0) := by
  funext i
  fin_cases i <;> rfl

/-- The cross matrix after adding the five fixed-block completion directions.
The fourth completion coordinate adds the all-one Hankel word. -/
def rationalOneMatrix
    (c : RationalTargetClass) (z : RationalCompletion) : E2.CrossMatrix :=
  ![
    ![z 3 + z 0, z 3 + z 1, z 3 + c 0, z 3 + c 1, z 3 + c 2],
    ![z 3 + z 1, z 3 + c 0 + z 2, z 3 + c 1, z 3 + c 2, z 3 + c 3],
    ![z 3 + c 0, z 3 + c 1, z 3 + c 2, z 3 + c 3, z 3 + c 4],
    ![z 3 + c 1, z 3 + c 2, z 3 + c 3, z 3 + c 4, z 3],
    ![z 3 + c 2, z 3 + c 3, z 3 + c 4, z 3, z 3 + z 4]
  ]

def RationalOneCompletable (c : RationalTargetClass) : Prop :=
  ∃ z : RationalCompletion, E2.RankLETwo (rationalOneMatrix c z)

instance (c : RationalTargetClass) : Decidable (RationalOneCompletable c) := by
  unfold RationalOneCompletable
  infer_instance

/-- The six nonzero rank-at-most-two target classes. -/
def RationalOneLowClass (c : RationalTargetClass) : Prop :=
  c = rationalWord 0 0 0 0 1 ∨
  c = rationalWord 0 1 0 0 1 ∨
  c = rationalWord 1 0 0 1 0 ∨
  c = rationalWord 1 0 1 0 1 ∨
  c = rationalWord 1 1 0 1 1 ∨
  c = rationalWord 1 1 1 1 1

instance (c : RationalTargetClass) : Decidable (RationalOneLowClass c) := by
  unfold RationalOneLowClass
  infer_instance

private theorem not_completable_of_minor {c : RationalTargetClass}
    {r s : Fin 10}
    (hcover : ∀ z : RationalCompletion,
      E2.minorThree (rationalOneMatrix c z) r s = 1) :
    ¬ RationalOneCompletable c := by
  rintro ⟨z, hz⟩
  exact E2.not_rankLETwo_of_minor_eq_one (hcover z) hz

private theorem not_completable_of_two_minors {c : RationalTargetClass}
    {r₀ s₀ r₁ s₁ : Fin 10}
    (hcover : ∀ z : RationalCompletion,
      E2.minorThree (rationalOneMatrix c z) r₀ s₀ = 1 ∨
      E2.minorThree (rationalOneMatrix c z) r₁ s₁ = 1) :
    ¬ RationalOneCompletable c := by
  rintro ⟨z, hz⟩
  rcases hcover z with h | h
  · exact E2.not_rankLETwo_of_minor_eq_one h hz
  · exact E2.not_rankLETwo_of_minor_eq_one h hz

private theorem not_completable_of_three_minors {c : RationalTargetClass}
    {r₀ s₀ r₁ s₁ r₂ s₂ : Fin 10}
    (hcover : ∀ z : RationalCompletion,
      E2.minorThree (rationalOneMatrix c z) r₀ s₀ = 1 ∨
      E2.minorThree (rationalOneMatrix c z) r₁ s₁ = 1 ∨
      E2.minorThree (rationalOneMatrix c z) r₂ s₂ = 1) :
    ¬ RationalOneCompletable c := by
  rintro ⟨z, hz⟩
  rcases hcover z with h | h | h
  · exact E2.not_rankLETwo_of_minor_eq_one h hz
  · exact E2.not_rankLETwo_of_minor_eq_one h hz
  · exact E2.not_rankLETwo_of_minor_eq_one h hz

private theorem comp_00000 :
    RationalOneCompletable (rationalWord 0 0 0 0 0) := by
  refine ⟨rationalWord 0 0 0 0 0, ?_⟩
  decide

private theorem comp_00001 :
    RationalOneCompletable (rationalWord 0 0 0 0 1) := by
  refine ⟨rationalWord 0 0 1 0 0, ?_⟩
  decide

private theorem comp_01001 :
    RationalOneCompletable (rationalWord 0 1 0 0 1) := by
  refine ⟨rationalWord 1 1 0 0 0, ?_⟩
  decide

private theorem comp_10010 :
    RationalOneCompletable (rationalWord 1 0 0 1 0) := by
  refine ⟨rationalWord 0 1 0 0 1, ?_⟩
  decide

private theorem comp_10101 :
    RationalOneCompletable (rationalWord 1 0 1 0 1) := by
  refine ⟨rationalWord 1 0 0 0 1, ?_⟩
  decide

private theorem comp_11011 :
    RationalOneCompletable (rationalWord 1 1 0 1 1) := by
  refine ⟨rationalWord 1 0 0 0 1, ?_⟩
  decide

private theorem comp_11111 :
    RationalOneCompletable (rationalWord 1 1 1 1 1) := by
  refine ⟨rationalWord 0 1 0 1 1, ?_⟩
  decide

private theorem cover_00010 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 0 1 0) z) 0 6 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 0 1 0) z) 0 9 = 1 := by
  decide

private theorem cover_00011 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 0 1 1) z) 0 3 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 0 1 1) z) 2 9 = 1 := by
  decide

private theorem cover_00100 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 1 0 0) z) 1 8 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 1 0 0) z) 0 6 = 1 := by
  decide

private theorem cover_00101 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 1 0 1) z) 0 9 = 1 := by
  decide

private theorem cover_00110 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 1 1 0) z) 0 9 = 1 := by
  decide

private theorem cover_00111 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 1 1 1) z) 0 5 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 0 0 1 1 1) z) 7 9 = 1 := by
  decide

private theorem cover_01000 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 0 0 0) z) 0 9 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 0 0 0) z) 6 9 = 1 := by
  decide

private theorem cover_01010 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 0 1 0) z) 1 9 = 1 := by
  decide

private theorem cover_01011 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 0 1 1) z) 0 9 = 1 := by
  decide

private theorem cover_01100 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 1 0 0) z) 0 9 = 1 := by
  decide

private theorem cover_01101 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 1 0 1) z) 1 9 = 1 := by
  decide

private theorem cover_01110 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 1 1 0) z) 3 4 = 1 := by
  decide

private theorem cover_01111 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 1 1 1) z) 3 5 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 0 1 1 1 1) z) 9 9 = 1 := by
  decide

private theorem cover_10000 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 0 0 0 0) z) 9 9 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 1 0 0 0 0) z) 3 9 = 1 := by
  decide

private theorem cover_10001 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 0 0 0 1) z) 3 3 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 1 0 0 0 1) z) 0 9 = 1 := by
  decide

private theorem cover_10011 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 0 0 1 1) z) 0 9 = 1 := by
  decide

private theorem cover_10100 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 0 1 0 0) z) 0 9 = 1 := by
  decide

private theorem cover_10110 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 0 1 1 0) z) 3 4 = 1 := by
  decide

private theorem cover_10111 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 0 1 1 1) z) 6 9 = 1 := by
  decide

private theorem cover_11000 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 0 0 0) z) 6 9 = 1 := by
  decide

private theorem cover_11001 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 0 0 1) z) 0 9 = 1 := by
  decide

private theorem cover_11010 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 0 1 0) z) 0 9 = 1 := by
  decide

private theorem cover_11100 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 1 0 0) z) 1 9 = 1 := by
  decide

private theorem cover_11101 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 1 0 1) z) 0 6 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 1 0 1) z) 0 9 = 1 := by
  decide

private theorem cover_11110 : ∀ z : RationalCompletion,
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 1 1 0) z) 3 4 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 1 1 0) z) 5 5 = 1 ∨
    E2.minorThree (rationalOneMatrix (rationalWord 1 1 1 1 0) z) 0 0 = 1 := by
  decide

/-- Exact rational fixed-block certificate.  The proof uses explicit
completions for the seven admissible classes and one-to-three displayed
minors for every excluded class. -/
theorem rationalOne_completable_iff (c : RationalTargetClass) :
    RationalOneCompletable c ↔ c = 0 ∨ RationalOneLowClass c := by
  rcases f2_eq_zero_or_one (c 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (c 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (c 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (c 3) with h3 | h3 <;>
          rcases f2_eq_zero_or_one (c 4) with h4 | h4
  all_goals
    have hc := rationalTargetClass_eq_word c
    simp only [h0, h1, h2, h3, h4] at hc
    subst c
  · exact iff_of_true comp_00000 (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_10000) (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_01000) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_11000) (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_00100) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_10100) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_01100) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_11100) (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_00010) (by decide)
  · exact iff_of_true comp_10010 (by decide)
  · exact iff_of_false (not_completable_of_minor cover_01010) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_11010) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_00110) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_10110) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_01110) (by decide)
  · exact iff_of_false (not_completable_of_three_minors cover_11110) (by decide)
  · exact iff_of_true comp_00001 (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_10001) (by decide)
  · exact iff_of_true comp_01001 (by decide)
  · exact iff_of_false (not_completable_of_minor cover_11001) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_00101) (by decide)
  · exact iff_of_true comp_10101 (by decide)
  · exact iff_of_false (not_completable_of_minor cover_01101) (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_11101) (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_00011) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_10011) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_01011) (by decide)
  · exact iff_of_true comp_11011 (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_00111) (by decide)
  · exact iff_of_false (not_completable_of_minor cover_10111) (by decide)
  · exact iff_of_false (not_completable_of_two_minors cover_01111) (by decide)
  · exact iff_of_true comp_11111 (by decide)

/-- The three low classes produced by a genuine high defect birth. -/
def RationalOneHighClass (c : RationalTargetClass) : Prop :=
  c = rationalWord 0 0 0 0 1 ∨
  c = rationalWord 1 0 1 0 1 ∨
  c = rationalWord 1 1 1 1 1

instance (c : RationalTargetClass) : Decidable (RationalOneHighClass c) := by
  unfold RationalOneHighClass
  infer_instance

/-- The remaining three low classes are the nonzero points of the
degree-two-place line. -/
def RationalOneQuadraticBirthClass (c : RationalTargetClass) : Prop :=
  c = rationalWord 0 1 0 0 1 ∨
  c = rationalWord 1 0 0 1 0 ∨
  c = rationalWord 1 1 0 1 1

instance (c : RationalTargetClass) : Decidable
    (RationalOneQuadraticBirthClass c) := by
  unfold RationalOneQuadraticBirthClass
  infer_instance

theorem rationalOne_low_split {c : RationalTargetClass}
    (hc : RationalOneLowClass c) :
    RationalOneHighClass c ∨ RationalOneQuadraticBirthClass c := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [RationalOneHighClass, RationalOneQuadraticBirthClass, rationalWord]

/-- Distinct high-shadow classes do not have high-shadow sum. -/
theorem rationalOne_high_sum_not_high
    {x y : RationalTargetClass}
    (hx : RationalOneHighClass x) (hy : RationalOneHighClass y)
    (hne : x ≠ y) : ¬ RationalOneHighClass (x + y) := by
  rcases hx with rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl <;>
      simp_all [RationalOneHighClass, rationalWord]

/-- A translated family of shadows attached to one fixed high colour. -/
def IsRationalOneHighShadowFamily (A : Set RationalTargetClass) : Prop :=
  0 ∈ A ∧
    (∀ x ∈ A, x ≠ 0 → RationalOneHighClass x) ∧
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → RationalOneHighClass (x + y))

private def rationalHigh0 : RationalTargetClass := rationalWord 0 0 0 0 1
private def rationalHigh1 : RationalTargetClass := rationalWord 1 0 1 0 1
private def rationalHigh2 : RationalTargetClass := rationalWord 1 1 1 1 1

private theorem rational_high_cases {x : RationalTargetClass}
    (hx : RationalOneHighClass x) :
    x = rationalHigh0 ∨ x = rationalHigh1 ∨ x = rationalHigh2 := by
  simpa [RationalOneHighClass, rationalHigh0, rationalHigh1,
    rationalHigh2] using hx

private def rationalHighLine (v : RationalTargetClass) :
    Submodule F₂ RationalTargetClass :=
  Submodule.span F₂ ({v} : Set RationalTargetClass)

private theorem rationalHighLine_finrank_le_one (v : RationalTargetClass) :
    Module.finrank F₂ (rationalHighLine v) ≤ 1 := by
  letI : Fintype ({v} : Set RationalTargetClass) := Fintype.ofFinite _
  exact (finrank_span_le_card ({v} : Set RationalTargetClass)).trans (by simp)

/-- The admissible shadows of one fixed high colour have affine dimension at
most one.  This is the precise linear-algebra consequence of the absence of
a projective line. -/
theorem rationalOne_highShadowFamily_span_finrank_le_one
    (A : Set RationalTargetClass) (hA : IsRationalOneHighShadowFamily A) :
    Module.finrank F₂ (Submodule.span F₂ A) ≤ 1 := by
  rcases hA with ⟨_hzero, hlow, hpair⟩
  by_cases h0 : rationalHigh0 ∈ A
  · have hsub : A ⊆ rationalHighLine rationalHigh0 := by
      intro x hx
      by_cases hx0 : x = 0
      · subst x
        exact Submodule.zero_mem _
      rcases rational_high_cases (hlow x hx hx0) with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exfalso
        exact rationalOne_high_sum_not_high
          (hlow rationalHigh1 hx (by decide))
          (hlow rationalHigh0 h0 (by decide)) (by decide)
          (hpair rationalHigh1 hx rationalHigh0 h0 (by decide))
      · exfalso
        exact rationalOne_high_sum_not_high
          (hlow rationalHigh2 hx (by decide))
          (hlow rationalHigh0 h0 (by decide)) (by decide)
          (hpair rationalHigh2 hx rationalHigh0 h0 (by decide))
    exact (Submodule.finrank_mono (Submodule.span_le.mpr hsub)).trans
      (rationalHighLine_finrank_le_one rationalHigh0)
  by_cases h1 : rationalHigh1 ∈ A
  · have hsub : A ⊆ rationalHighLine rationalHigh1 := by
      intro x hx
      by_cases hx0 : x = 0
      · subst x
        exact Submodule.zero_mem _
      rcases rational_high_cases (hlow x hx hx0) with rfl | rfl | rfl
      · exact (h0 hx).elim
      · exact Submodule.subset_span (by simp)
      · exfalso
        exact rationalOne_high_sum_not_high
          (hlow rationalHigh2 hx (by decide))
          (hlow rationalHigh1 h1 (by decide)) (by decide)
          (hpair rationalHigh2 hx rationalHigh1 h1 (by decide))
    exact (Submodule.finrank_mono (Submodule.span_le.mpr hsub)).trans
      (rationalHighLine_finrank_le_one rationalHigh1)
  have hsub : A ⊆ rationalHighLine rationalHigh2 := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact Submodule.zero_mem _
    rcases rational_high_cases (hlow x hx hx0) with rfl | rfl | rfl
    · exact (h0 hx).elim
    · exact (h1 hx).elim
    · exact Submodule.subset_span (by simp)
  exact (Submodule.finrank_mono (Submodule.span_le.mpr hsub)).trans
    (rationalHighLine_finrank_le_one rationalHigh2)

end
end N5
end UnrestrictedBooleanMul
