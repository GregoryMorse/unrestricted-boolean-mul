import UnrestrictedBooleanMul.N5.E2.WStarRank
import UnrestrictedBooleanMul.N5.E2.WPQRank
import UnrestrictedBooleanMul.N5.E2.WThreePRank

/-!
# Geometry of the two-defect low-rank class sets

This file extracts the affine-dimension consequences of equations (10.6),
(10.8), and (10.11).  A family is translated to contain zero, so pairwise
differences are sums.  The proofs use only the displayed class equations and
small linear spans; no circuit or completion space is enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

noncomputable section

/-- A zero-based family whose nonzero members and pairwise differences lie in
the indicated class predicate. -/
def IsZeroBasedPairwiseFamily
    (Low : TargetClass → Prop) (A : Set TargetClass) : Prop :=
  0 ∈ A ∧
    (∀ x ∈ A, x ≠ 0 → Low x) ∧
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → Low (x + y))

private def star0 : TargetClass := word 0 0 0 1
private def star1 : TargetClass := word 1 0 0 1
private def star2 : TargetClass := word 1 1 1 0

private def starLine (v : TargetClass) : Submodule F₂ TargetClass :=
  Submodule.span F₂ ({v} : Set TargetClass)

private theorem star_low_cases {x : TargetClass} (hx : WStarLowClass x) :
    x = star0 ∨ x = star1 ∨ x = star2 := by
  simpa [WStarLowClass, star0, star1, star2, word] using hx

private theorem star_distinct_low_sum_not_low
    {x y : TargetClass} (hx : WStarLowClass x) (hy : WStarLowClass y)
    (hne : x ≠ y) : ¬ WStarLowClass (x + y) := by
  rcases star_low_cases hx with rfl | rfl | rfl <;>
    rcases star_low_cases hy with rfl | rfl | rfl <;>
      simp_all [WStarLowClass, star0, star1, star2, word]

private theorem starLine_finrank_le_one (v : TargetClass) :
    Module.finrank F₂ (starLine v) ≤ 1 := by
  letI : Fintype ({v} : Set TargetClass) := Fintype.ofFinite _
  exact (finrank_span_le_card ({v} : Set TargetClass)).trans (by simp)

/-- Equation (10.6): a zero-based pairwise-difference family has linear span
of dimension at most one. -/
theorem wStar_pairwise_span_finrank_le_one
    (A : Set TargetClass) (hA : IsZeroBasedPairwiseFamily WStarLowClass A) :
    Module.finrank F₂ (Submodule.span F₂ A) ≤ 1 := by
  rcases hA with ⟨hzero, hlow, hpair⟩
  by_cases h0 : star0 ∈ A
  · have hsub : A ⊆ starLine star0 := by
      intro x hx
      by_cases hx0 : x = 0
      · subst x
        exact Submodule.zero_mem _
      have hxl := star_low_cases (hlow x hx hx0)
      rcases hxl with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exfalso
        exact star_distinct_low_sum_not_low
          (hlow star1 hx (by decide)) (hlow star0 h0 (by decide)) (by decide)
          (hpair star1 hx star0 h0 (by decide))
      · exfalso
        exact star_distinct_low_sum_not_low
          (hlow star2 hx (by decide)) (hlow star0 h0 (by decide)) (by decide)
          (hpair star2 hx star0 h0 (by decide))
    exact (Submodule.finrank_mono (Submodule.span_le.mpr hsub)).trans
      (starLine_finrank_le_one star0)
  by_cases h1 : star1 ∈ A
  · have hsub : A ⊆ starLine star1 := by
      intro x hx
      by_cases hx0 : x = 0
      · subst x
        exact Submodule.zero_mem _
      have hxl := star_low_cases (hlow x hx hx0)
      rcases hxl with rfl | rfl | rfl
      · exact (h0 hx).elim
      · exact Submodule.subset_span (by simp)
      · exfalso
        exact star_distinct_low_sum_not_low
          (hlow star2 hx (by decide)) (hlow star1 h1 (by decide)) (by decide)
          (hpair star2 hx star1 h1 (by decide))
    exact (Submodule.finrank_mono (Submodule.span_le.mpr hsub)).trans
      (starLine_finrank_le_one star1)
  have hsub : A ⊆ starLine star2 := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact Submodule.zero_mem _
    rcases star_low_cases (hlow x hx hx0) with rfl | rfl | rfl
    · exact (h0 hx).elim
    · exact (h1 hx).elim
    · exact Submodule.subset_span (by simp)
  exact (Submodule.finrank_mono (Submodule.span_le.mpr hsub)).trans
    (starLine_finrank_le_one star2)

/-! ## The two-rational planes -/

private def pq0 : TargetClass := word 0 0 1 0
private def pq1 : TargetClass := word 0 1 0 1
private def pq2 : TargetClass := word 0 1 1 1
private def pq3 : TargetClass := word 1 0 0 0
private def pq4 : TargetClass := word 1 0 0 1
private def pq5 : TargetClass := word 1 0 1 1
private def pq6 : TargetClass := word 1 1 1 1

def WPQPlaneAClass (x : TargetClass) : Prop :=
  x = 0 ∨ x = pq0 ∨ x = pq1 ∨ x = pq2

def WPQPlaneBClass (x : TargetClass) : Prop :=
  x = 0 ∨ x = pq0 ∨ x = pq4 ∨ x = pq5

def WPQPlaneCClass (x : TargetClass) : Prop :=
  x = 0 ∨ x = pq2 ∨ x = pq3 ∨ x = pq6

def wPQPlaneA : Submodule F₂ TargetClass :=
  Submodule.span F₂ (Set.range (![pq0, pq1] : Fin 2 → TargetClass))

def wPQPlaneB : Submodule F₂ TargetClass :=
  Submodule.span F₂ (Set.range (![pq0, pq4] : Fin 2 → TargetClass))

def wPQPlaneC : Submodule F₂ TargetClass :=
  Submodule.span F₂ (Set.range (![pq2, pq3] : Fin 2 → TargetClass))

private theorem pq2_eq : pq2 = pq0 + pq1 := by decide
private theorem pq5_eq : pq5 = pq0 + pq4 := by decide
private theorem pq6_eq : pq6 = pq2 + pq3 := by decide

theorem WPQPlaneAClass.mem_space {x : TargetClass} (hx : WPQPlaneAClass x) :
    x ∈ wPQPlaneA := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · rw [pq2_eq]
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨0, rfl⟩)
      (Submodule.subset_span ⟨1, rfl⟩)

theorem WPQPlaneBClass.mem_space {x : TargetClass} (hx : WPQPlaneBClass x) :
    x ∈ wPQPlaneB := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · rw [pq5_eq]
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨0, rfl⟩)
      (Submodule.subset_span ⟨1, rfl⟩)

theorem WPQPlaneCClass.mem_space {x : TargetClass} (hx : WPQPlaneCClass x) :
    x ∈ wPQPlaneC := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · rw [pq6_eq]
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨0, rfl⟩)
      (Submodule.subset_span ⟨1, rfl⟩)

private theorem pairSpan_finrank_le_two (u v : TargetClass) :
    Module.finrank F₂
      (Submodule.span F₂ (Set.range (![u, v] : Fin 2 → TargetClass))) ≤ 2 := by
  letI : Fintype (Set.range (![u, v] : Fin 2 → TargetClass)) :=
    Fintype.ofFinite _
  exact (finrank_span_le_card
    (Set.range (![u, v] : Fin 2 → TargetClass))).trans (by
      rw [Set.toFinset_card]
      simpa using Fintype.card_range_le (![u, v] : Fin 2 → TargetClass))

theorem wPQPlaneA_finrank_le_two : Module.finrank F₂ wPQPlaneA ≤ 2 :=
  pairSpan_finrank_le_two pq0 pq1

theorem wPQPlaneB_finrank_le_two : Module.finrank F₂ wPQPlaneB ≤ 2 :=
  pairSpan_finrank_le_two pq0 pq4

theorem wPQPlaneC_finrank_le_two : Module.finrank F₂ wPQPlaneC ≤ 2 :=
  pairSpan_finrank_le_two pq2 pq3

private theorem target_class_cases (x : TargetClass) :
    x = word (x 3) (x 2) (x 1) (x 0) := targetClass_eq_word x

private theorem compatible_pq1 (x : TargetClass)
    (hx : x = 0 ∨ WPQLowClass x)
    (hsum : x = pq1 ∨ WPQLowClass (x + pq1)) : WPQPlaneAClass x := by
  rcases f2_eq_zero_or_one (x 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (x 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (x 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (x 3) with h3 | h3
  all_goals
    have hw := target_class_cases x
    simp only [h0, h1, h2, h3] at hw
    subst x
  all_goals simp [WPQLowClass, WPQPlaneAClass, pq0, pq1, pq2, word] at *

private theorem compatible_pq4 (x : TargetClass)
    (hx : x = 0 ∨ WPQLowClass x)
    (hsum : x = pq4 ∨ WPQLowClass (x + pq4)) : WPQPlaneBClass x := by
  rcases f2_eq_zero_or_one (x 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (x 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (x 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (x 3) with h3 | h3
  all_goals
    have hw := target_class_cases x
    simp only [h0, h1, h2, h3] at hw
    subst x
  all_goals simp [WPQLowClass, WPQPlaneBClass, pq0, pq4, pq5, word] at *

private theorem compatible_pq3 (x : TargetClass)
    (hx : x = 0 ∨ WPQLowClass x)
    (hsum : x = pq3 ∨ WPQLowClass (x + pq3)) : WPQPlaneCClass x := by
  rcases f2_eq_zero_or_one (x 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (x 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (x 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (x 3) with h3 | h3
  all_goals
    have hw := target_class_cases x
    simp only [h0, h1, h2, h3] at hw
    subst x
  all_goals simp [WPQLowClass, WPQPlaneCClass, pq2, pq3, pq6, word] at *

private theorem compatible_pq6 (x : TargetClass)
    (hx : x = 0 ∨ WPQLowClass x)
    (hsum : x = pq6 ∨ WPQLowClass (x + pq6)) : WPQPlaneCClass x := by
  rcases f2_eq_zero_or_one (x 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (x 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (x 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (x 3) with h3 | h3
  all_goals
    have hw := target_class_cases x
    simp only [h0, h1, h2, h3] at hw
    subst x
  all_goals simp [WPQLowClass, WPQPlaneCClass, pq2, pq3, pq6, word] at *

private theorem reduced_pq2 (x : TargetClass)
    (hx : x = 0 ∨ WPQLowClass x)
    (hsum : x = pq2 ∨ WPQLowClass (x + pq2))
    (h1 : x ≠ pq1) (h4 : x ≠ pq4) (h3 : x ≠ pq3)
    (h6 : x ≠ pq6) : WPQPlaneAClass x := by
  rcases f2_eq_zero_or_one (x 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (x 1) with hbit1 | hbit1 <;>
      rcases f2_eq_zero_or_one (x 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (x 3) with hbit3 | hbit3
  all_goals
    have hw := target_class_cases x
    simp only [h0, hbit1, h2, hbit3] at hw
    subst x
  all_goals simp [WPQLowClass, WPQPlaneAClass, pq0, pq1, pq2, pq3,
    pq4, pq6, word] at *

private theorem reduced_pq5 (x : TargetClass)
    (hx : x = 0 ∨ WPQLowClass x)
    (hsum : x = pq5 ∨ WPQLowClass (x + pq5))
    (h1 : x ≠ pq1) (h4 : x ≠ pq4) (h3 : x ≠ pq3)
    (h6 : x ≠ pq6) (h2 : x ≠ pq2) : WPQPlaneBClass x := by
  rcases f2_eq_zero_or_one (x 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (x 1) with hbit1 | hbit1 <;>
      rcases f2_eq_zero_or_one (x 2) with hbit2 | hbit2 <;>
        rcases f2_eq_zero_or_one (x 3) with hbit3 | hbit3
  all_goals
    have hw := target_class_cases x
    simp only [h0, hbit1, hbit2, hbit3] at hw
    subst x
  all_goals simp [WPQLowClass, WPQPlaneBClass, pq0, pq1, pq2, pq3,
    pq4, pq5, pq6, word] at *

private theorem reduced_final (x : TargetClass)
    (hx : x = 0 ∨ WPQLowClass x)
    (h1 : x ≠ pq1) (h4 : x ≠ pq4) (h3 : x ≠ pq3)
    (h6 : x ≠ pq6) (h2 : x ≠ pq2) (h5 : x ≠ pq5) :
    WPQPlaneAClass x := by
  rcases f2_eq_zero_or_one (x 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (x 1) with hbit1 | hbit1 <;>
      rcases f2_eq_zero_or_one (x 2) with hbit2 | hbit2 <;>
        rcases f2_eq_zero_or_one (x 3) with hbit3 | hbit3
  all_goals
    have hw := target_class_cases x
    simp only [h0, hbit1, hbit2, hbit3] at hw
    subst x
  all_goals simp [WPQLowClass, WPQPlaneAClass, pq0, pq1, pq2, pq3,
    pq4, pq5, pq6, word] at *

/-- Equation (10.9): every zero-based two-rational pairwise-difference family
lies in one of the three displayed planes. -/
theorem wPQ_pairwise_plane_classification
    (A : Set TargetClass) (hA : IsZeroBasedPairwiseFamily WPQLowClass A) :
    (∀ x ∈ A, WPQPlaneAClass x) ∨
      (∀ x ∈ A, WPQPlaneBClass x) ∨
      (∀ x ∈ A, WPQPlaneCClass x) := by
  rcases hA with ⟨hzero, hlow, hpair⟩
  have classOf (x : TargetClass) (hx : x ∈ A) : x = 0 ∨ WPQLowClass x := by
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr (hlow x hx hx0)
  have sumOf (p x : TargetClass) (hp : p ∈ A) (hx : x ∈ A) :
      x = p ∨ WPQLowClass (x + p) := by
    by_cases hxp : x = p
    · exact Or.inl hxp
    · exact Or.inr (hpair x hx p hp hxp)
  by_cases h1A : pq1 ∈ A
  · exact Or.inl (fun x hx => compatible_pq1 x (classOf x hx)
      (sumOf pq1 x h1A hx))
  by_cases h4A : pq4 ∈ A
  · exact Or.inr (Or.inl (fun x hx => compatible_pq4 x (classOf x hx)
      (sumOf pq4 x h4A hx)))
  by_cases h3A : pq3 ∈ A
  · exact Or.inr (Or.inr (fun x hx => compatible_pq3 x (classOf x hx)
      (sumOf pq3 x h3A hx)))
  by_cases h6A : pq6 ∈ A
  · exact Or.inr (Or.inr (fun x hx => compatible_pq6 x (classOf x hx)
      (sumOf pq6 x h6A hx)))
  by_cases h2A : pq2 ∈ A
  · exact Or.inl (fun x hx => reduced_pq2 x (classOf x hx)
      (sumOf pq2 x h2A hx)
      (fun h => h1A (h ▸ hx)) (fun h => h4A (h ▸ hx))
      (fun h => h3A (h ▸ hx)) (fun h => h6A (h ▸ hx)))
  by_cases h5A : pq5 ∈ A
  · exact Or.inr (Or.inl (fun x hx => reduced_pq5 x (classOf x hx)
      (sumOf pq5 x h5A hx)
      (fun h => h1A (h ▸ hx)) (fun h => h4A (h ▸ hx))
      (fun h => h3A (h ▸ hx)) (fun h => h6A (h ▸ hx))
      (fun h => h2A (h ▸ hx))))
  exact Or.inl (fun x hx => reduced_final x (classOf x hx)
    (fun h => h1A (h ▸ hx)) (fun h => h4A (h ▸ hx))
    (fun h => h3A (h ▸ hx)) (fun h => h6A (h ▸ hx))
    (fun h => h2A (h ▸ hx)) (fun h => h5A (h ▸ hx)))

theorem wPQ_pairwise_span_finrank_le_two
    (A : Set TargetClass) (hA : IsZeroBasedPairwiseFamily WPQLowClass A) :
    Module.finrank F₂ (Submodule.span F₂ A) ≤ 2 := by
  rcases wPQ_pairwise_plane_classification A hA with hA' | hB' | hC'
  · exact (Submodule.finrank_mono (Submodule.span_le.mpr
      (fun x hx => (hA' x hx).mem_space))).trans wPQPlaneA_finrank_le_two
  · exact (Submodule.finrank_mono (Submodule.span_le.mpr
      (fun x hx => (hB' x hx).mem_space))).trans wPQPlaneB_finrank_le_two
  · exact (Submodule.finrank_mono (Submodule.span_le.mpr
      (fun x hx => (hC' x hx).mem_space))).trans wPQPlaneC_finrank_le_two

/-! ## The length-three hyperplane and exceptional plane -/

def wThreeHFunctional : TargetClass →ₗ[F₂] F₂ where
  toFun c := c 3 + c 2 + c 0
  map_add' x y := by
    change (x 3 + y 3) + (x 2 + y 2) + (x 0 + y 0) =
      (x 3 + x 2 + x 0) + (y 3 + y 2 + y 0)
    ring
  map_smul' a x := by
    change a * x 3 + a * x 2 + a * x 0 = a * (x 3 + x 2 + x 0)
    ring

def wThreeHSpace : Submodule F₂ TargetClass := LinearMap.ker wThreeHFunctional

private def h0 : TargetClass := ![1, 0, 0, 1]
private def h1 : TargetClass := ![0, 1, 0, 0]
private def h2 : TargetClass := ![0, 0, 1, 1]

private def hBasis : Fin 3 → TargetClass := ![h0, h1, h2]

private def hSpan : Submodule F₂ TargetClass :=
  Submodule.span F₂ (Set.range hBasis)

private theorem one_add_one_f2 : (1 + 1 : F₂) = 0 :=
  N3Certificate.two_eq_zero_f2

private theorem wThreeHSpace_le_hSpan : wThreeHSpace ≤ hSpan := by
  intro c hc
  have heq : c 3 = c 2 + c 0 := by
    change c 3 + c 2 + c 0 = 0 at hc
    rcases f2_eq_zero_or_one (c 0) with h0 | h0 <;>
      rcases f2_eq_zero_or_one (c 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (c 3) with h3 | h3 <;>
          simp_all [one_add_one_f2]
  have hrep : c = c 0 • h0 + c 1 • h1 + c 2 • h2 := by
    funext i
    fin_cases i <;> simp [h0, h1, h2, heq, add_comm]
  rw [hrep]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))

theorem wThreeHSpace_finrank_le_three :
    Module.finrank F₂ wThreeHSpace ≤ 3 := by
  apply (Submodule.finrank_mono wThreeHSpace_le_hSpan).trans
  letI : Fintype (Set.range hBasis) := Fintype.ofFinite _
  exact (finrank_span_le_card (Set.range hBasis)).trans (by
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le hBasis)

private def threeU : TargetClass := ![1, 0, 0, 0]
private def threeV : TargetClass := ![1, 1, 1, 1]

def wThreeExceptionalPlane : Submodule F₂ TargetClass :=
  Submodule.span F₂
    (Set.range (![threeU, threeV] : Fin 2 → TargetClass))

theorem wThreeExceptionalPlane_finrank_le_three :
    Module.finrank F₂ wThreeExceptionalPlane ≤ 3 :=
  (pairSpan_finrank_le_two threeU threeV).trans (by omega)

private theorem threeU_not_mem_H : threeU ∉ wThreeHSpace := by
  intro h
  have hz := (LinearMap.mem_ker).mp h
  simp [wThreeHFunctional, threeU] at hz

private theorem threeV_not_mem_H : threeV ∉ wThreeHSpace := by
  intro h
  have hz := (LinearMap.mem_ker).mp h
  simp [wThreeHFunctional, threeV, one_add_one_f2] at hz

private theorem H_member_compatible_threeU
    {x : TargetClass} (hxH : x ∈ wThreeHSpace) (hx0 : x ≠ 0)
    (hsum : WThreePLowClass (x + threeU)) :
    x = threeU + threeV := by
  rcases hsum with hH | hu | hv
  · have hsumH : wThreeHFunctional (x + threeU) = 0 := by
      simpa [wThreeHFunctional] using hH.1
    rw [map_add, (LinearMap.mem_ker).mp hxH] at hsumH
    have huval : wThreeHFunctional threeU = 1 := by decide
    simp [huval] at hsumH
  · have hxzero : x = 0 := by
      have hu' : x + threeU = threeU := by
        simpa [threeU] using hu
      apply add_right_cancel (b := threeU)
      simpa using hu'
    exact (hx0 hxzero).elim
  · have hv' : x + threeU = threeV := by
      simpa [threeU, threeV] using hv
    apply add_right_cancel (b := threeU)
    exact hv'.trans (by decide)

private theorem H_member_compatible_threeV
    {x : TargetClass} (hxH : x ∈ wThreeHSpace) (hx0 : x ≠ 0)
    (hsum : WThreePLowClass (x + threeV)) :
    x = threeU + threeV := by
  rcases hsum with hH | hu | hv
  · have hsumH : wThreeHFunctional (x + threeV) = 0 := by
      simpa [wThreeHFunctional] using hH.1
    rw [map_add, (LinearMap.mem_ker).mp hxH] at hsumH
    have hvval : wThreeHFunctional threeV = 1 := by decide
    simp [hvval] at hsumH
  · have hu' : x + threeV = threeU := by
      simpa [threeU, threeV] using hu
    apply add_right_cancel (b := threeV)
    exact hu'.trans (by decide)
  · have hxzero : x = 0 := by
      have hv' : x + threeV = threeV := by
        simpa [threeV] using hv
      apply add_right_cancel (b := threeV)
      simpa using hv'
    exact (hx0 hxzero).elim

private theorem h_member_mem_exception {x : TargetClass}
    (hx : x = threeU + threeV) : x ∈ wThreeExceptionalPlane := by
  rw [hx]
  exact Submodule.add_mem _
    (Submodule.subset_span ⟨0, rfl⟩)
    (Submodule.subset_span ⟨1, rfl⟩)

/-- The consequence following (10.11): every zero-based pairwise-difference
family lies either in the hyperplane or in the exceptional plane. -/
theorem wThreeP_pairwise_plane_classification
    (A : Set TargetClass)
    (hA : IsZeroBasedPairwiseFamily WThreePLowClass A) :
    A ⊆ wThreeHSpace ∨ A ⊆ wThreeExceptionalPlane := by
  rcases hA with ⟨hzero, hlow, hpair⟩
  by_cases huA : threeU ∈ A
  · right
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact Submodule.zero_mem _
    rcases hlow x hx hx0 with hxH | hxu | hxv
    · have hxHmem : x ∈ wThreeHSpace := by
        rw [wThreeHSpace, LinearMap.mem_ker]
        simpa [wThreeHFunctional] using hxH.1
      exact h_member_mem_exception
        (H_member_compatible_threeU hxHmem hxH.2
          (hpair x hx threeU huA (fun h => threeU_not_mem_H (h ▸ hxHmem))))
    · have hxu' : x = threeU := by simpa [threeU] using hxu
      subst x
      exact Submodule.subset_span ⟨0, rfl⟩
    · have hxv' : x = threeV := by simpa [threeV] using hxv
      subst x
      exact Submodule.subset_span ⟨1, rfl⟩
  by_cases hvA : threeV ∈ A
  · right
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact Submodule.zero_mem _
    rcases hlow x hx hx0 with hxH | hxu | hxv
    · have hxHmem : x ∈ wThreeHSpace := by
        rw [wThreeHSpace, LinearMap.mem_ker]
        simpa [wThreeHFunctional] using hxH.1
      have hsum : WThreePLowClass (x + threeV) :=
        hpair x hx threeV hvA (fun h => threeV_not_mem_H (h ▸ hxHmem))
      exact h_member_mem_exception
        (H_member_compatible_threeV hxHmem hxH.2 hsum)
    · have hxu' : x = threeU := by simpa [threeU] using hxu
      exact (huA (hxu' ▸ hx)).elim
    · have hxv' : x = threeV := by simpa [threeV] using hxv
      subst x
      exact Submodule.subset_span ⟨1, rfl⟩
  left
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact Submodule.zero_mem _
  rcases hlow x hx hx0 with hxH | hxu | hxv
  · change wThreeHFunctional x = 0
    simpa [wThreeHFunctional] using hxH.1
  · have hxu' : x = threeU := by simpa [threeU] using hxu
    exact (huA (hxu' ▸ hx)).elim
  · have hxv' : x = threeV := by simpa [threeV] using hxv
    exact (hvA (hxv' ▸ hx)).elim

theorem wThreeP_pairwise_span_finrank_le_three
    (A : Set TargetClass)
    (hA : IsZeroBasedPairwiseFamily WThreePLowClass A) :
    Module.finrank F₂ (Submodule.span F₂ A) ≤ 3 := by
  rcases wThreeP_pairwise_plane_classification A hA with hH | hE
  · exact (Submodule.finrank_mono (Submodule.span_le.mpr hH)).trans
      wThreeHSpace_finrank_le_three
  · exact (Submodule.finrank_mono (Submodule.span_le.mpr hE)).trans
      wThreeExceptionalPlane_finrank_le_three

end
end E2
end N5
end UnrestrictedBooleanMul
