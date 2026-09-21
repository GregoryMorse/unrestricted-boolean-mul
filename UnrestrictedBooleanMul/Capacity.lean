import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Capacity for any finite-dimensional target and any allowed generator set.
No rank-one classification, finite catalogue, or computation is assumed. -/
namespace UnrestrictedBooleanMul.Capacity
noncomputable section
open Module Submodule

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

def spanAt (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) : Submodule K M :=
  Submodule.span K {x | x ∈ G ∧ T.mkQ x ∈ Q}

def value (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) : Nat :=
  finrank K (T ⊓ spanAt T G Q : Submodule K M)

theorem value_le_target (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) :
    value T G Q ≤ finrank K T := Submodule.finrank_mono inf_le_left

omit [FiniteDimensional K M] in
theorem spanAt_remove_zero (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) :
    spanAt T (G \ {0}) Q = spanAt T G Q := by
  apply le_antisymm
  · apply Submodule.span_mono
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  · apply Submodule.span_le.mpr
    intro x hx
    by_cases hzero : x = 0
    · rw [hzero]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨hx.1, hzero⟩, hx.2⟩

omit [FiniteDimensional K M] in
theorem value_remove_zero (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) :
    value T (G \ {0}) Q = value T G Q := by
  unfold value
  rw [spanAt_remove_zero]

theorem value_full_iff (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) :
    value T G Q = finrank K T ↔ T ≤ spanAt T G Q := by
  constructor
  · intro hv
    have heq : T ⊓ spanAt T G Q = T := Submodule.eq_of_le_of_finrank_eq inf_le_left hv
    exact inf_eq_left.mp heq
  · intro hT
    unfold value
    rw [inf_eq_left.mpr hT]

/-- The exact sequence calculation used in the specialized n=5 obstruction. -/
theorem quotient_dimension (T D : Submodule K M) (hT : T ≤ D) :
    finrank K (D.map T.mkQ) + finrank K T = finrank K D := by
  have hr := (T.mkQ.domRestrict D).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hr
  rw [(Submodule.comapSubtypeEquivOfLe hT).finrank_eq] at hr
  exact hr

omit [FiniteDimensional K M] in
theorem spanAt_map_le (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) :
    (spanAt T G Q).map T.mkQ ≤ Q := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  intro x hx
  exact hx.2

theorem presentation_obstruction (T : Submodule K M) (G : Set M) {r : Nat}
    (p : Fin r → M) (hp : ∀ i, p i ∈ G) (hT : T ≤ Submodule.span K (Set.range p)) :
    ∃ Q : Submodule K (M ⧸ T), finrank K Q ≤ r - finrank K T ∧
      value T G Q = finrank K T := by
  classical
  let D := Submodule.span K (Set.range p)
  let Q := D.map T.mkQ
  have hD : finrank K D ≤ r := by
    apply (finrank_span_le_card (Set.range p)).trans
    simpa using (Finset.card_image_le (s := Finset.univ) (f := p))
  have hdim := quotient_dimension T D hT
  have hspan : D ≤ spanAt T G Q := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨hp i, ⟨p i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩⟩
  refine ⟨Q, ?_, (value_full_iff T G Q).mpr (hT.trans hspan)⟩
  change finrank K Q + finrank K T = finrank K D at hdim
  omega

/-- A full-capacity subspace supplies an actual finite generator family,
chosen from G, not just a dimension bound on an arbitrary subspace. -/
theorem presentation_of_full (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) (hcap : value T G Q = finrank K T) :
    ∃ r ≤ finrank K T + finrank K Q, ∃ p : Fin r → M,
      (∀ i, p i ∈ G) ∧ T ≤ Submodule.span K (Set.range p) := by
  let D := spanAt T G Q
  have hT : T ≤ D := (value_full_iff T G Q).mp hcap
  have hdim := quotient_dimension T D hT
  have hmap : finrank K (D.map T.mkQ) ≤ finrank K Q :=
    Submodule.finrank_mono (spanAt_map_le T G Q)
  obtain ⟨p, hp, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq K
    {x | x ∈ G ∧ T.mkQ x ∈ Q}
  refine ⟨_, ?_, p, fun i => (hp i).1, ?_⟩
  · change finrank K D ≤ finrank K T + finrank K Q
    omega
  · rw [hspan]
    exact hT

/-- Uniform capacity criterion, with a concrete generator presentation on
the left and an explicit existential on the right (not an assumed maximum). -/
theorem criterion (T : Submodule K M) (G : Set M) (e : Nat) :
    (∃ r ≤ finrank K T + e, ∃ p : Fin r → M,
      (∀ i, p i ∈ G) ∧ T ≤ Submodule.span K (Set.range p)) ↔
    ∃ Q : Submodule K (M ⧸ T), finrank K Q ≤ e ∧ value T G Q = finrank K T := by
  constructor
  · rintro ⟨r, hr, p, hp, hT⟩
    obtain ⟨Q, hQ, hcap⟩ := presentation_obstruction T G p hp hT
    refine ⟨Q, ?_, hcap⟩
    omega
  · rintro ⟨Q, hQ, hcap⟩
    obtain ⟨r, hr, p, hp, hT⟩ := presentation_of_full T G Q hcap
    exact ⟨r, hr.trans (Nat.add_le_add_left hQ _), p, hp, hT⟩

#check value_full_iff
#check value_le_target
#check spanAt_remove_zero
#check value_remove_zero
#check quotient_dimension
#check spanAt_map_le
#check presentation_obstruction
#check presentation_of_full
#check criterion
#print axioms value_full_iff
#print axioms value_le_target
#print axioms spanAt_remove_zero
#print axioms value_remove_zero
#print axioms quotient_dimension
#print axioms spanAt_map_le
#print axioms presentation_obstruction
#print axioms presentation_of_full
#print axioms criterion
end
end UnrestrictedBooleanMul.Capacity
