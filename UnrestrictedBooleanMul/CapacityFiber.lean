import UnrestrictedBooleanMul.CapacityRelation

/-! Fiber decomposition of capacity. All fibers, including the zero fiber,
are accounted for. The index family may repeat points; its coverage is an
explicit hypothesis, not a property assumed of a saved catalogue. -/
namespace UnrestrictedBooleanMul.Capacity
noncomputable section
open Module Submodule

variable {K M X : Type*} [Field K] [AddCommGroup M] [Module K M]

def fiber (T : Submodule K M) (G : Set M) (q : M ⧸ T) : Set M :=
  {x | x ∈ G ∧ T.mkQ x = q}

def zeroSpan (T : Submodule K M) (G : Set M) : Submodule K M :=
  span K (fiber T G 0)

def displacement (T : Submodule K M) (G : Set M) (q : X → M ⧸ T)
    (lift : X → M) : Submodule K M :=
  zeroSpan T G ⊔ span K {z | ∃ i, ∃ x ∈ fiber T G (q i), z = x - lift i}

theorem zeroSpan_le (T : Submodule K M) (G : Set M) : zeroSpan T G ≤ T := by
  apply span_le.mpr
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero T).1 hx.2

theorem displacement_le (T : Submodule K M) (G : Set M) (q : X → M ⧸ T)
    (lift : X → M) (hlift : ∀ i, lift i ∈ fiber T G (q i)) :
    displacement T G q lift ≤ T := by
  apply sup_le (zeroSpan_le T G)
  apply span_le.mpr
  rintro z ⟨i, x, hx, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero T).1
  change T.mkQ (x - lift i) = 0
  rw [map_sub, hx.2, (hlift i).2, sub_self]

theorem displacement_le_spanAt (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) (q : X → M ⧸ T) (lift : X → M)
    (hq : ∀ i, q i ∈ Q) (hlift : ∀ i, lift i ∈ fiber T G (q i)) :
    displacement T G q lift ≤ spanAt T G Q := by
  apply sup_le
  · apply span_le.mpr
    intro x hx
    exact subset_span ⟨hx.1, hx.2.symm ▸ Q.zero_mem⟩
  · apply span_le.mpr
    rintro z ⟨i, x, hx, rfl⟩
    exact (spanAt T G Q).sub_mem
      (subset_span ⟨hx.1, hx.2.symm ▸ hq i⟩)
      (subset_span ⟨(hlift i).1, (hlift i).2.symm ▸ hq i⟩)

/-- Coverage is required for every nonzero populated quotient point. No
uniqueness, ordering, or representative normalization is required. -/
theorem spanAt_eq_displacement_sup_lifts (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) (q : X → M ⧸ T) (lift : X → M)
    (hq : ∀ i, q i ∈ Q) (hlift : ∀ i, lift i ∈ fiber T G (q i))
    (hcover : ∀ x ∈ G, T.mkQ x ∈ Q → T.mkQ x ≠ 0 → ∃ i, q i = T.mkQ x) :
    spanAt T G Q = displacement T G q lift ⊔ span K (Set.range lift) := by
  apply le_antisymm
  · apply span_le.mpr
    intro x hx
    by_cases hz : T.mkQ x = 0
    · exact mem_sup_left (mem_sup_left (subset_span ⟨hx.1, hz⟩))
    · obtain ⟨i, hi⟩ := hcover x hx.1 hx.2 hz
      have hd : x - lift i ∈ displacement T G q lift :=
        mem_sup_right (subset_span ⟨i, x, ⟨hx.1, hi.symm⟩, rfl⟩)
      have hr : lift i ∈ span K (Set.range lift) := subset_span ⟨i, rfl⟩
      have hs := (displacement T G q lift ⊔ span K (Set.range lift)).add_mem
        (mem_sup_left hd) (mem_sup_right hr)
      simpa using hs
  · apply sup_le (displacement_le_spanAt T G Q q lift hq hlift)
    apply span_le.mpr
    rintro x ⟨i, rfl⟩
    exact subset_span ⟨(hlift i).1, (hlift i).2.symm ▸ hq i⟩

/-- Local displacement is independent of the chosen lift in each fiber. -/
theorem displacement_change_lifts (T : Submodule K M) (G : Set M) (q : X → M ⧸ T)
    (lift lift' : X → M) (hlift : ∀ i, lift i ∈ fiber T G (q i))
    (hlift' : ∀ i, lift' i ∈ fiber T G (q i)) :
    displacement T G q lift = displacement T G q lift' := by
  have hle : ∀ (l l' : X → M), (∀ i, l i ∈ fiber T G (q i)) →
      displacement T G q l ≤ displacement T G q l' := by
    intro l l' hl
    apply sup_le le_sup_left
    apply span_le.mpr
    rintro z ⟨i, x, hx, rfl⟩
    have hx' : x - l' i ∈ displacement T G q l' :=
      mem_sup_right (subset_span ⟨i, x, hx, rfl⟩)
    have hl' : l i - l' i ∈ displacement T G q l' :=
      mem_sup_right (subset_span ⟨i, l i, hl i, rfl⟩)
    have hs := (displacement T G q l').sub_mem hx' hl'
    change x - l i ∈ displacement T G q l'
    simpa only [sub_sub_sub_cancel_right] using hs
  exact le_antisymm (hle lift lift' hlift) (hle lift' lift hlift')

variable [FiniteDimensional K M] [Fintype X]

theorem value_fiber_formula (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) (q : X → M ⧸ T) (lift : X → M)
    (hq : ∀ i, q i ∈ Q) (hlift : ∀ i, lift i ∈ fiber T G (q i))
    (hcover : ∀ x ∈ G, T.mkQ x ∈ Q → T.mkQ x ≠ 0 → ∃ i, q i = T.mkQ x) :
    value T G Q = finrank K (displacement T G q lift) +
      finrank K (LinearMap.range (relationMap T (displacement T G q lift) lift q)) :=
  relationMap_finrank T (displacement T G q lift) (spanAt T G Q) lift q
    (displacement_le T G q lift hlift) (fun i => (hlift i).2)
    (spanAt_eq_displacement_sup_lifts T G Q q lift hq hlift hcover)

/-- The actual nonzero populated points, not a catalogue supplied by a caller. -/
def Populated (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) :=
  {q : M ⧸ T // q ∈ Q ∧ q ≠ 0 ∧ (fiber T G q).Nonempty}

instance populatedFintype [Finite M] (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) : Fintype (Populated T G Q) := by
  letI : Finite (M ⧸ T) := Finite.of_surjective T.mkQ T.mkQ_surjective
  unfold Populated
  exact Fintype.ofFinite _

def populatedQuotient (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T))
    (q : Populated T G Q) : M ⧸ T := q.1

def populatedLift (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T))
    (q : Populated T G Q) : M := q.2.2.2.choose

omit [FiniteDimensional K M] in
theorem populatedLift_mem (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T))
    (q : Populated T G Q) : populatedLift T G Q q ∈ fiber T G (populatedQuotient T G Q q) :=
  q.2.2.2.choose_spec

omit [FiniteDimensional K M] in
theorem populatedQuotient_complete (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) (x : M) (hx : x ∈ G) (hQ : T.mkQ x ∈ Q)
    (hne : T.mkQ x ≠ 0) : ∃ i, populatedQuotient T G Q i = T.mkQ x :=
  ⟨⟨T.mkQ x, hQ, hne, x, hx, rfl⟩, rfl⟩

def localDisplacement (T : Submodule K M) (G : Set M) (Q : Submodule K (M ⧸ T)) :
    Submodule K M := displacement T G (populatedQuotient T G Q) (populatedLift T G Q)

def populatedRelationMap [Finite M] (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) :
    relationKernel T (populatedQuotient T G Q) →ₗ[K] M ⧸ localDisplacement T G Q :=
  relationMap T (localDisplacement T G Q) (populatedLift T G Q) (populatedQuotient T G Q)

/-- The canonical formula has no catalogue-coverage or lift-validity premise:
both are discharged by the semantic populated-point definition. -/
theorem value_populated_formula [Finite M] (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) :
    value T G Q = finrank K (localDisplacement T G Q) +
      finrank K (LinearMap.range (populatedRelationMap T G Q)) :=
  value_fiber_formula T G Q (populatedQuotient T G Q) (populatedLift T G Q)
    (fun i => i.2.1) (populatedLift_mem T G Q) (populatedQuotient_complete T G Q)

/-- Rank-nullity exposes the remaining quantitative obligation without
mistaking an identity for a bound on the relation image. -/
theorem value_add_kernel_add_populated_span [Finite M] (T : Submodule K M) (G : Set M)
    (Q : Submodule K (M ⧸ T)) :
    value T G Q + finrank K (LinearMap.ker (populatedRelationMap T G Q)) +
      finrank K (span K (Set.range (populatedQuotient T G Q))) =
        finrank K (localDisplacement T G Q) + Fintype.card (Populated T G Q) := by
  have hv := value_populated_formula T G Q
  have hr := (populatedRelationMap T G Q).finrank_range_add_finrank_ker
  have hc := relationKernel_finrank_add_span T (populatedQuotient T G Q)
  omega

#check zeroSpan_le
#check displacement_le
#check displacement_le_spanAt
#check spanAt_eq_displacement_sup_lifts
#check displacement_change_lifts
#check value_fiber_formula
#check populatedLift_mem
#check populatedQuotient_complete
#check value_populated_formula
#check value_add_kernel_add_populated_span
#print axioms zeroSpan_le
#print axioms displacement_le
#print axioms displacement_le_spanAt
#print axioms spanAt_eq_displacement_sup_lifts
#print axioms displacement_change_lifts
#print axioms value_fiber_formula
#print axioms populatedLift_mem
#print axioms populatedQuotient_complete
#print axioms value_populated_formula
#print axioms value_add_kernel_add_populated_span
end
end UnrestrictedBooleanMul.Capacity
