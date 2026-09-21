import UnrestrictedBooleanMul.Capacity

/-! The exact relation-map calculation for an arbitrary target subspace.
The proof generalizes N5.RelationMap without importing the n=5 geometry. -/
namespace UnrestrictedBooleanMul.Capacity
noncomputable section
open Module Submodule

variable {K M X : Type*} [Field K] [AddCommGroup M] [Module K M] [Fintype X]

def coefficientSum (v : X → M) : (X → K) →ₗ[K] M where
  toFun a := ∑ x, a x • v x
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

theorem coefficientSum_range (v : X → M) :
    LinearMap.range (coefficientSum v) = span K (Set.range v) := by
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    apply Submodule.sum_mem
    intro x _
    exact Submodule.smul_mem _ _ (subset_span ⟨x, rfl⟩)
  · apply span_le.mpr
    rintro _ ⟨x, rfl⟩
    refine ⟨(Pi.basisFun K X) x, ?_⟩
    classical
    simp [coefficientSum, Pi.basisFun, Pi.single_apply]

def relationKernel (T : Submodule K M) (q : X → M ⧸ T) : Submodule K (X → K) :=
  LinearMap.ker (coefficientSum q)

def relationMap (T D : Submodule K M) (lift : X → M) (q : X → M ⧸ T) :
    relationKernel T q →ₗ[K] M ⧸ D :=
  D.mkQ.comp ((coefficientSum lift).domRestrict (relationKernel T q))

theorem coefficientSum_projection (T : Submodule K M)
    (lift : X → M) (q : X → M ⧸ T) (hq : ∀ x, T.mkQ (lift x) = q x)
    (a : X → K) : T.mkQ (coefficientSum lift a) = coefficientSum q a := by
  simp [coefficientSum, hq]

/-- The image is precisely the target part of W, modulo local displacement.
The presentation and the fact that displacement lies in T are explicit. -/
theorem relationMap_exact (T D W : Submodule K M) (lift : X → M) (q : X → M ⧸ T)
    (hD : D ≤ T) (hq : ∀ x, T.mkQ (lift x) = q x)
    (hW : W = D ⊔ span K (Set.range lift)) :
    (T ⊓ W : Submodule K M).map D.mkQ = LinearMap.range (relationMap T D lift q) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htW : t ∈ D ⊔ span K (Set.range lift) := hW ▸ ht.2
    rcases mem_sup.mp htW with ⟨d, hd, s, hs, rfl⟩
    rw [← coefficientSum_range] at hs
    rcases hs with ⟨a, rfl⟩
    have hsT : coefficientSum lift a ∈ T := by
      simpa using T.sub_mem ht.1 (hD hd)
    have ha0 : coefficientSum q a = 0 := by
      rw [← coefficientSum_projection T lift q hq a]
      exact (Submodule.Quotient.mk_eq_zero T).2 hsT
    refine ⟨⟨a, (LinearMap.mem_ker).2 ha0⟩, ?_⟩
    change D.mkQ (coefficientSum lift a) = D.mkQ (d + coefficientSum lift a)
    have hd0 : D.mkQ d = 0 := (Submodule.Quotient.mk_eq_zero D).2 hd
    rw [map_add, hd0, zero_add]
  · rintro ⟨a, rfl⟩
    have hsT : coefficientSum lift a.1 ∈ T := by
      apply (Submodule.Quotient.mk_eq_zero T).1
      change T.mkQ (coefficientSum lift a.1) = 0
      rw [coefficientSum_projection T lift q hq]
      exact (LinearMap.mem_ker).1 a.2
    have hsSpan : coefficientSum lift a.1 ∈ span K (Set.range lift) := by
      rw [← coefficientSum_range]
      exact ⟨a.1, rfl⟩
    refine ⟨coefficientSum lift a.1, ⟨hsT, ?_⟩, rfl⟩
    rw [hW]
    exact mem_sup_right hsSpan

variable [FiniteDimensional K M]

theorem relationMap_finrank (T D W : Submodule K M) (lift : X → M) (q : X → M ⧸ T)
    (hD : D ≤ T) (hq : ∀ x, T.mkQ (lift x) = q x)
    (hW : W = D ⊔ span K (Set.range lift)) :
    finrank K (T ⊓ W : Submodule K M) =
      finrank K D + finrank K (LinearMap.range (relationMap T D lift q)) := by
  have hDI : D ≤ T ⊓ W := by
    apply le_inf hD
    rw [hW]
    exact le_sup_left
  have hr := quotient_dimension D (T ⊓ W) hDI
  rw [relationMap_exact T D W lift q hD hq hW] at hr
  omega

omit [FiniteDimensional K M] in
theorem relationKernel_finrank_add_span (T : Submodule K M) (q : X → M ⧸ T) :
    finrank K (relationKernel T q) + finrank K (span K (Set.range q)) = Fintype.card X := by
  have h := (coefficientSum (K := K) q).finrank_range_add_finrank_ker
  rw [coefficientSum_range] at h
  change finrank K (span K (Set.range q)) + finrank K (relationKernel T q) = _ at h
  have hf : finrank K (X → K) = Fintype.card X := by simp
  omega

omit [FiniteDimensional K M] in
/-- Representative changes within D do not change even the linear map. -/
theorem relationMap_change_lifts (T D : Submodule K M) (q : X → M ⧸ T)
    (lift lift' : X → M) (h : ∀ x, lift x - lift' x ∈ D) :
    relationMap T D lift q = relationMap T D lift' q := by
  have hpoint : ∀ x, D.mkQ (lift x) = D.mkQ (lift' x) := by
    intro x
    have hz := (Submodule.Quotient.mk_eq_zero D).2 (h x)
    change D.mkQ (lift x - lift' x) = 0 at hz
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  ext a
  change D.mkQ (coefficientSum lift a.1) = D.mkQ (coefficientSum lift' a.1)
  simp [coefficientSum, hpoint]

#check coefficientSum_range
#check coefficientSum_projection
#check relationMap_exact
#check relationMap_finrank
#check relationKernel_finrank_add_span
#check relationMap_change_lifts
#print axioms coefficientSum_range
#print axioms coefficientSum_projection
#print axioms relationMap_exact
#print axioms relationMap_finrank
#print axioms relationKernel_finrank_add_span
#print axioms relationMap_change_lifts
end
end UnrestrictedBooleanMul.Capacity
