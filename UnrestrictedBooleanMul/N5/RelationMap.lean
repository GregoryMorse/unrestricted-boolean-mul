import UnrestrictedBooleanMul.N5.Fiber

/-!
# The exact relation map

This module formalizes the linear-algebra mechanism of manuscript Theorem
3.2.  It is independent of the later closed-place classification: a finite
family of quotient points, chosen lifts, and a displacement subspace determine
the relation map.  The primary theorem is a submodule identity; the finrank
formula is a corollary of rank-nullity.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Linear combination of a finite family, with coefficients represented as
a function on its finite index type. -/
def coefficientSum {X V : Type*} [Fintype X] [AddCommGroup V] [Module F₂ V]
    (v : X → V) : (X → F₂) →ₗ[F₂] V where
  toFun a := ∑ x : X, a x • v x
  map_add' a b := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [Finset.smul_sum, smul_smul]

/-- The image of `coefficientSum` is exactly the span of the family. -/
theorem coefficientSum_range {X V : Type*} [Fintype X]
    [AddCommGroup V] [Module F₂ V] (v : X → V) :
    LinearMap.range (coefficientSum v) = Submodule.span F₂ (Set.range v) := by
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    apply Submodule.sum_mem
    intro x _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨x, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    refine ⟨(Pi.basisFun F₂ X) x, ?_⟩
    classical
    simp [coefficientSum, Pi.basisFun, Pi.single_apply]

/-- Additive relations among a finite family of quotient points. -/
def relationKernel {X : Type*} [Fintype X] (q : X → QuadraticQuotient) :
    Submodule F₂ (X → F₂) :=
  LinearMap.ker (coefficientSum q)

/-- Relation gifts supplied by chosen lifts, modulo the displacement space. -/
def relationMap {X : Type*} [Fintype X] (D : Submodule F₂ TwoForm)
    (lift : X → TwoForm) (q : X → QuadraticQuotient) :
    relationKernel q →ₗ[F₂] (TwoForm ⧸ D) :=
  (Submodule.mkQ D).comp ((coefficientSum lift).domRestrict (relationKernel q))

theorem coefficientSum_projection {X : Type*} [Fintype X]
    (lift : X → TwoForm) (q : X → QuadraticQuotient)
    (hq : ∀ x, quadraticQuotientProjection (lift x) = q x)
    (a : X → F₂) :
    quadraticQuotientProjection (coefficientSum lift a) =
      coefficientSum q a := by
  simp [coefficientSum, hq]

/-- Manuscript Theorem 3.2, exact form:
`(T ∩ W)/D` is the image of the relation map.  Both sides are represented
inside the common ambient quotient `TwoForm ⧸ D`. -/
theorem relationMap_exact {X : Type*} [Fintype X]
    (D W : Submodule F₂ TwoForm)
    (lift : X → TwoForm) (q : X → QuadraticQuotient)
    (hD : D ≤ targetTwoSpace)
    (hq : ∀ x, quadraticQuotientProjection (lift x) = q x)
    (hW : W = D ⊔ Submodule.span F₂ (Set.range lift)) :
    Submodule.map (Submodule.mkQ D) (targetTwoSpace ⊓ W) =
      LinearMap.range (relationMap D lift q) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htW : t ∈ D ⊔ Submodule.span F₂ (Set.range lift) := by
      rw [← hW]
      exact ht.2
    rcases Submodule.mem_sup.mp htW with ⟨d, hd, s, hs, rfl⟩
    rw [← coefficientSum_range] at hs
    rcases hs with ⟨a, rfl⟩
    have hsT : coefficientSum lift a ∈ targetTwoSpace := by
      have hsumT : d + coefficientSum lift a ∈ targetTwoSpace := ht.1
      have hdT : d ∈ targetTwoSpace := hD hd
      have := targetTwoSpace.sub_mem hsumT hdT
      simpa using this
    have ha0 : coefficientSum q a = 0 := by
      rw [← coefficientSum_projection lift q hq a]
      exact (quadraticQuotientProjection_eq_zero_iff _).2 hsT
    have ha : a ∈ relationKernel q := by
      exact (LinearMap.mem_ker).2 ha0
    refine ⟨⟨a, ha⟩, ?_⟩
    change (Submodule.mkQ D) (coefficientSum lift a) =
      (Submodule.mkQ D) (d + coefficientSum lift a)
    rw [map_add]
    have hd0 : (Submodule.mkQ D) d = (0 : TwoForm ⧸ D) := by
      change Submodule.Quotient.mk d = 0
      exact (Submodule.Quotient.mk_eq_zero D).2 hd
    rw [hd0, zero_add]
  · rintro ⟨a, rfl⟩
    let s : TwoForm := coefficientSum lift a.1
    have hqsum : coefficientSum q a.1 = 0 :=
      (LinearMap.mem_ker).1 a.2
    have hsT : s ∈ targetTwoSpace := by
      apply (quadraticQuotientProjection_eq_zero_iff s).1
      rw [coefficientSum_projection lift q hq]
      exact hqsum
    have hsSpan : s ∈ Submodule.span F₂ (Set.range lift) := by
      rw [← coefficientSum_range]
      exact ⟨a.1, rfl⟩
    have hsW : s ∈ W := by
      rw [hW]
      exact Submodule.mem_sup_right hsSpan
    refine ⟨s, ⟨hsT, hsW⟩, ?_⟩
    rfl

/-- Finrank form of the exact relation-map theorem. -/
theorem relationMap_finrank {X : Type*} [Fintype X]
    (D W : Submodule F₂ TwoForm)
    (lift : X → TwoForm) (q : X → QuadraticQuotient)
    (hD : D ≤ targetTwoSpace)
    (hq : ∀ x, quadraticQuotientProjection (lift x) = q x)
    (hW : W = D ⊔ Submodule.span F₂ (Set.range lift)) :
    Module.finrank F₂ ↑(targetTwoSpace ⊓ W) =
      Module.finrank F₂ D +
        Module.finrank F₂ (LinearMap.range (relationMap D lift q)) := by
  let I : Submodule F₂ TwoForm := targetTwoSpace ⊓ W
  let f : I →ₗ[F₂] (TwoForm ⧸ D) := (Submodule.mkQ D).domRestrict I
  have hDI : D ≤ I := by
    intro d hd
    refine ⟨hD hd, ?_⟩
    rw [hW]
    exact Submodule.mem_sup_left hd
  have hker : LinearMap.ker f = D.comap I.subtype := by
    ext x
    simp [f, Submodule.Quotient.mk_eq_zero]
  have hkerRank : Module.finrank F₂ (LinearMap.ker f) =
      Module.finrank F₂ D := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hDI).finrank_eq
  have hrange : LinearMap.range f =
      LinearMap.range (relationMap D lift q) := by
    rw [← relationMap_exact D W lift q hD hq hW]
    simp [f, I]
  have hrank := f.finrank_range_add_finrank_ker
  rw [hkerRank, hrange] at hrank
  change Module.finrank F₂ I = _
  omega

end

end N5
end UnrestrictedBooleanMul
