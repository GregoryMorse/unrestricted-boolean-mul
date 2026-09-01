import UnrestrictedBooleanMul.N5.FanoRelations

/-!
# Incidence of sparse defect relations

This module specializes the sparse Fano presentation to populated quotient
points and effective closed places.  Keeping these lemmas downstream avoids
introducing broad polymorphic rewriting into the core relation module.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem quotient_add_self (q : QuadraticQuotient) : q + q = 0 := by
  have hone : (1 + 1 : F₂) = 0 := by
    change (2 : F₂) = 0
    exact N3Certificate.two_eq_zero_f2
  calc
    q + q = (1 + 1 : F₂) • q := by simp [add_smul]
    _ = 0 := by rw [hone, zero_smul]

private theorem quotient_add_eq_zero_iff_eq (q r : QuadraticQuotient) :
    q + r = 0 ↔ q = r := by
  constructor
  · intro h
    calc
      q = q + 0 := (add_zero _).symm
      _ = q + (r + r) := by rw [quotient_add_self]
      _ = (q + r) + r := (add_assoc _ _ _).symm
      _ = r := by rw [h, zero_add]
  · rintro rfl
    exact quotient_add_self q

/-- The third point on a populated Fano line is the sum of either two. -/
theorem fanoLine_exists_third
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (x y : PopulatedPoint Q)
    (hx : x ∈ r.support) (hy : y ∈ r.support) (hxy : x ≠ y) :
    ∃ z : PopulatedPoint Q,
      z ∈ r.support ∧ z ≠ x ∧ z ≠ y ∧
      populatedQuotientPoint z =
        populatedQuotientPoint x + populatedQuotientPoint y := by
  classical
  have hyErase : y ∈ r.support.erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hcardEraseX : (r.support.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx, r.card_support]
  have hcardRest : ((r.support.erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem hyErase, hcardEraseX]
  rcases Finset.card_eq_one.mp hcardRest with ⟨z, hzRest⟩
  have hzDoubleErase : z ∈ (r.support.erase x).erase y := by
    rw [hzRest]
    simp
  have hzC : z ∈ r.support :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hzDoubleErase).2).2
  have hzx : z ≠ x :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hzDoubleErase).2).1
  have hzy : z ≠ y := (Finset.mem_erase.mp hzDoubleErase).1
  have hsupport : r.support = {x, y, z} := by
    ext w
    constructor
    · intro hw
      by_cases hwx : w = x
      · simp [hwx]
      by_cases hwy : w = y
      · simp [hwy]
      have hwRest : w ∈ (r.support.erase x).erase y := by
        simp [hw, hwx, hwy]
      rw [hzRest] at hwRest
      simp at hwRest
      simp [hwRest]
    · intro hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hzC
  have hsum : populatedQuotientPoint x +
      (populatedQuotientPoint y + populatedQuotientPoint z) = 0 := by
    have h := r.sum_eq_zero
    rw [hsupport] at h
    have hxNot : x ∉ ({y, z} : Finset (PopulatedPoint Q)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, fun hxz => hzx hxz.symm⟩
    have hyNot : y ∉ ({z} : Finset (PopulatedPoint Q)) := by
      simp only [Finset.mem_singleton]
      exact fun hyz => hzy hyz.symm
    rw [Finset.sum_insert hxNot, Finset.sum_insert hyNot,
      Finset.sum_singleton] at h
    exact h
  refine ⟨z, hzC, hzx, hzy, ?_⟩
  apply (quotient_add_eq_zero_iff_eq
    (populatedQuotientPoint z)
    (populatedQuotientPoint x + populatedQuotientPoint y)).1
  have hreorder : populatedQuotientPoint z +
      (populatedQuotientPoint x + populatedQuotientPoint y) =
      populatedQuotientPoint x +
        (populatedQuotientPoint y + populatedQuotientPoint z) := by
    ac_rfl
  rw [hreorder]
  exact hsum

/-- A populated Fano line cannot contain effective points of two distinct
closed-place types. -/
theorem fanoLine_effective_places_eq
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (u v : PopulatedPoint Q) (hu : u ∈ r.support)
    (hv : v ∈ r.support) (huv : u ≠ v)
    (x y : ClosedPlaceEffectiveParam)
    (hux : populatedQuotientPoint u = closedPlaceEffectivePoint x)
    (hvy : populatedQuotientPoint v = closedPlaceEffectivePoint y) :
    x.1 = y.1 := by
  by_contra hplace
  rcases fanoLine_exists_third Q r u v hu hv huv with
    ⟨z, _hz, _hzu, _hzv, hzsum⟩
  apply no_populatedPoint_eq_sum_of_distinct_effective_places
    Q x y hplace z
  rw [← hux, ← hvy]
  exact hzsum

/-- The two complementary pairs in a populated Fano quadrilateral have the
same quotient sum. -/
theorem fanoQuadrilateral_exists_complementary_pair
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoQuadrilateralRelation
      (populatedQuotientPoint (Q := Q)))
    (x y : PopulatedPoint Q)
    (hx : x ∈ r.support) (hy : y ∈ r.support) (hxy : x ≠ y) :
    ∃ z w : PopulatedPoint Q,
      z ∈ r.support ∧ w ∈ r.support ∧
      z ≠ w ∧ z ≠ x ∧ z ≠ y ∧
      w ≠ x ∧ w ≠ y ∧
      populatedQuotientPoint z + populatedQuotientPoint w =
        populatedQuotientPoint x + populatedQuotientPoint y := by
  classical
  have hyErase : y ∈ r.support.erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hcardEraseX : (r.support.erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hx, r.card_support]
  have hcardRest : ((r.support.erase x).erase y).card = 2 := by
    rw [Finset.card_erase_of_mem hyErase, hcardEraseX]
  rcases Finset.card_eq_two.mp hcardRest with ⟨z, w, hzw, hRest⟩
  have hzRest : z ∈ (r.support.erase x).erase y := by
    rw [hRest]
    simp
  have hwRest : w ∈ (r.support.erase x).erase y := by
    rw [hRest]
    simp
  have hzC : z ∈ r.support :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hzRest).2).2
  have hwC : w ∈ r.support :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hwRest).2).2
  have hzx : z ≠ x :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hzRest).2).1
  have hzy : z ≠ y := (Finset.mem_erase.mp hzRest).1
  have hwx : w ≠ x :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hwRest).2).1
  have hwy : w ≠ y := (Finset.mem_erase.mp hwRest).1
  have hsupport : r.support = {x, y, z, w} := by
    ext t
    constructor
    · intro ht
      by_cases htx : t = x
      · simp [htx]
      by_cases hty : t = y
      · simp [hty]
      have htRest : t ∈ (r.support.erase x).erase y := by
        simp [ht, htx, hty]
      rw [hRest] at htRest
      simp only [Finset.mem_insert, Finset.mem_singleton] at htRest
      rcases htRest with rfl | rfl <;> simp
    · intro ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hzC
      · exact hwC
  have hsum : populatedQuotientPoint x +
      (populatedQuotientPoint y +
        (populatedQuotientPoint z + populatedQuotientPoint w)) = 0 := by
    have h := r.sum_eq_zero
    rw [hsupport] at h
    have hxNot : x ∉ ({y, z, w} : Finset (PopulatedPoint Q)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, fun hxz => hzx hxz.symm,
        fun hxw => hwx hxw.symm⟩
    have hyNot : y ∉ ({z, w} : Finset (PopulatedPoint Q)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun hyz => hzy hyz.symm, fun hyw => hwy hyw.symm⟩
    have hzNot : z ∉ ({w} : Finset (PopulatedPoint Q)) := by
      simp only [Finset.mem_singleton]
      exact hzw
    rw [Finset.sum_insert hxNot, Finset.sum_insert hyNot,
      Finset.sum_insert hzNot, Finset.sum_singleton] at h
    exact h
  refine ⟨z, w, hzC, hwC, hzw, hzx, hzy, hwx, hwy, ?_⟩
  apply (quotient_add_eq_zero_iff_eq
    (populatedQuotientPoint z + populatedQuotientPoint w)
    (populatedQuotientPoint x + populatedQuotientPoint y)).1
  have hreorder :
      (populatedQuotientPoint z + populatedQuotientPoint w) +
        (populatedQuotientPoint x + populatedQuotientPoint y) =
      populatedQuotientPoint x +
        (populatedQuotientPoint y +
          (populatedQuotientPoint z + populatedQuotientPoint w)) := by
    ac_rfl
  rw [hreorder]
  exact hsum

/-- If one pair of a Fano quadrilateral consists of effective points of
distinct place types, then the common complementary-pair sum has an empty
decomposable fiber. -/
theorem fanoQuadrilateral_mixed_complement_sum_not_populated
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoQuadrilateralRelation
      (populatedQuotientPoint (Q := Q)))
    (u v : PopulatedPoint Q) (hu : u ∈ r.support)
    (hv : v ∈ r.support) (huv : u ≠ v)
    (x y : ClosedPlaceEffectiveParam)
    (hux : populatedQuotientPoint u = closedPlaceEffectivePoint x)
    (hvy : populatedQuotientPoint v = closedPlaceEffectivePoint y)
    (hplace : x.1 ≠ y.1) :
    ∃ z w : PopulatedPoint Q,
      z ∈ r.support ∧ w ∈ r.support ∧ z ≠ w ∧
      populatedQuotientPoint z + populatedQuotientPoint w =
        populatedQuotientPoint u + populatedQuotientPoint v ∧
      ¬ IsPopulatedFiber
        (populatedQuotientPoint z + populatedQuotientPoint w) := by
  rcases fanoQuadrilateral_exists_complementary_pair Q r u v hu hv huv with
    ⟨z, w, hz, hw, hzw, _hzu, _hzv, _hwu, _hwv, hsum⟩
  refine ⟨z, w, hz, hw, hzw, hsum, ?_⟩
  rw [hsum, hux, hvy]
  exact not_populated_sum_of_distinct_effective_places x y hplace

end

end N5
end UnrestrictedBooleanMul
