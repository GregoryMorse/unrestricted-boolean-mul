import UnrestrictedBooleanMul.N5.RelationGiftPivots

/-!
# Closed-place labels of effective populated points

The 43-point atlas classifies effective quotient fibers, but sparse incidence
arguments are indexed by `PopulatedPoint Q`.  This module supplies the unique
bridge between those two presentations and packages mixed-place exclusion as
linear independence of any three effective points of pairwise distinct place
types.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Effective members of the populated quotient-point family of `Q`. -/
abbrev EffectivePopulatedPoint
    (Q : Submodule F₂ QuadraticQuotient) :=
  {x : PopulatedPoint Q //
    IsEffectiveFiber (populatedQuotientPoint x)}

/-- Every effective populated point has a closed-place atlas label. -/
theorem exists_closedPlaceEffectiveParam
    (Q : Submodule F₂ QuadraticQuotient)
    (x : EffectivePopulatedPoint Q) :
    ∃ p : ClosedPlaceEffectiveParam,
      populatedQuotientPoint x.1 = closedPlaceEffectivePoint p := by
  classical
  have hmem := effectiveFiber_mem_atlas x.2
  rw [effectiveFiberAtlas, Finset.mem_image] at hmem
  rcases hmem with ⟨p, _hp, hp⟩
  exact ⟨p, hp.symm⟩

/-- The unique atlas label of an effective populated point. -/
def effectiveClosedPlaceParam
    (Q : Submodule F₂ QuadraticQuotient)
    (x : EffectivePopulatedPoint Q) : ClosedPlaceEffectiveParam :=
  Classical.choose (exists_closedPlaceEffectiveParam Q x)

@[simp] theorem populatedQuotientPoint_effectiveClosedPlaceParam
    (Q : Submodule F₂ QuadraticQuotient)
    (x : EffectivePopulatedPoint Q) :
    populatedQuotientPoint x.1 =
      closedPlaceEffectivePoint (effectiveClosedPlaceParam Q x) :=
  Classical.choose_spec (exists_closedPlaceEffectiveParam Q x)

/-- Atlas labels are unique, including their closed-place type. -/
theorem effectiveClosedPlaceParam_unique
    (Q : Submodule F₂ QuadraticQuotient)
    (x : EffectivePopulatedPoint Q)
    (p : ClosedPlaceEffectiveParam)
    (hp : populatedQuotientPoint x.1 = closedPlaceEffectivePoint p) :
    effectiveClosedPlaceParam Q x = p := by
  apply closedPlaceEffectivePoint_injective
  rw [← hp]
  exact (populatedQuotientPoint_effectiveClosedPlaceParam Q x).symm

/-- Closed-place type of an effective populated point. -/
def effectivePlace
    (Q : Submodule F₂ QuadraticQuotient)
    (x : EffectivePopulatedPoint Q) : Fin 4 :=
  (effectiveClosedPlaceParam Q x).1

/-- An effective point certifies that its closed place is represented in
`Q`. -/
theorem effectivePlace_isRepresented
    (Q : Submodule F₂ QuadraticQuotient)
    (x : EffectivePopulatedPoint Q) :
    IsRepresentedPlace Q (effectivePlace Q x) := by
  change IsRepresentedPlace Q (effectiveClosedPlaceParam Q x).1
  refine ⟨(effectiveClosedPlaceParam Q x).2, ?_⟩
  change closedPlaceEffectivePoint (effectiveClosedPlaceParam Q x) ∈ Q
  rw [← populatedQuotientPoint_effectiveClosedPlaceParam Q x]
  exact x.1.1.2

/-- Distinct closed-place atlas labels give distinct populated points. -/
theorem populatedPoint_ne_of_closedPlace_ne
    (Q : Submodule F₂ QuadraticQuotient)
    (x y : PopulatedPoint Q)
    (p q : ClosedPlaceEffectiveParam)
    (hxp : populatedQuotientPoint x = closedPlaceEffectivePoint p)
    (hyq : populatedQuotientPoint y = closedPlaceEffectivePoint q)
    (hpq : p.1 ≠ q.1) : x ≠ y := by
  intro hxy
  apply hpq
  apply congrArg Sigma.fst
  apply closedPlaceEffectivePoint_injective
  rw [← hxp, ← hyq, hxy]

/-- Three effective populated points of pairwise distinct closed-place types
are linearly independent in the defect space.  A three-term dependence would
be a populated Fano line mixing place types, forbidden by strong mixed-place
exclusion. -/
theorem three_distinct_effective_places_linearIndependent
    (Q : Submodule F₂ QuadraticQuotient)
    (x₀ x₁ x₂ : PopulatedPoint Q)
    (p₀ p₁ p₂ : ClosedPlaceEffectiveParam)
    (hx₀ : populatedQuotientPoint x₀ = closedPlaceEffectivePoint p₀)
    (hx₁ : populatedQuotientPoint x₁ = closedPlaceEffectivePoint p₁)
    (hx₂ : populatedQuotientPoint x₂ = closedPlaceEffectivePoint p₂)
    (hp₀₁ : p₀.1 ≠ p₁.1) (hp₀₂ : p₀.1 ≠ p₂.1)
    (hp₁₂ : p₁.1 ≠ p₂.1) :
    LinearIndependent F₂
      (![x₀.1, x₁.1, x₂.1] : Fin 3 → Q) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hsumQ : ∑ j : Fin 3,
      g j • populatedQuotientPoint (![x₀, x₁, x₂] j) = 0 := by
    exact congrArg Subtype.val hsum
  rcases f2_eq_zero_or_one (g 0) with hg₀ | hg₀ <;>
    rcases f2_eq_zero_or_one (g 1) with hg₁ | hg₁ <;>
      rcases f2_eq_zero_or_one (g 2) with hg₂ | hg₂
  · fin_cases i <;> assumption
  · have hz : populatedQuotientPoint x₂ = 0 := by
      simpa [Fin.sum_univ_succ, hg₀, hg₁, hg₂] using hsumQ
    exact (x₂.2.1 hz).elim
  · have hz : populatedQuotientPoint x₁ = 0 := by
      simpa [Fin.sum_univ_succ, hg₀, hg₁, hg₂] using hsumQ
    exact (x₁.2.1 hz).elim
  · have heq : populatedQuotientPoint x₁ =
        populatedQuotientPoint x₂ := by
      apply sub_eq_zero.mp
      rw [ZModModule.sub_eq_add]
      simpa [Fin.sum_univ_succ, hg₀, hg₁, hg₂] using hsumQ
    exfalso
    apply (populatedPoint_ne_of_closedPlace_ne Q x₁ x₂ p₁ p₂
      hx₁ hx₂ hp₁₂)
    exact populatedQuotientPoint_injective Q heq
  · have hz : populatedQuotientPoint x₀ = 0 := by
      simpa [Fin.sum_univ_succ, hg₀, hg₁, hg₂] using hsumQ
    exact (x₀.2.1 hz).elim
  · have heq : populatedQuotientPoint x₀ =
        populatedQuotientPoint x₂ := by
      apply sub_eq_zero.mp
      rw [ZModModule.sub_eq_add]
      simpa [Fin.sum_univ_succ, hg₀, hg₁, hg₂] using hsumQ
    exfalso
    apply (populatedPoint_ne_of_closedPlace_ne Q x₀ x₂ p₀ p₂
      hx₀ hx₂ hp₀₂)
    exact populatedQuotientPoint_injective Q heq
  · have heq : populatedQuotientPoint x₀ =
        populatedQuotientPoint x₁ := by
      apply sub_eq_zero.mp
      rw [ZModModule.sub_eq_add]
      simpa [Fin.sum_univ_succ, hg₀, hg₁, hg₂] using hsumQ
    exfalso
    apply (populatedPoint_ne_of_closedPlace_ne Q x₀ x₁ p₀ p₁
      hx₀ hx₁ hp₀₁)
    exact populatedQuotientPoint_injective Q heq
  · have hline : populatedQuotientPoint x₀ +
        populatedQuotientPoint x₁ + populatedQuotientPoint x₂ = 0 := by
      simpa [Fin.sum_univ_succ, hg₀, hg₁, hg₂,
        add_assoc] using hsumQ
    have hx₀₁ := populatedPoint_ne_of_closedPlace_ne Q x₀ x₁ p₀ p₁
      hx₀ hx₁ hp₀₁
    have hx₀₂ := populatedPoint_ne_of_closedPlace_ne Q x₀ x₂ p₀ p₂
      hx₀ hx₂ hp₀₂
    have hx₁₂ := populatedPoint_ne_of_closedPlace_ne Q x₁ x₂ p₁ p₂
      hx₁ hx₂ hp₁₂
    let r := fanoLineRelationOf
      (populatedQuotientPoint (Q := Q)) x₀ x₁ x₂
        hx₀₁ hx₀₂ hx₁₂ hline
    have hplace : p₀.1 = p₁.1 :=
      fanoLine_effective_places_eq Q r x₀ x₁ (by
        simp [r, fanoLineRelationOf]) (by
        simp [r, fanoLineRelationOf]) hx₀₁ p₀ p₁ hx₀ hx₁
    exact (hp₀₁ hplace).elim

end

end N5
end UnrestrictedBooleanMul
