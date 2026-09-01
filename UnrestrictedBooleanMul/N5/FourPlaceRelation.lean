import UnrestrictedBooleanMul.N5.EffectivePointPlaces

/-!
# The exceptional four-place quadrilateral

If a defect space of dimension at most three represents all four closed-place
types, choose one effective point of each type.  Any three are independent by
mixed-place exclusion, while all four lie in a three-dimensional space.  Their
unique dependence therefore uses every point and is a populated Fano
quadrilateral.  This is the sole incidence configuration left for the local
Klein-syzygy obstruction.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- A chosen effective atlas parameter witnessing a represented place. -/
def representedClosedPlaceParam
    (Q : Submodule F₂ QuadraticQuotient) (place : Fin 4)
    (hplace : IsRepresentedPlace Q place) : ClosedPlaceEffectiveParam :=
  ⟨place, Classical.choose hplace⟩

@[simp] theorem representedClosedPlaceParam_place
    (Q : Submodule F₂ QuadraticQuotient) (place : Fin 4)
    (hplace : IsRepresentedPlace Q place) :
    (representedClosedPlaceParam Q place hplace).1 = place := rfl

theorem representedClosedPlaceParam_mem
    (Q : Submodule F₂ QuadraticQuotient) (place : Fin 4)
    (hplace : IsRepresentedPlace Q place) :
    closedPlaceEffectivePoint
      (representedClosedPlaceParam Q place hplace) ∈ Q :=
  Classical.choose_spec hplace

/-- A chosen populated point witnessing a represented place. -/
def representedPopulatedPoint
    (Q : Submodule F₂ QuadraticQuotient) (place : Fin 4)
    (hplace : IsRepresentedPlace Q place) : PopulatedPoint Q :=
  closedPlacePopulatedPoint Q
    (representedClosedPlaceParam Q place hplace)
    (representedClosedPlaceParam_mem Q place hplace)

@[simp] theorem representedPopulatedPoint_quotient
    (Q : Submodule F₂ QuadraticQuotient) (place : Fin 4)
    (hplace : IsRepresentedPlace Q place) :
    populatedQuotientPoint
        (representedPopulatedPoint Q place hplace) =
      closedPlaceEffectivePoint
        (representedClosedPlaceParam Q place hplace) := rfl

/-- Chosen witnesses for different place types are distinct populated points. -/
theorem representedPopulatedPoint_ne
    (Q : Submodule F₂ QuadraticQuotient) (i j : Fin 4)
    (hi : IsRepresentedPlace Q i) (hj : IsRepresentedPlace Q j)
    (hij : i ≠ j) :
    representedPopulatedPoint Q i hi ≠
      representedPopulatedPoint Q j hj := by
  apply populatedPoint_ne_of_closedPlace_ne Q
    (representedPopulatedPoint Q i hi)
    (representedPopulatedPoint Q j hj)
    (representedClosedPlaceParam Q i hi)
    (representedClosedPlaceParam Q j hj)
    (representedPopulatedPoint_quotient Q i hi)
    (representedPopulatedPoint_quotient Q j hj)
  simpa using hij

/-- Three chosen witnesses at distinct place indices are independent. -/
theorem representedTriple_linearIndependent
    (Q : Submodule F₂ QuadraticQuotient)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i) (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent F₂
      (![ (representedPopulatedPoint Q i hi).1,
          (representedPopulatedPoint Q j hj).1,
          (representedPopulatedPoint Q k hk).1 ] : Fin 3 → Q) := by
  apply three_distinct_effective_places_linearIndependent Q
    (representedPopulatedPoint Q i hi)
    (representedPopulatedPoint Q j hj)
    (representedPopulatedPoint Q k hk)
    (representedClosedPlaceParam Q i hi)
    (representedClosedPlaceParam Q j hj)
    (representedClosedPlaceParam Q k hk)
    (representedPopulatedPoint_quotient Q i hi)
    (representedPopulatedPoint_quotient Q j hj)
    (representedPopulatedPoint_quotient Q k hk)
  · simpa using hij
  · simpa using hik
  · simpa using hjk

/-- If all four place types are represented in a defect space of dimension at
most three, the four chosen quotient points sum to zero. -/
theorem four_represented_place_points_sum_eq_zero
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hplace : ∀ i : Fin 4, IsRepresentedPlace Q i) :
    ∑ i : Fin 4,
      populatedQuotientPoint
        (representedPopulatedPoint Q i (hplace i)) = 0 := by
  let x : Fin 4 → PopulatedPoint Q :=
    fun i ↦ representedPopulatedPoint Q i (hplace i)
  let v : Fin 4 → Q := fun i ↦ (x i).1
  have hnot : ¬ LinearIndependent F₂ v := by
    intro hlin
    have hcard := hlin.fintype_card_le_finrank
    have : 4 ≤ Module.finrank F₂ Q := by simpa using hcard
    omega
  rcases Fintype.not_linearIndependent_iff.mp hnot with
    ⟨g, hsum, iNonzero, hiNonzero⟩
  have hg₀ : g 0 ≠ 0 := by
    intro hg
    have hlin := representedTriple_linearIndependent Q 1 2 3
      (hplace 1) (hplace 2) (hplace 3)
      (by decide) (by decide) (by decide)
    have hrest : ∑ j : Fin 3, (![g 1, g 2, g 3] j) •
        (![v 1, v 2, v 3] j) = 0 := by
      simpa [Fin.sum_univ_succ, hg, v, x] using hsum
    have hz := Fintype.linearIndependent_iff.mp hlin _ hrest
    have hz₁ : g 1 = 0 := by simpa using hz 0
    have hz₂ : g 2 = 0 := by simpa using hz 1
    have hz₃ : g 3 = 0 := by simpa using hz 2
    fin_cases iNonzero <;> simp_all
  have hg₁ : g 1 ≠ 0 := by
    intro hg
    have hlin := representedTriple_linearIndependent Q 0 2 3
      (hplace 0) (hplace 2) (hplace 3)
      (by decide) (by decide) (by decide)
    have hrest : ∑ j : Fin 3, (![g 0, g 2, g 3] j) •
        (![v 0, v 2, v 3] j) = 0 := by
      simpa [Fin.sum_univ_succ, hg, v, x, add_assoc] using hsum
    have hz := Fintype.linearIndependent_iff.mp hlin _ hrest
    have hz₀ : g 0 = 0 := by simpa using hz 0
    have hz₂ : g 2 = 0 := by simpa using hz 1
    have hz₃ : g 3 = 0 := by simpa using hz 2
    fin_cases iNonzero <;> simp_all
  have hg₂ : g 2 ≠ 0 := by
    intro hg
    have hlin := representedTriple_linearIndependent Q 0 1 3
      (hplace 0) (hplace 1) (hplace 3)
      (by decide) (by decide) (by decide)
    have hrest : ∑ j : Fin 3, (![g 0, g 1, g 3] j) •
        (![v 0, v 1, v 3] j) = 0 := by
      simpa [Fin.sum_univ_succ, hg, v, x, add_assoc] using hsum
    have hz := Fintype.linearIndependent_iff.mp hlin _ hrest
    have hz₀ : g 0 = 0 := by simpa using hz 0
    have hz₁ : g 1 = 0 := by simpa using hz 1
    have hz₃ : g 3 = 0 := by simpa using hz 2
    fin_cases iNonzero <;> simp_all
  have hg₃ : g 3 ≠ 0 := by
    intro hg
    have hlin := representedTriple_linearIndependent Q 0 1 2
      (hplace 0) (hplace 1) (hplace 2)
      (by decide) (by decide) (by decide)
    have hrest : ∑ j : Fin 3, (![g 0, g 1, g 2] j) •
        (![v 0, v 1, v 2] j) = 0 := by
      simpa [Fin.sum_univ_succ, hg, v, x, add_assoc] using hsum
    have hz := Fintype.linearIndependent_iff.mp hlin _ hrest
    have hz₀ : g 0 = 0 := by simpa using hz 0
    have hz₁ : g 1 = 0 := by simpa using hz 1
    have hz₂ : g 2 = 0 := by simpa using hz 2
    fin_cases iNonzero <;> simp_all
  have hg₀one : g 0 = 1 := (f2_eq_zero_or_one (g 0)).resolve_left hg₀
  have hg₁one : g 1 = 1 := (f2_eq_zero_or_one (g 1)).resolve_left hg₁
  have hg₂one : g 2 = 1 := (f2_eq_zero_or_one (g 2)).resolve_left hg₂
  have hg₃one : g 3 = 1 := (f2_eq_zero_or_one (g 3)).resolve_left hg₃
  have hsumQ := congrArg Subtype.val hsum
  change (∑ i : Fin 4, g i • populatedQuotientPoint (x i)) = 0 at hsumQ
  simpa [Fin.sum_univ_succ, hg₀one, hg₁one, hg₂one,
    hg₃one, v, x, add_assoc] using hsumQ

/-- The chosen witnesses of all four represented places form the exceptional
populated Fano quadrilateral. -/
noncomputable def fourPlaceFanoQuadrilateral
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hplace : ∀ i : Fin 4, IsRepresentedPlace Q i) :
    FanoQuadrilateralRelation
      (populatedQuotientPoint (Q := Q)) :=
  fanoQuadrilateralRelationOf
    (populatedQuotientPoint (Q := Q))
    (representedPopulatedPoint Q 0 (hplace 0))
    (representedPopulatedPoint Q 1 (hplace 1))
    (representedPopulatedPoint Q 2 (hplace 2))
    (representedPopulatedPoint Q 3 (hplace 3))
    (representedPopulatedPoint_ne Q 0 1 (hplace 0) (hplace 1) (by decide))
    (representedPopulatedPoint_ne Q 0 2 (hplace 0) (hplace 2) (by decide))
    (representedPopulatedPoint_ne Q 0 3 (hplace 0) (hplace 3) (by decide))
    (representedPopulatedPoint_ne Q 1 2 (hplace 1) (hplace 2) (by decide))
    (representedPopulatedPoint_ne Q 1 3 (hplace 1) (hplace 3) (by decide))
    (representedPopulatedPoint_ne Q 2 3 (hplace 2) (hplace 3) (by decide))
    (by simpa [Fin.sum_univ_succ, add_assoc] using
      four_represented_place_points_sum_eq_zero Q hQ hplace)

end

end N5
end UnrestrictedBooleanMul
