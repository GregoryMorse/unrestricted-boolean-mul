import UnrestrictedBooleanMul.N5.SparseAnchorGifts

/-!
# Three distinct represented place types

When three distinct place types are represented in a defect space of
dimension at most three, their chosen effective points form a basis.  Strong
mixed-place exclusion removes all three pair sums from the populated family.
Thus every populated point is one of the three basis points or their total
sum, so the relation kernel and relation-gift image have dimension at most
one.  For the three rational places this already proves the sharp displacement
bound.  For the degree-two place together with two rational places it isolates
the remaining local pivot to the possible quadrilateral gift.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private abbrev representedTripleWitness
    (Q : Submodule F₂ QuadraticQuotient)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k) : Fin 3 → PopulatedPoint Q :=
  ![representedPopulatedPoint Q i hi,
    representedPopulatedPoint Q j hj,
    representedPopulatedPoint Q k hk]

/-- Every populated point in the three-rational-place profile is a basis
point or the sum of all three basis points. -/
theorem populatedPoint_cases_of_three_distinct_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (y : PopulatedPoint Q) :
    y = representedTripleWitness Q i j k hi hj hk 0 ∨
    y = representedTripleWitness Q i j k hi hj hk 1 ∨
    y = representedTripleWitness Q i j k hi hj hk 2 ∨
    populatedQuotientPoint y =
      populatedQuotientPoint (representedTripleWitness Q i j k hi hj hk 0) +
      populatedQuotientPoint (representedTripleWitness Q i j k hi hj hk 1) +
      populatedQuotientPoint (representedTripleWitness Q i j k hi hj hk 2) := by
  let x := representedTripleWitness Q i j k hi hj hk
  let v : Fin 3 → Q := fun i ↦ (x i).1
  have hlin : LinearIndependent F₂ v := by
    rw [show v =
        (![ (representedPopulatedPoint Q i hi).1,
            (representedPopulatedPoint Q j hj).1,
            (representedPopulatedPoint Q k hk).1 ] : Fin 3 → Q) by
      funext i
      fin_cases i <;> rfl]
    exact representedTriple_linearIndependent Q i j k hi hj hk hij hik hjk
  have hrank : Module.finrank F₂ Q = 3 := by
    have hcard := hlin.fintype_card_le_finrank
    have : 3 ≤ Module.finrank F₂ Q := by simpa using hcard
    omega
  have hspan : Submodule.span F₂ (Set.range v) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank' (by simp [hrank])
  have hyspan : y.1 ∈ Submodule.span F₂ (Set.range v) := by
    rw [hspan]
    trivial
  rw [← coefficientSum_range] at hyspan
  rcases hyspan with ⟨a, ha⟩
  rcases f2_eq_zero_or_one (a 0) with ha₀ | ha₀ <;>
    rcases f2_eq_zero_or_one (a 1) with ha₁ | ha₁ <;>
      rcases f2_eq_zero_or_one (a 2) with ha₂ | ha₂
  · have hyzero : populatedQuotientPoint y = 0 := by
      change (y.1 : Q).1 = 0
      have := congrArg Subtype.val ha
      simpa [coefficientSum, Fin.sum_univ_succ, ha₀, ha₁, ha₂,
        v] using this.symm
    exact (y.2.1 hyzero).elim
  · right; right; left
    apply populatedQuotientPoint_injective Q
    change (y.1 : Q).1 = ((x 2).1 : Q).1
    have := congrArg Subtype.val ha
    simpa [coefficientSum, Fin.sum_univ_succ, ha₀, ha₁, ha₂,
      v] using this.symm
  · right; left
    apply populatedQuotientPoint_injective Q
    change (y.1 : Q).1 = ((x 1).1 : Q).1
    have := congrArg Subtype.val ha
    simpa [coefficientSum, Fin.sum_univ_succ, ha₀, ha₁, ha₂,
      v] using this.symm
  · have heq : populatedQuotientPoint y =
        populatedQuotientPoint (x 1) + populatedQuotientPoint (x 2) := by
      change (y.1 : Q).1 = ((x 1).1 : Q).1 + ((x 2).1 : Q).1
      have := congrArg Subtype.val ha
      simpa [coefficientSum, Fin.sum_univ_succ, ha₀, ha₁, ha₂,
        v] using this.symm
    have hpop : IsPopulatedFiber
        (populatedQuotientPoint (x 1) + populatedQuotientPoint (x 2)) := by
      rw [← heq]
      exact y.2.2
    exact (not_populated_sum_of_distinct_effective_places
      (representedClosedPlaceParam Q j hj)
      (representedClosedPlaceParam Q k hk)
      (by simpa using hjk) hpop).elim
  · left
    apply populatedQuotientPoint_injective Q
    change (y.1 : Q).1 = ((x 0).1 : Q).1
    have := congrArg Subtype.val ha
    simpa [coefficientSum, Fin.sum_univ_succ, ha₀, ha₁, ha₂,
      v] using this.symm
  · have heq : populatedQuotientPoint y =
        populatedQuotientPoint (x 0) + populatedQuotientPoint (x 2) := by
      change (y.1 : Q).1 = ((x 0).1 : Q).1 + ((x 2).1 : Q).1
      have := congrArg Subtype.val ha
      simpa [coefficientSum, Fin.sum_univ_succ, ha₀, ha₁, ha₂,
        v] using this.symm
    have hpop : IsPopulatedFiber
        (populatedQuotientPoint (x 0) + populatedQuotientPoint (x 2)) := by
      rw [← heq]
      exact y.2.2
    exact (not_populated_sum_of_distinct_effective_places
      (representedClosedPlaceParam Q i hi)
      (representedClosedPlaceParam Q k hk)
      (by simpa using hik) hpop).elim
  · have heq : populatedQuotientPoint y =
        populatedQuotientPoint (x 0) + populatedQuotientPoint (x 1) := by
      change (y.1 : Q).1 = ((x 0).1 : Q).1 + ((x 1).1 : Q).1
      have := congrArg Subtype.val ha
      simpa [coefficientSum, Fin.sum_univ_succ, ha₀, ha₁, ha₂,
        v] using this.symm
    have hpop : IsPopulatedFiber
        (populatedQuotientPoint (x 0) + populatedQuotientPoint (x 1)) := by
      rw [← heq]
      exact y.2.2
    exact (not_populated_sum_of_distinct_effective_places
      (representedClosedPlaceParam Q i hi)
      (representedClosedPlaceParam Q j hj)
      (by simpa using hij) hpop).elim
  · right; right; right
    change (y.1 : Q).1 =
      ((x 0).1 : Q).1 + ((x 1).1 : Q).1 + ((x 2).1 : Q).1
    have := congrArg Subtype.val ha
    simpa [coefficientSum, Fin.sum_univ_succ, ha₀, ha₁, ha₂,
      v, x, representedTripleWitness, add_assoc] using this.symm

/-- Four-valued coordinate of a populated point in the three-rational
profile. -/
def threePlacePopulatedIndex
    (Q : Submodule F₂ QuadraticQuotient)
    (_hQ : Module.finrank F₂ Q ≤ 3)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (y : PopulatedPoint Q) : Fin 4 := by
  classical
  exact if y = representedTripleWitness Q i j k hi hj hk 0 then 0
    else if y = representedTripleWitness Q i j k hi hj hk 1 then 1
    else if y = representedTripleWitness Q i j k hi hj hk 2 then 2
    else 3

theorem threePlacePopulatedIndex_injective
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (threePlacePopulatedIndex Q hQ i j k hi hj hk) := by
  classical
  intro y z hyz
  let x₀ := representedPopulatedPoint Q i hi
  let x₁ := representedPopulatedPoint Q j hj
  let x₂ := representedPopulatedPoint Q k hk
  let index := threePlacePopulatedIndex Q hQ i j k hi hj hk
  change index y = index z at hyz
  have hx₀₁ : x₀ ≠ x₁ := by
    exact representedPopulatedPoint_ne Q i j hi hj hij
  have hx₀₂ : x₀ ≠ x₂ := by
    exact representedPopulatedPoint_ne Q i k hi hk hik
  have hx₁₂ : x₁ ≠ x₂ := by
    exact representedPopulatedPoint_ne Q j k hj hk hjk
  have hindex₀ (w : PopulatedPoint Q) : index w = 0 ↔ w = x₀ := by
    change (if w = x₀ then 0 else if w = x₁ then 1
      else if w = x₂ then 2 else 3) = 0 ↔ w = x₀
    split_ifs <;> simp_all
  have hindex₁ (w : PopulatedPoint Q) : index w = 1 ↔ w = x₁ := by
    change (if w = x₀ then 0 else if w = x₁ then 1
      else if w = x₂ then 2 else 3) = 1 ↔ w = x₁
    split_ifs <;> simp_all
  have hindex₂ (w : PopulatedPoint Q) : index w = 2 ↔ w = x₂ := by
    change (if w = x₀ then 0 else if w = x₁ then 1
      else if w = x₂ then 2 else 3) = 2 ↔ w = x₂
    split_ifs <;> simp_all
  by_cases hy₀ : index y = 0
  · have hz₀ : index z = 0 := hyz.symm.trans hy₀
    exact ((hindex₀ y).mp hy₀).trans ((hindex₀ z).mp hz₀).symm
  by_cases hy₁ : index y = 1
  · have hz₁ : index z = 1 := hyz.symm.trans hy₁
    exact ((hindex₁ y).mp hy₁).trans ((hindex₁ z).mp hz₁).symm
  by_cases hy₂ : index y = 2
  · have hz₂ : index z = 2 := hyz.symm.trans hy₂
    exact ((hindex₂ y).mp hy₂).trans ((hindex₂ z).mp hz₂).symm
  have hy₃ : index y = 3 := by
    generalize hi : index y = i
    fin_cases i
    · exact (hy₀ hi).elim
    · exact (hy₁ hi).elim
    · exact (hy₂ hi).elim
    · rfl
  have hz₃ : index z = 3 := hyz.symm.trans hy₃
  have hyCases : y = x₀ ∨ y = x₁ ∨ y = x₂ ∨
      populatedQuotientPoint y =
        populatedQuotientPoint x₀ + populatedQuotientPoint x₁ +
          populatedQuotientPoint x₂ := by
    simpa [x₀, x₁, x₂, representedTripleWitness] using
      populatedPoint_cases_of_three_distinct_places Q hQ i j k hi hj hk
        hij hik hjk y
  have hzCases : z = x₀ ∨ z = x₁ ∨ z = x₂ ∨
      populatedQuotientPoint z =
        populatedQuotientPoint x₀ + populatedQuotientPoint x₁ +
          populatedQuotientPoint x₂ := by
    simpa [x₀, x₁, x₂, representedTripleWitness] using
      populatedPoint_cases_of_three_distinct_places Q hQ i j k hi hj hk
        hij hik hjk z
  rcases hyCases with hy | hy | hy | hy
  · exact (hy₀ ((hindex₀ y).mpr hy)).elim
  · exact (hy₁ ((hindex₁ y).mpr hy)).elim
  · exact (hy₂ ((hindex₂ y).mpr hy)).elim
  · rcases hzCases with hz | hz | hz | hz
    · have : index z = 0 := (hindex₀ z).mpr hz
      exact (by omega)
    · have : index z = 1 := (hindex₁ z).mpr hz
      exact (by omega)
    · have : index z = 2 := (hindex₂ z).mpr hz
      exact (by omega)
    · apply populatedQuotientPoint_injective Q
      exact hy.trans hz.symm

/-- At most four nonzero quotient points are populated in the
three-rational-place profile. -/
theorem populatedPoint_card_le_four_of_three_distinct_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Fintype.card (PopulatedPoint Q) ≤ 4 := by
  simpa using Fintype.card_le_of_injective
    (threePlacePopulatedIndex Q hQ i j k hi hj hk)
    (threePlacePopulatedIndex_injective Q hQ i j k hi hj hk hij hik hjk)

/-- The relation kernel has dimension at most one in the all-rational
profile. -/
theorem populatedRelationKernel_finrank_le_one_of_three_distinct_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Module.finrank F₂
      (relationKernel (populatedQuotientPoint (Q := Q))) ≤ 1 := by
  let x := representedTripleWitness Q i j k hi hj hk
  have hlinQ : LinearIndependent F₂ (fun i : Fin 3 ↦ (x i).1) := by
    rw [show (fun i : Fin 3 ↦ (x i).1) =
        (![ (representedPopulatedPoint Q i hi).1,
            (representedPopulatedPoint Q j hj).1,
            (representedPopulatedPoint Q k hk).1 ] : Fin 3 → Q) by
      funext i
      fin_cases i <;> rfl]
    exact representedTriple_linearIndependent Q i j k hi hj hk hij hik hjk
  have hlin : LinearIndependent F₂
      (fun i : Fin 3 ↦ populatedQuotientPoint (x i)) :=
    hlinQ.map' Q.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hsmallSpan : Submodule.span F₂
      (Set.range (fun i : Fin 3 ↦ populatedQuotientPoint (x i))) ≤
      Submodule.span F₂
        (Set.range (populatedQuotientPoint (Q := Q))) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, rfl⟩
  have hspanRank : 3 ≤ Module.finrank F₂
      (Submodule.span F₂
        (Set.range (populatedQuotientPoint (Q := Q)))) := by
    have hrank := Submodule.finrank_mono hsmallSpan
    rw [finrank_span_eq_card hlin] at hrank
    simpa using hrank
  have hkernel := relationKernel_finrank_add_span
    (populatedQuotientPoint (Q := Q))
  have hcard := populatedPoint_card_le_four_of_three_distinct_places
    Q hQ i j k hi hj hk hij hik hjk
  omega

/-- Sharp relation-gift bound in the all-rational profile. -/
theorem relationGiftRank_le_one_of_three_distinct_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    relationGiftRank Q ≤ 1 :=
  (relationGiftRank_le_relationKernel Q).trans
    (populatedRelationKernel_finrank_le_one_of_three_distinct_places
      Q hQ i j k hi hj hk hij hik hjk)

/-- Before the final degree-two quadrilateral pivot, three distinct place
types already give the one-off bound `d + rank(λ) ≤ 5`. -/
theorem displacement_add_gifts_le_five_of_three_distinct_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    displacementRank Q + relationGiftRank Q ≤ 5 := by
  rw [displacementRank_eq_representedPlaceWeight]
  have hweight := representedPlaceWeight_le_four_of_finrank_le_three Q hQ
  have hgift := relationGiftRank_le_one_of_three_distinct_places
    Q hQ i j k hi hj hk hij hik hjk
  omega

/-- Capacity form of the generic three-distinct-place incidence bound. -/
theorem targetCapacity_le_eight_of_three_distinct_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j k : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hk : IsRepresentedPlace Q k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    targetCapacity Q ≤ 8 := by
  rw [targetCapacity_eq_three_add_displacement_add_gifts]
  have hbound := displacement_add_gifts_le_five_of_three_distinct_places
    Q hQ i j k hi hj hk hij hik hjk
  omega

/-- Relation-gift specialization for the three rational place types. -/
theorem relationGiftRank_le_one_of_three_rational_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h₀ : IsRepresentedPlace Q 0)
    (h₁ : IsRepresentedPlace Q 1)
    (h₂ : IsRepresentedPlace Q 2) :
    relationGiftRank Q ≤ 1 :=
  relationGiftRank_le_one_of_three_distinct_places Q hQ 0 1 2 h₀ h₁ h₂
    (by decide) (by decide) (by decide)

/-- With all rational places represented, the degree-two place is excluded,
so the represented-place displacement weight is exactly three. -/
theorem representedPlaceWeight_eq_three_of_three_rational_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h₀ : IsRepresentedPlace Q 0)
    (h₁ : IsRepresentedPlace Q 1)
    (h₂ : IsRepresentedPlace Q 2) :
    representedPlaceWeight Q = 3 := by
  classical
  have h₃ : ¬ IsRepresentedPlace Q 3 := by
    intro h₃
    apply not_all_closedPlaces_represented Q hQ
    intro i
    fin_cases i <;> assumption
  simp [representedPlaceWeight, representedRationalPlaceCount,
    representedDegreeTwoIndicator, h₀, h₁, h₂, h₃]

/-- Sharp displacement-plus-gift bound for the all-rational profile. -/
theorem displacement_add_gifts_le_four_of_three_rational_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h₀ : IsRepresentedPlace Q 0)
    (h₁ : IsRepresentedPlace Q 1)
    (h₂ : IsRepresentedPlace Q 2) :
    displacementRank Q + relationGiftRank Q ≤ 4 := by
  rw [displacementRank_eq_representedPlaceWeight,
    representedPlaceWeight_eq_three_of_three_rational_places Q hQ h₀ h₁ h₂]
  have hgift := relationGiftRank_le_one_of_three_rational_places
    Q hQ h₀ h₁ h₂
  omega

/-- Capacity form of the sharp all-rational profile bound. -/
theorem targetCapacity_le_seven_of_three_rational_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h₀ : IsRepresentedPlace Q 0)
    (h₁ : IsRepresentedPlace Q 1)
    (h₂ : IsRepresentedPlace Q 2) :
    targetCapacity Q ≤ 7 := by
  rw [targetCapacity_eq_three_add_displacement_add_gifts]
  have hbound := displacement_add_gifts_le_four_of_three_rational_places
    Q hQ h₀ h₁ h₂
  omega

end

end N5
end UnrestrictedBooleanMul
