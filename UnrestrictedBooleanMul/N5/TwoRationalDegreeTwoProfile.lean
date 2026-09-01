import UnrestrictedBooleanMul.N5.RationalPlaceSymmetry

/-!
# The two-rational plus degree-two capacity profile

The expensive algebraic obstruction is supplied once for each rational pair
by `RationalPlaceSymmetry`.  This module factors the remaining Fano-space
argument uniformly: an empty triple-sum fiber leaves only the three
represented populated points, so the relation kernel and its gift vanish.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem populatedPoint_cases_of_twoRational_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j : Fin 4) (hij : i ≠ j) (hi3 : i ≠ 3) (hj3 : j ≠ 3)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (h3 : IsRepresentedPlace Q 3)
    (hempty : ∀ q r s : LocalKleinParam,
      RationalLocalEffective q → RationalLocalEffective r →
        DegreeTwoLocalEffective s →
        decomposableFiber
          (closedPlaceQuotientPoint i q + closedPlaceQuotientPoint j r +
            closedPlaceQuotientPoint 3 s) = ∅)
    (y : PopulatedPoint Q) :
    y = representedPopulatedPoint Q i hi ∨
      y = representedPopulatedPoint Q j hj ∨
      y = representedPopulatedPoint Q 3 h3 := by
  let pi := representedClosedPlaceParam Q i hi
  let pj := representedClosedPlaceParam Q j hj
  let p3 := representedClosedPlaceParam Q 3 h3
  let qi : LocalKleinParam := pi.2.1
  let qj : LocalKleinParam := pj.2.1
  let q3 : LocalKleinParam := p3.2.1
  have hqi : RationalLocalEffective qi := by
    have hm := pi.2.2
    change qi ∈ effectiveParamsAt i at hm
    rw [effectiveParamsAt, if_neg hi3] at hm
    simpa [rationalEffectiveParams] using hm
  have hqj : RationalLocalEffective qj := by
    have hm := pj.2.2
    change qj ∈ effectiveParamsAt j at hm
    rw [effectiveParamsAt, if_neg hj3] at hm
    simpa [rationalEffectiveParams] using hm
  have hq3 : DegreeTwoLocalEffective q3 := by
    have hm := p3.2.2
    change q3 ∈ degreeTwoEffectiveParams at hm
    simpa [degreeTwoEffectiveParams] using hm
  have hcases := populatedPoint_cases_of_three_distinct_places
    Q hQ i j 3 hi hj h3 hij hi3 hj3 y
  change y = representedPopulatedPoint Q i hi ∨
      y = representedPopulatedPoint Q j hj ∨
      y = representedPopulatedPoint Q 3 h3 ∨
      populatedQuotientPoint y =
        populatedQuotientPoint (representedPopulatedPoint Q i hi) +
          populatedQuotientPoint (representedPopulatedPoint Q j hj) +
          populatedQuotientPoint (representedPopulatedPoint Q 3 h3) at hcases
  rcases hcases with h | h | h | hy
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    have hfiber : populatedLift y ∈ decomposableFiber
        (closedPlaceQuotientPoint i qi +
          closedPlaceQuotientPoint j qj +
          closedPlaceQuotientPoint 3 q3) := by
      have hm := populatedLift_mem_fiber y
      rw [hy] at hm
      simpa [pi, pj, p3, qi, qj, q3, closedPlaceEffectivePoint] using hm
    rw [hempty qi qj q3 hqi hqj hq3] at hfiber
    exact hfiber.elim

theorem populatedPoint_card_le_three_of_twoRational_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j : Fin 4) (hij : i ≠ j) (hi3 : i ≠ 3) (hj3 : j ≠ 3)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (h3 : IsRepresentedPlace Q 3)
    (hempty : ∀ q r s : LocalKleinParam,
      RationalLocalEffective q → RationalLocalEffective r →
        DegreeTwoLocalEffective s →
        decomposableFiber
          (closedPlaceQuotientPoint i q + closedPlaceQuotientPoint j r +
            closedPlaceQuotientPoint 3 s) = ∅) :
    Fintype.card (PopulatedPoint Q) ≤ 3 := by
  classical
  let xi := representedPopulatedPoint Q i hi
  let xj := representedPopulatedPoint Q j hj
  let x3 := representedPopulatedPoint Q 3 h3
  have hsubset : (Finset.univ : Finset (PopulatedPoint Q)) ⊆
      {xi, xj, x3} := by
    intro y hy
    have hcases := populatedPoint_cases_of_twoRational_degreeTwo_places
      Q hQ i j hij hi3 hj3 hi hj h3 hempty y
    simpa [xi, xj, x3] using hcases
  calc
    Fintype.card (PopulatedPoint Q) =
        (Finset.univ : Finset (PopulatedPoint Q)).card :=
      Finset.card_univ.symm
    _ ≤ ({xi, xj, x3} : Finset (PopulatedPoint Q)).card :=
      Finset.card_le_card hsubset
    _ ≤ 3 := Finset.card_le_three

theorem populatedRelationKernel_finrank_eq_zero_of_twoRational_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j : Fin 4) (hij : i ≠ j) (hi3 : i ≠ 3) (hj3 : j ≠ 3)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (h3 : IsRepresentedPlace Q 3)
    (hempty : ∀ q r s : LocalKleinParam,
      RationalLocalEffective q → RationalLocalEffective r →
        DegreeTwoLocalEffective s →
        decomposableFiber
          (closedPlaceQuotientPoint i q + closedPlaceQuotientPoint j r +
            closedPlaceQuotientPoint 3 s) = ∅) :
    Module.finrank F₂
      ↑(relationKernel (populatedQuotientPoint (Q := Q))) = 0 := by
  let x : Fin 3 → PopulatedPoint Q :=
    ![representedPopulatedPoint Q i hi,
      representedPopulatedPoint Q j hj,
      representedPopulatedPoint Q 3 h3]
  have hlinQ : LinearIndependent F₂ (fun k : Fin 3 ↦ (x k).1) := by
    rw [show (fun k : Fin 3 ↦ (x k).1) =
        (![ (representedPopulatedPoint Q i hi).1,
            (representedPopulatedPoint Q j hj).1,
            (representedPopulatedPoint Q 3 h3).1 ] : Fin 3 → Q) by
      funext k
      fin_cases k <;> rfl]
    exact representedTriple_linearIndependent Q i j 3 hi hj h3 hij hi3 hj3
  have hlin : LinearIndependent F₂
      (fun k : Fin 3 ↦ populatedQuotientPoint (x k)) :=
    hlinQ.map' Q.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hsmallSpan : Submodule.span F₂
      (Set.range (fun k : Fin 3 ↦ populatedQuotientPoint (x k))) ≤
      Submodule.span F₂
        (Set.range (populatedQuotientPoint (Q := Q))) := by
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨x k, rfl⟩
  have hspanRank : 3 ≤ Module.finrank F₂
      (Submodule.span F₂
        (Set.range (populatedQuotientPoint (Q := Q)))) := by
    have hrank := Submodule.finrank_mono hsmallSpan
    rw [finrank_span_eq_card hlin] at hrank
    simpa using hrank
  have hkernel := relationKernel_finrank_add_span
    (populatedQuotientPoint (Q := Q))
  have hcard :=
    populatedPoint_card_le_three_of_twoRational_degreeTwo_places
      Q hQ i j hij hi3 hj3 hi hj h3 hempty
  omega

theorem relationGiftRank_eq_zero_of_twoRational_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (i j : Fin 4) (hij : i ≠ j) (hi3 : i ≠ 3) (hj3 : j ≠ 3)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (h3 : IsRepresentedPlace Q 3)
    (hempty : ∀ q r s : LocalKleinParam,
      RationalLocalEffective q → RationalLocalEffective r →
        DegreeTwoLocalEffective s →
        decomposableFiber
          (closedPlaceQuotientPoint i q + closedPlaceQuotientPoint j r +
            closedPlaceQuotientPoint 3 s) = ∅) :
    relationGiftRank Q = 0 := by
  have hgift := relationGiftRank_le_relationKernel Q
  rw [populatedRelationKernel_finrank_eq_zero_of_twoRational_degreeTwo_places
    Q hQ i j hij hi3 hj3 hi hj h3 hempty] at hgift
  omega

theorem relationGiftRank_eq_zero_of_rational12_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h1 : IsRepresentedPlace Q 1)
    (h2 : IsRepresentedPlace Q 2)
    (h3 : IsRepresentedPlace Q 3) :
    relationGiftRank Q = 0 :=
  relationGiftRank_eq_zero_of_twoRational_degreeTwo_places
    Q hQ 1 2 (by decide) (by decide) (by decide) h1 h2 h3
      (fun q r s hq hr hs =>
        rational12_degreeTwo_mixed_decomposableFiber_empty q r s hq hr hs)

theorem relationGiftRank_eq_zero_of_rational02_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h2 : IsRepresentedPlace Q 2)
    (h3 : IsRepresentedPlace Q 3) :
    relationGiftRank Q = 0 :=
  relationGiftRank_eq_zero_of_twoRational_degreeTwo_places
    Q hQ 0 2 (by decide) (by decide) (by decide) h0 h2 h3
      (fun q r s hq hr hs =>
        rational02_degreeTwo_mixed_decomposableFiber_empty q r s hq hr hs)

theorem representedPlaceWeight_eq_four_of_rational12_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h1 : IsRepresentedPlace Q 1)
    (h2 : IsRepresentedPlace Q 2)
    (h3 : IsRepresentedPlace Q 3) :
    representedPlaceWeight Q = 4 := by
  classical
  have h0 : ¬ IsRepresentedPlace Q 0 := by
    intro h0
    apply not_all_closedPlaces_represented Q hQ
    intro k
    fin_cases k <;> assumption
  simp [representedPlaceWeight, representedRationalPlaceCount,
    representedDegreeTwoIndicator, h0, h1, h2, h3]

theorem representedPlaceWeight_eq_four_of_rational02_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h2 : IsRepresentedPlace Q 2)
    (h3 : IsRepresentedPlace Q 3) :
    representedPlaceWeight Q = 4 := by
  classical
  have h1 : ¬ IsRepresentedPlace Q 1 := by
    intro h1
    apply not_all_closedPlaces_represented Q hQ
    intro k
    fin_cases k <;> assumption
  simp [representedPlaceWeight, representedRationalPlaceCount,
    representedDegreeTwoIndicator, h0, h1, h2, h3]

theorem targetCapacity_eq_seven_of_rational12_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h1 : IsRepresentedPlace Q 1)
    (h2 : IsRepresentedPlace Q 2)
    (h3 : IsRepresentedPlace Q 3) :
    targetCapacity Q = 7 := by
  rw [targetCapacity_eq_three_add_representedPlaceWeight_add_gifts,
    representedPlaceWeight_eq_four_of_rational12_degreeTwo_places
      Q hQ h1 h2 h3,
    relationGiftRank_eq_zero_of_rational12_degreeTwo_places
      Q hQ h1 h2 h3]

theorem targetCapacity_eq_seven_of_rational02_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h2 : IsRepresentedPlace Q 2)
    (h3 : IsRepresentedPlace Q 3) :
    targetCapacity Q = 7 := by
  rw [targetCapacity_eq_three_add_representedPlaceWeight_add_gifts,
    representedPlaceWeight_eq_four_of_rational02_degreeTwo_places
      Q hQ h0 h2 h3,
    relationGiftRank_eq_zero_of_rational02_degreeTwo_places
      Q hQ h0 h2 h3]

end

end N5
end UnrestrictedBooleanMul
