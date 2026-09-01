import UnrestrictedBooleanMul.N5.RelationGiftCoefficients

/-!
# Displacement pivots in target coefficients

This module transports the exact represented-place displacement profile from
two-forms to the nine target coefficients.  It gives the relation-gift map its
smallest natural codomain and records the resulting weak dimension bound.  The
remaining content of manuscript Theorem 6.2 is thereby isolated as two extra
sparse-incidence pivot conditions.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Active closed-place directions before embedding into two-forms. -/
def activeDisplacementCoeffDirection
    (Q : Submodule F₂ QuadraticQuotient)
    (i : ActiveDisplacementDirection Q) : TargetCoeff :=
  closedPlaceDirections i.1

/-- The coefficient version of the intrinsic displacement space. -/
def activeDisplacementCoeffSpace
    (Q : Submodule F₂ QuadraticQuotient) : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ (Set.range (activeDisplacementCoeffDirection Q))

/-- Embedding the active coefficient directions gives exactly the active
two-form displacement space. -/
theorem activeDisplacementCoeffSpace_map_targetTwo
    (Q : Submodule F₂ QuadraticQuotient) :
    (activeDisplacementCoeffSpace Q).map targetTwoLinear =
      activeDisplacementTwoSpace Q := by
  rw [activeDisplacementCoeffSpace, Submodule.map_span,
    activeDisplacementTwoSpace]
  apply congrArg (Submodule.span F₂)
  ext p
  simp [activeDisplacementCoeffDirection,
    activeDisplacementTwoDirection, targetTwo]

/-- The intrinsic displacement coefficients are exactly the active
closed-place coefficient directions. -/
theorem localDisplacementCoeffSpace_eq_active
    (Q : Submodule F₂ QuadraticQuotient) :
    localDisplacementCoeffSpace Q = activeDisplacementCoeffSpace Q := by
  rw [localDisplacementCoeffSpace,
    localDisplacementSpace_eq_activeDisplacementTwoSpace,
    ← activeDisplacementCoeffSpace_map_targetTwo]
  exact (Submodule.comap_map_eq_of_injective
    targetTwoLinear_injective) (activeDisplacementCoeffSpace Q)

/-- Every active closed-place coefficient direction belongs to the intrinsic
coefficient displacement space. -/
theorem closedPlaceDirection_mem_localDisplacementCoeffSpace
    (Q : Submodule F₂ QuadraticQuotient) (i : Fin 8)
    (hi : IsActiveDisplacementDirection Q i) :
    closedPlaceDirections i ∈ localDisplacementCoeffSpace Q := by
  rw [localDisplacementCoeffSpace_eq_active, activeDisplacementCoeffSpace]
  apply Submodule.subset_span
  exact ⟨⟨i, hi⟩, rfl⟩

/-- The active coefficient directions remain linearly independent. -/
theorem activeDisplacementCoeffDirection_linearIndependent
    (Q : Submodule F₂ QuadraticQuotient) :
    LinearIndependent F₂ (activeDisplacementCoeffDirection Q) := by
  exact closedPlaceDirections_linearIndependent.comp
    (fun i : ActiveDisplacementDirection Q ↦ i.1)
    Subtype.val_injective

/-- Exact numerical dimension of the intrinsic coefficient displacement
space. -/
theorem localDisplacementCoeffSpace_finrank
    (Q : Submodule F₂ QuadraticQuotient) :
    Module.finrank F₂ (localDisplacementCoeffSpace Q) =
      3 + representedPlaceWeight Q := by
  rw [localDisplacementCoeffSpace_eq_active,
    activeDisplacementCoeffSpace]
  calc
    Module.finrank F₂
        (Submodule.span F₂
          (Set.range (activeDisplacementCoeffDirection Q))) =
        Fintype.card (ActiveDisplacementDirection Q) :=
      finrank_span_eq_card
        (activeDisplacementCoeffDirection_linearIndependent Q)
    _ = 3 + representedPlaceWeight Q :=
      activeDisplacementDirection_card Q

/-- The nine target coefficients have dimension nine. -/
theorem targetCoeff_finrank : Module.finrank F₂ TargetCoeff = 9 := by
  simp [TargetCoeff]

/-- Exact dimension of the coefficient gift quotient. -/
theorem targetCoeffQuotient_finrank
    (Q : Submodule F₂ QuadraticQuotient) :
    Module.finrank F₂
        (TargetCoeff ⧸ localDisplacementCoeffSpace Q) =
      6 - representedPlaceWeight Q := by
  rw [Submodule.finrank_quotient,
    targetCoeff_finrank, localDisplacementCoeffSpace_finrank]
  omega

/-- The coefficient model gives the immediate ambient-quotient bound on
relation gifts.  The sparse displacement pivots will sharpen the right side
from `6 - d` to `4 - d`. -/
theorem relationGiftRank_le_six_sub_representedPlaceWeight
    (Q : Submodule F₂ QuadraticQuotient) :
    relationGiftRank Q ≤ 6 - representedPlaceWeight Q := by
  rw [relationGiftRank_eq_coefficients,
    ← targetCoeffQuotient_finrank Q]
  exact Submodule.finrank_le _

/-- Additive form of the ambient coefficient-quotient bound. -/
theorem representedPlaceWeight_add_relationGiftRank_le_six
    (Q : Submodule F₂ QuadraticQuotient) :
    representedPlaceWeight Q + relationGiftRank Q ≤ 6 := by
  have h := relationGiftRank_le_six_sub_representedPlaceWeight Q
  have hweight : 3 + representedPlaceWeight Q ≤ 9 := by
    have hsub := Submodule.finrank_le (localDisplacementCoeffSpace Q)
    have hamb := targetCoeff_finrank
    rw [localDisplacementCoeffSpace_finrank] at hsub
    omega
  omega

end

end N5
end UnrestrictedBooleanMul
