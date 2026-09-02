import UnrestrictedBooleanMul.N5.StableTargetInduction
import UnrestrictedBooleanMul.N5.FirstOrderState
import UnrestrictedBooleanMul.N5.QuadraticCoordinates
import UnrestrictedBooleanMul.N5.LowProductSemantic

/-!
# Normal form for a first escape from the first-order envelope

Because the first-order target envelope has codimension one, every target
word outside it has the unique nonzero missing-coset coordinate.  Combining
that fact with the one-step suffix extraction gives the exact product
equation to which the envelope and colour calculations apply.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Every target-ambient word outside the first-order ANF envelope has
quadratic coefficient `firstOrderMissingCoeff + u`, with `u` in the
first-order coefficient space. -/
theorem exists_missingCoordinates_of_mem_targetAmbient_not_firstOrder
    (t : ANF 10)
    (ht : t ∈ N4.targetAmbient 10 (mulTarget 5))
    (htU : t ∉ firstOrderEnvelopeState) :
    ∃ (a : F₂) (ell : LinearForm) (u : TargetCoeff),
      u ∈ firstOrderEnvelopeCoeffSpace ∧
      t = quadraticCoordinateANF a ell
        (targetTwo (firstOrderMissingCoeff + u)) := by
  have htquad : t ∈ N4.quadraticANFSpace 10 :=
    targetAmbient_five_le_quadraticANFSpace ht
  rcases exists_quadraticCoordinates htquad with ⟨a, ell, q, htcoord⟩
  have hqTarget : q ∈ targetTwoSpace := by
    have hprojection :=
      quadraticProjection_mem_targetTwoSpace_of_mem_targetAmbient ht
    rwa [htcoord, quadraticProjection_quadraticCoordinateANF] at hprojection
  rcases hqTarget with ⟨c, hc⟩
  have hcNot : c ∉ firstOrderEnvelopeCoeffSpace := by
    intro hcU
    apply htU
    change t ∈ E2.quadraticEnvelopeState firstOrderEnvelopeTwoSpace
    rw [E2.mem_quadraticEnvelopeState_iff]
    refine ⟨htquad, ?_⟩
    rw [htcoord, quadraticProjection_quadraticCoordinateANF, ← hc]
    exact ⟨c, hcU, rfl⟩
  have hfunctional : firstOrderMissingFunctional c = 1 := by
    rcases f2_eq_zero_or_one (firstOrderMissingFunctional c) with hzero | hone
    · exact (hcNot ((mem_firstOrderEnvelopeCoeffSpace c).2 hzero)).elim
    · exact hone
  let u : TargetCoeff := c + firstOrderMissingCoeff
  have hu : u ∈ firstOrderEnvelopeCoeffSpace := by
    rw [mem_firstOrderEnvelopeCoeffSpace]
    simp only [u, map_add, hfunctional,
      firstOrderMissingFunctional_missing, CharTwo.add_self_eq_zero]
  have hcMissing : c = firstOrderMissingCoeff + u := by
    funext i
    change c i = firstOrderMissingCoeff i +
      (c i + firstOrderMissingCoeff i)
    symm
    calc
      firstOrderMissingCoeff i + (c i + firstOrderMissingCoeff i) =
          (firstOrderMissingCoeff i + firstOrderMissingCoeff i) + c i := by
            ac_rfl
      _ = c i := by rw [CharTwo.add_self_eq_zero, zero_add]
  refine ⟨a, ell, u, hu, ?_⟩
  rw [htcoord, ← hc, hcMissing]
  rfl

/-- A failing target-preservation step has a normalized missing-coset target
on the right side of the actual product equation. -/
theorem exists_missing_product_equation_of_firstOrder_step_escape
    {V : Submodule F₂ (ANF 10)} (p q : ANF 10)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hescape : ¬ (andExtend V p q ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState)) :
    ∃ (a : F₂) (ell : LinearForm) (u : TargetCoeff) (v : ANF 10),
      u ∈ firstOrderEnvelopeCoeffSpace ∧ v ∈ V ∧
      p * q = quadraticCoordinateANF a ell
        (targetTwo (firstOrderMissingCoeff + u)) + v := by
  rcases exists_product_correction_of_targetStep_escape p q hold hescape with
    ⟨t, v, ht, htU, hv, hpq⟩
  rcases exists_missingCoordinates_of_mem_targetAmbient_not_firstOrder
      t ht htU with ⟨a, ell, u, hu, htcoord⟩
  refine ⟨a, ell, u, v, hu, hv, ?_⟩
  rw [hpq, htcoord]

/-- The normalized escape equation simultaneously gives equality of literal
high quotient classes and the missing-coset quadratic shadow equation. -/
theorem firstOrder_missing_product_equation_projections
    (p q v : ANF 10) (a : F₂) (ell : LinearForm) (u : TargetCoeff)
    (heq : p * q = quadraticCoordinateANF a ell
      (targetTwo (firstOrderMissingCoeff + u)) + v) :
    highProjectionTen (p * q) = highProjectionTen v ∧
      quadraticProjection 10 (p * q) =
        targetTwo (firstOrderMissingCoeff + u) + quadraticProjection 10 v := by
  constructor
  · rw [heq, map_add,
      highProjectionTen_eq_zero_of_quadratic
        (quadraticCoordinateANF_mem_quadraticANFSpace a ell
          (targetTwo (firstOrderMissingCoeff + u))), zero_add]
  · rw [heq, map_add, quadraticProjection_quadraticCoordinateANF]

end
end N5
end UnrestrictedBooleanMul
