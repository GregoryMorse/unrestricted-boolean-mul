import UnrestrictedBooleanMul.Mul
import Mathlib.Tactic.FinCases

/-!
# The five-term multiplication target

This module starts the `n = 5` formalization with the part that is independent
of the closed-place case analysis.  Nine private quadratic coefficients show
that the nine output coordinates of `Mul 5` are linearly independent.  The
same projection gives the unconditional nine-AND dimension lower bound.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- One private cross monomial for each output coefficient of `Mul 5`. -/
def fiveTargetAnchor : Fin 9 → Monomial 10 :=
  ![⟨{0, 5}⟩, ⟨{0, 6}⟩, ⟨{0, 7}⟩, ⟨{0, 8}⟩, ⟨{0, 9}⟩,
    ⟨{1, 9}⟩, ⟨{2, 9}⟩, ⟨{3, 9}⟩, ⟨{4, 9}⟩]

/-- Projection to the nine private target coefficients. -/
def fiveTargetProjection : ANF 10 →ₗ[F₂] (Fin 9 → F₂) :=
  coefficientProjection fiveTargetAnchor

theorem fiveTargetAnchor_degree (i : Fin 9) :
    (fiveTargetAnchor i).vars.card = 2 := by
  fin_cases i <;> decide

theorem fiveTargetProjection_kills_affine :
    affine 10 ≤ LinearMap.ker fiveTargetProjection :=
  coefficientProjection_kills_affine fiveTargetAnchor fiveTargetAnchor_degree

local macro "prove_five_target_row" : tactic =>
  `(tactic|
    ext j <;> fin_cases j <;>
      simp [fiveTargetProjection, coefficientProjection, fiveTargetAnchor, Mul,
        mulCoefficient, Fin.sum_univ_succ, aVar, bVar, X, monomial_mul,
        Pi.basisFun] <;> decide)

private theorem fiveTargetProjection_Mul_0 :
    fiveTargetProjection (Mul 5 0) = (Pi.basisFun F₂ (Fin 9)) 0 := by
  prove_five_target_row

private theorem fiveTargetProjection_Mul_1 :
    fiveTargetProjection (Mul 5 1) = (Pi.basisFun F₂ (Fin 9)) 1 := by
  prove_five_target_row

private theorem fiveTargetProjection_Mul_2 :
    fiveTargetProjection (Mul 5 2) = (Pi.basisFun F₂ (Fin 9)) 2 := by
  prove_five_target_row

private theorem fiveTargetProjection_Mul_3 :
    fiveTargetProjection (Mul 5 3) = (Pi.basisFun F₂ (Fin 9)) 3 := by
  prove_five_target_row

private theorem fiveTargetProjection_Mul_4 :
    fiveTargetProjection (Mul 5 4) = (Pi.basisFun F₂ (Fin 9)) 4 := by
  prove_five_target_row

private theorem fiveTargetProjection_Mul_5 :
    fiveTargetProjection (Mul 5 5) = (Pi.basisFun F₂ (Fin 9)) 5 := by
  prove_five_target_row

private theorem fiveTargetProjection_Mul_6 :
    fiveTargetProjection (Mul 5 6) = (Pi.basisFun F₂ (Fin 9)) 6 := by
  prove_five_target_row

private theorem fiveTargetProjection_Mul_7 :
    fiveTargetProjection (Mul 5 7) = (Pi.basisFun F₂ (Fin 9)) 7 := by
  prove_five_target_row

private theorem fiveTargetProjection_Mul_8 :
    fiveTargetProjection (Mul 5 8) = (Pi.basisFun F₂ (Fin 9)) 8 := by
  prove_five_target_row

theorem fiveTargetProjection_Mul (i : Fin 9) :
    fiveTargetProjection (Mul 5 i) = (Pi.basisFun F₂ (Fin 9)) i := by
  fin_cases i
  · exact fiveTargetProjection_Mul_0
  · exact fiveTargetProjection_Mul_1
  · exact fiveTargetProjection_Mul_2
  · exact fiveTargetProjection_Mul_3
  · exact fiveTargetProjection_Mul_4
  · exact fiveTargetProjection_Mul_5
  · exact fiveTargetProjection_Mul_6
  · exact fiveTargetProjection_Mul_7
  · exact fiveTargetProjection_Mul_8

/-- The nine coefficient functions of five-term multiplication are linearly
independent over `F₂`. -/
theorem mulFive_linearIndependent : LinearIndependent F₂ (Mul 5) := by
  apply LinearIndependent.of_comp fiveTargetProjection
  have h : fiveTargetProjection ∘ Mul 5 = (Pi.basisFun F₂ (Fin 9)) := by
    funext i
    exact fiveTargetProjection_Mul i
  rw [h]
  exact (Pi.basisFun F₂ (Fin 9)).linearIndependent

theorem mulTarget_five_finrank : Module.finrank F₂ (mulTarget 5) = 9 := by
  exact finrank_span_eq_card mulFive_linearIndependent

/-- The target-dimension layer of the lower bound.  The paper strengthens
this from nine to thirteen by controlling quotient defects and nonlinear
feedback. -/
theorem mul_five_dimension_lower (r : Nat) (h : HasCircuit (Mul 5) r) :
    9 ≤ r := by
  rcases h with ⟨⟨C, computes⟩⟩
  exact circuit_lower_bound_of_projection C (Mul 5) fiveTargetProjection
    fiveTargetProjection_kills_affine fiveTargetProjection_Mul computes

end

end N5
end UnrestrictedBooleanMul
