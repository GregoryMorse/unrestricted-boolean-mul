module

public import UnrestrictedBooleanMul.N3.Coordinates

@[expose] public section

namespace UnrestrictedBooleanMul
open N3Certificate
noncomputable section

theorem ambientBasis_linearIndependent : LinearIndependent F₂ ambientBasis := by
  apply LinearIndependent.of_comp ambientProjection
  have h : ambientProjection ∘ ambientBasis = (Pi.basisFun F₂ (Fin 12)) := by
    funext i
    exact ambientProjection_basis i
  rw [h]
  exact (Pi.basisFun F₂ (Fin 12)).linearIndependent

theorem ambientSpace_finrank : Module.finrank F₂ ambientSpace = 12 := by
  exact finrank_span_eq_card ambientBasis_linearIndependent

def freeBasis : Fin 7 → ANF 6 := ![1, X 0, X 1, X 2, X 3, X 4, X 5]

theorem affine_six_eq_span_freeBasis :
    affine 6 = Submodule.span F₂ (Set.range freeBasis) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p (rfl | ⟨i, rfl⟩)
    · apply Submodule.subset_span
      exact ⟨0, by simp [freeBasis]⟩
    · fin_cases i
      · apply Submodule.subset_span; exact ⟨1, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨2, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨3, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨4, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨5, by simp [freeBasis]⟩
      · apply Submodule.subset_span; exact ⟨6, by simp [freeBasis]⟩
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    fin_cases i
    · simpa [freeBasis] using one_mem_affine 6
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 0)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 1)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 2)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 3)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 4)
    · simpa [freeBasis] using X_mem_affine (m := 6) (i := 5)

theorem affine_six_finrank_le : Module.finrank F₂ (affine 6) ≤ 7 := by
  rw [affine_six_eq_span_freeBasis]
  exact (finrank_span_le_card (Set.range freeBasis)).trans (by
    convert! Fintype.card_range_le freeBasis
    rw [Set.toFinset_card])

theorem rationalBasis_mem (i : Fin 10) : rationalBasis i ∈ rationalSpace :=
  Submodule.subset_span ⟨i, rfl⟩

theorem ambientBasis_mem (i : Fin 12) : ambientBasis i ∈ ambientSpace :=
  Submodule.subset_span ⟨i, rfl⟩

theorem affine_le_rationalSpace : affine 6 ≤ rationalSpace := by
  rw [affine_six_eq_span_freeBasis]
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  fin_cases i
  all_goals first | simpa [freeBasis, rationalBasis] using rationalBasis_mem 0 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 1 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 2 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 3 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 4 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 5 |
    simpa [freeBasis, rationalBasis] using rationalBasis_mem 6

theorem ambientSpace_eq_mulAmbient : ambientSpace = mulAmbient 3 := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using one_mem_affine 6)
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 0))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 1))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 2))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 3))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 4))
    · exact Submodule.mem_sup_left (by simpa [ambientBasis] using X_mem_affine (m := 6) (i := 5))
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 0)
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 1)
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 2)
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 3)
    · exact Submodule.mem_sup_right (by simpa [ambientBasis] using Mul_mem_target 3 4)
  · apply sup_le
    · rw [affine_six_eq_span_freeBasis]
      apply Submodule.span_le.mpr
      rintro p ⟨i, rfl⟩
      fin_cases i
      all_goals first | simpa [freeBasis, ambientBasis] using ambientBasis_mem 0 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 1 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 2 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 3 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 4 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 5 |
        simpa [freeBasis, ambientBasis] using ambientBasis_mem 6
    · apply Submodule.span_le.mpr
      rintro p ⟨i, rfl⟩
      fin_cases i
      all_goals first | simpa [ambientBasis] using ambientBasis_mem 7 |
        simpa [ambientBasis] using ambientBasis_mem 8 |
        simpa [ambientBasis] using ambientBasis_mem 9 |
        simpa [ambientBasis] using ambientBasis_mem 10 |
        simpa [ambientBasis] using ambientBasis_mem 11

theorem targetSum_mem_ambientSpace : targetSum ∈ ambientSpace := by
  apply Submodule.sum_mem
  intro i _hi
  fin_cases i
  · simpa [ambientBasis] using ambientBasis_mem 7
  · simpa [ambientBasis] using ambientBasis_mem 8
  · simpa [ambientBasis] using ambientBasis_mem 9
  · simpa [ambientBasis] using ambientBasis_mem 10
  · simpa [ambientBasis] using ambientBasis_mem 11

theorem rationalSpace_le_ambientSpace : rationalSpace ≤ ambientSpace := by
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  fin_cases i
  all_goals first | simpa [rationalBasis, ambientBasis] using ambientBasis_mem 0 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 1 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 2 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 3 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 4 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 5 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 6 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 7 |
    simpa [rationalBasis, ambientBasis] using ambientBasis_mem 11 |
    simpa [rationalBasis] using targetSum_mem_ambientSpace

macro "solve_ambient_coeff" : tactic =>
  `(tactic|
    (simp +decide [ambientRep, ambientBasis, UnrestrictedBooleanMul.Mul,
      mulCoefficient, aVar, bVar, X, monomial_mul, coeff_monomial,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero]))


end

end UnrestrictedBooleanMul
