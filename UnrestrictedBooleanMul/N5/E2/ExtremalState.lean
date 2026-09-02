import UnrestrictedBooleanMul.N5.E2.EnvelopeStates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The normalized extremal two-defect envelope

The extremal case `W_{*P}` of manuscript Proposition 10.2 is obtained from
the degree-two envelope by adjoining one rational first-jet target direction.
We normalize the rational place to zero; the other two choices are conjugate
under the already formalized rational-place symmetry.

This construction is deliberately expressed as a subspace sum.  Its target
intersection then follows from modularity of the submodule lattice and the
previously checked intersection for `wStarTwoSpace`, without repeating the
large cross-coordinate calculation.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

noncomputable section

/-- Six independent target directions in the normalized extremal envelope. -/
def wStarZeroBaseCoeff : Fin 6 → TargetCoeff :=
  Fin.snoc wStarBaseCoeff jZeroCoeff

/-- Coordinates one and four separate the added jet from the old target
base, so no six-vector elimination is needed. -/
theorem jZeroCoeff_not_mem_wStarBaseCoeffSpan :
    jZeroCoeff ∉ Submodule.span F₂ (Set.range wStarBaseCoeff) := by
  intro hmem
  rcases (Submodule.mem_span_range_iff_exists_fun
      (R := F₂) (v := wStarBaseCoeff) (x := jZeroCoeff)).mp hmem with
    ⟨f, hf⟩
  have h1 := congrFun hf (1 : Fin 9)
  have h4 := congrFun hf (4 : Fin 9)
  simp [wStarBaseCoeff, outsideHankelWord, rankTwoHankelWord,
    rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff,
    dStarZeroCoeff, dStarOneCoeff, Fin.sum_univ_succ] at h1 h4
  exact one_ne_zero (h1.symm.trans h4)

theorem wStarZeroBaseCoeff_linearIndependent :
    LinearIndependent F₂ wStarZeroBaseCoeff := by
  exact wStarBaseCoeff_linearIndependent.finSnoc
    jZeroCoeff_not_mem_wStarBaseCoeffSpan

/-- The normalized extremal quadratic envelope `W_{*0}`. -/
def wStarZeroTwoSpace : Submodule F₂ TwoForm :=
  wStarTwoSpace ⊔ Submodule.span F₂ {targetTwo jZeroCoeff}

/-- Its six-dimensional target part. -/
def wStarZeroTargetBase : Submodule F₂ TwoForm :=
  wStarTargetBase ⊔ Submodule.span F₂ {targetTwo jZeroCoeff}

theorem wStarZeroTargetBase_eq_coeffTargetTwoSpan :
    wStarZeroTargetBase = coeffTargetTwoSpan wStarZeroBaseCoeff := by
  apply le_antisymm
  · apply sup_le
    · rw [wStarTargetBase, coeffTargetTwoSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [coeffTargetTwoSpan]
      apply Submodule.subset_span
      fin_cases i
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
    · rw [Submodule.span_le]
      rintro _ h
      rw [Set.mem_singleton_iff.mp h, coeffTargetTwoSpan]
      exact Submodule.subset_span ⟨5, rfl⟩
  · rw [coeffTargetTwoSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · apply Submodule.mem_sup_left
      rw [wStarTargetBase, coeffTargetTwoSpan]
      exact Submodule.subset_span ⟨0, rfl⟩
    · apply Submodule.mem_sup_left
      rw [wStarTargetBase, coeffTargetTwoSpan]
      exact Submodule.subset_span ⟨1, rfl⟩
    · apply Submodule.mem_sup_left
      rw [wStarTargetBase, coeffTargetTwoSpan]
      exact Submodule.subset_span ⟨2, rfl⟩
    · apply Submodule.mem_sup_left
      rw [wStarTargetBase, coeffTargetTwoSpan]
      exact Submodule.subset_span ⟨3, rfl⟩
    · apply Submodule.mem_sup_left
      rw [wStarTargetBase, coeffTargetTwoSpan]
      exact Submodule.subset_span ⟨4, rfl⟩
    · apply Submodule.mem_sup_right
      exact Submodule.subset_span (Set.mem_singleton _)

theorem wStarZeroTargetBase_finrank :
    Module.finrank F₂ wStarZeroTargetBase = 6 := by
  rw [wStarZeroTargetBase_eq_coeffTargetTwoSpan]
  exact coeffTargetTwoSpan_finrank wStarZeroBaseCoeff
    wStarZeroBaseCoeff_linearIndependent

theorem targetTwo_jZero_not_mem_wStarTargetBase :
    targetTwo jZeroCoeff ∉ wStarTargetBase := by
  intro hmem
  have hspan : Submodule.span F₂ {targetTwo jZeroCoeff} ≤
      wStarTargetBase := by
    rw [Submodule.span_le]
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact hmem
  have heq : wStarZeroTargetBase = wStarTargetBase := by
    rw [wStarZeroTargetBase, sup_eq_left]
    exact hspan
  have hdim := wStarZeroTargetBase_finrank
  rw [heq, wStarTargetBase_finrank] at hdim
  omega

theorem targetTwo_jZero_not_mem_wStarTwoSpace :
    targetTwo jZeroCoeff ∉ wStarTwoSpace := by
  intro hmem
  apply targetTwo_jZero_not_mem_wStarTargetBase
  rw [← targetTwoSpace_inf_wStarTwoSpace]
  exact ⟨targetTwo_mem_targetTwoSpace jZeroCoeff, hmem⟩

theorem wStarZeroTwoSpace_finrank :
    Module.finrank F₂ wStarZeroTwoSpace = 8 := by
  rw [wStarZeroTwoSpace,
    Submodule.finrank_sup_span_singleton
      targetTwo_jZero_not_mem_wStarTwoSpace,
    wStarTwoSpace_finrank]

theorem targetTwoSpace_inf_wStarZeroTwoSpace :
    targetTwoSpace ⊓ wStarZeroTwoSpace = wStarZeroTargetBase := by
  have hjet : Submodule.span F₂ {targetTwo jZeroCoeff} ≤
      targetTwoSpace := by
    rw [Submodule.span_le]
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact targetTwo_mem_targetTwoSpace jZeroCoeff
  calc
    targetTwoSpace ⊓ wStarZeroTwoSpace =
        (wStarTwoSpace ⊔ Submodule.span F₂ {targetTwo jZeroCoeff}) ⊓
          targetTwoSpace := by rw [wStarZeroTwoSpace, inf_comm]
    _ = (Submodule.span F₂ {targetTwo jZeroCoeff} ⊔ wStarTwoSpace) ⊓
          targetTwoSpace := by rw [sup_comm]
    _ = Submodule.span F₂ {targetTwo jZeroCoeff} ⊔
          (wStarTwoSpace ⊓ targetTwoSpace) :=
      sup_inf_assoc_of_le wStarTwoSpace hjet
    _ = Submodule.span F₂ {targetTwo jZeroCoeff} ⊔
          wStarTargetBase := by
      rw [inf_comm, targetTwoSpace_inf_wStarTwoSpace]
    _ = wStarZeroTargetBase := by
      rw [wStarZeroTargetBase, sup_comm]

theorem wStarZero_target_intersection_finrank :
    Module.finrank F₂ ↑(targetTwoSpace ⊓ wStarZeroTwoSpace) = 6 := by
  rw [targetTwoSpace_inf_wStarZeroTwoSpace,
    wStarZeroTargetBase_finrank]

/-- The normalized extremal envelope lifted to the ANF circuit state. -/
def wStarZeroState : Submodule F₂ (ANF 10) :=
  quadraticEnvelopeState wStarZeroTwoSpace

theorem wStarZeroState_targetRank :
    N4.flagTargetRank wStarZeroState (mulTarget 5) = 6 := by
  rw [wStarZeroState, quadraticEnvelopeState_targetRank, inf_comm,
    wStarZero_target_intersection_finrank]

theorem wStarZeroState_defectRank :
    N4.flagDefectRank wStarZeroState (mulTarget 5) = 2 := by
  rw [wStarZeroState, quadraticEnvelopeState_defectRank,
    wStarZeroTwoSpace_finrank, inf_comm,
    wStarZero_target_intersection_finrank]

end
end E2
end N5
end UnrestrictedBooleanMul
