import UnrestrictedBooleanMul.Phase3.Flag
import Mathlib.Tactic.FinCases

/-!
# The four-term target and its ambient dimension

This file supplies concrete coordinate projections for the nine affine and
seven target directions.  They make the flag ledger numerically usable while
keeping all proofs in ordinary linear algebra over `F₂`.
-/

namespace UnrestrictedBooleanMul
namespace Phase3

noncomputable section

def targetANFLinear : TargetCoeff →ₗ[F₂] ANF 8 where
  toFun := targetANF
  map_add' c d := by
    simp only [targetANF, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [targetANF, Pi.smul_apply, Finset.smul_sum, smul_smul,
      RingHom.id_apply, smul_eq_mul]

@[simp] theorem targetANFLinear_apply (c : TargetCoeff) :
    targetANFLinear c = targetANF c := rfl

/-- Seven quadratic monomials, one private to each coordinate of `Mul 4`. -/
def fourTargetAnchor : Fin 7 → Monomial 8 :=
  ![⟨{0, 4}⟩, ⟨{0, 5}⟩, ⟨{0, 6}⟩, ⟨{0, 7}⟩,
    ⟨{1, 7}⟩, ⟨{2, 7}⟩, ⟨{3, 7}⟩]

def fourTargetProjection : ANF 8 →ₗ[F₂] (Fin 7 → F₂) :=
  coefficientProjection fourTargetAnchor

theorem fourTargetAnchor_degree (i : Fin 7) :
    (fourTargetAnchor i).vars.card = 2 := by
  fin_cases i <;> decide

theorem fourTargetProjection_kills_affine :
    affine 8 ≤ LinearMap.ker fourTargetProjection :=
  coefficientProjection_kills_affine fourTargetAnchor fourTargetAnchor_degree

theorem fourTargetProjection_Mul (i : Fin 7) :
    fourTargetProjection (Mul 4 i) = (Pi.basisFun F₂ (Fin 7)) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [fourTargetProjection, coefficientProjection, fourTargetAnchor, Mul,
      mulCoefficient, Fin.sum_univ_succ, aVar, bVar, X, monomial_mul,
      Pi.basisFun] <;> decide

theorem fourTargetProjection_targetANF (c : TargetCoeff) :
    fourTargetProjection (targetANF c) = c := by
  funext j
  simp only [targetANF, map_sum, map_smul, fourTargetProjection_Mul,
    Finset.sum_apply]
  rw [Fintype.sum_eq_single j]
  · simp [Pi.basisFun]
  · intro i hi
    simp [Pi.basisFun, hi]

theorem targetANF_injective : Function.Injective targetANF := by
  intro c d h
  have hp := congrArg fourTargetProjection h
  simpa [fourTargetProjection_targetANF] using hp

theorem targetANF_mem_mulTarget (c : TargetCoeff) :
    targetANF c ∈ mulTarget 4 := by
  apply Submodule.sum_mem
  intro i _hi
  exact Submodule.smul_mem _ _ (Mul_mem_target 4 i)

theorem mulFour_linearIndependent : LinearIndependent F₂ (Mul 4) := by
  apply LinearIndependent.of_comp fourTargetProjection
  have h : fourTargetProjection ∘ Mul 4 = (Pi.basisFun F₂ (Fin 7)) := by
    funext i
    exact fourTargetProjection_Mul i
  rw [h]
  exact (Pi.basisFun F₂ (Fin 7)).linearIndependent

theorem mulTarget_four_finrank : Module.finrank F₂ (mulTarget 4) = 7 := by
  exact finrank_span_eq_card mulFour_linearIndependent

/-- A concrete basis for the affine input space on eight variables. -/
def affineFourBasis : Fin 9 → ANF 8 :=
  ![1, X 0, X 1, X 2, X 3, X 4, X 5, X 6, X 7]

def affineFourAnchor : Fin 9 → Monomial 8 :=
  ![⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{2}⟩, ⟨{3}⟩,
    ⟨{4}⟩, ⟨{5}⟩, ⟨{6}⟩, ⟨{7}⟩]

def affineFourProjection : ANF 8 →ₗ[F₂] (Fin 9 → F₂) :=
  coefficientProjection affineFourAnchor

theorem affineFourProjection_basis (i : Fin 9) :
    affineFourProjection (affineFourBasis i) =
      (Pi.basisFun F₂ (Fin 9)) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [affineFourProjection, coefficientProjection, affineFourAnchor,
      affineFourBasis, X, monomial, Pi.basisFun] <;> decide

theorem affineFourBasis_linearIndependent :
    LinearIndependent F₂ affineFourBasis := by
  apply LinearIndependent.of_comp affineFourProjection
  have h : affineFourProjection ∘ affineFourBasis =
      (Pi.basisFun F₂ (Fin 9)) := by
    funext i
    exact affineFourProjection_basis i
  rw [h]
  exact (Pi.basisFun F₂ (Fin 9)).linearIndependent

theorem affine_eight_eq_span :
    affine 8 = Submodule.span F₂ (Set.range affineFourBasis) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p (rfl | ⟨i, rfl⟩)
    · apply Submodule.subset_span
      exact ⟨0, by simp [affineFourBasis]⟩
    · fin_cases i
      all_goals apply Submodule.subset_span
      · exact ⟨1, by simp [affineFourBasis]⟩
      · exact ⟨2, by simp [affineFourBasis]⟩
      · exact ⟨3, by simp [affineFourBasis]⟩
      · exact ⟨4, by simp [affineFourBasis]⟩
      · exact ⟨5, by simp [affineFourBasis]⟩
      · exact ⟨6, by simp [affineFourBasis]⟩
      · exact ⟨7, by simp [affineFourBasis]⟩
      · exact ⟨8, by simp [affineFourBasis]⟩
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    fin_cases i
    · simpa [affineFourBasis] using one_mem_affine 8
    · simpa [affineFourBasis] using X_mem_affine (m := 8) (i := 0)
    · simpa [affineFourBasis] using X_mem_affine (m := 8) (i := 1)
    · simpa [affineFourBasis] using X_mem_affine (m := 8) (i := 2)
    · simpa [affineFourBasis] using X_mem_affine (m := 8) (i := 3)
    · simpa [affineFourBasis] using X_mem_affine (m := 8) (i := 4)
    · simpa [affineFourBasis] using X_mem_affine (m := 8) (i := 5)
    · simpa [affineFourBasis] using X_mem_affine (m := 8) (i := 6)
    · simpa [affineFourBasis] using X_mem_affine (m := 8) (i := 7)

theorem affine_eight_finrank : Module.finrank F₂ (affine 8) = 9 := by
  rw [affine_eight_eq_span]
  exact finrank_span_eq_card affineFourBasis_linearIndependent

/-- The affine and target spaces meet trivially.  The proof projects to the
seven private quadratic coefficients, so it is both symbolic and inexpensive. -/
theorem affine_disjoint_mulTarget_four : Disjoint (affine 8) (mulTarget 4) := by
  rw [disjoint_iff_inf_le]
  intro p hp
  rcases (Submodule.mem_span_range_iff_exists_fun (R := F₂)
    (v := Mul 4) (x := p)).mp hp.2 with ⟨c, hc⟩
  have hprojAffine : fourTargetProjection p = 0 := by
    rw [← LinearMap.mem_ker]
    exact fourTargetProjection_kills_affine hp.1
  have hprojRep : fourTargetProjection (∑ i, c i • Mul 4 i) = c := by
    funext j
    simp only [map_sum, map_smul, fourTargetProjection_Mul, Finset.sum_apply]
    rw [Fintype.sum_eq_single j]
    · simp [Pi.basisFun]
    · intro i hi
      simp [Pi.basisFun, hi]
  have hc0 : c = 0 := by
    rw [hc] at hprojRep
    exact hprojRep.symm.trans hprojAffine
  rw [← hc, hc0]
  simp

theorem targetAmbient_four_finrank :
    Module.finrank F₂ (targetAmbient 8 (mulTarget 4)) = 16 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (affine 8) (mulTarget 4)
  rw [affine_disjoint_mulTarget_four.eq_bot, finrank_bot,
    add_zero, affine_eight_finrank, mulTarget_four_finrank] at hdim
  unfold targetAmbient
  omega

theorem final_target_rank_four (C : Circuit 8 8) (hC : C.Computes (Mul 4)) :
    flagTargetRank C.finalWire (mulTarget 4) = 7 := by
  have hamb : targetAmbient 8 (mulTarget 4) ≤ C.finalWire := by
    apply sup_le
    · simpa [Circuit.finalWire] using affine_le_wireSpace C.gate (j := 8)
    · apply Submodule.span_le.mpr
      rintro p ⟨i, rfl⟩
      exact hC i
  have hinf : C.finalWire ⊓ targetAmbient 8 (mulTarget 4) =
      targetAmbient 8 (mulTarget 4) := inf_eq_right.mpr hamb
  unfold flagTargetRank
  rw [hinf, targetAmbient_four_finrank, affine_eight_finrank]

/-- A circuit with `r` gates has final dimension at most affine dimension plus
`r`, whether or not some gate is redundant. -/
theorem finalWire_finrank_le_affine_add {m r : Nat} (C : Circuit m r) :
    Module.finrank F₂ C.finalWire ≤ Module.finrank F₂ (affine m) + r := by
  rw [C.finalWire_eq]
  have hspan :
      Module.finrank F₂ (Submodule.span F₂ (Set.range C.gate)) ≤ r := by
    exact (finrank_span_le_card (Set.range C.gate)).trans (by
      convert! Fintype.card_range_le C.gate
      rw [Set.toFinset_card]
      simp)
  have hsup := Submodule.finrank_add_le_finrank_add_finrank
    (affine m) (Submodule.span F₂ (Set.range C.gate))
  omega

/-- The defect budget of any hypothetical eight-gate circuit for `Mul 4` is
at most one; no nonredundancy assumption is needed. -/
theorem eight_gate_defect_le_one (C : Circuit 8 8)
    (hC : C.Computes (Mul 4)) :
    flagDefectRank C.finalWire (mulTarget 4) ≤ 1 := by
  have hledger := flag_rank_ledger (V := C.finalWire) (T := mulTarget 4)
    (by simpa [Circuit.finalWire] using affine_le_wireSpace C.gate (j := 8))
  have ht := final_target_rank_four C hC
  have hdim := finalWire_finrank_le_affine_add C
  rw [ht, affine_eight_finrank] at hledger
  rw [affine_eight_finrank] at hdim
  omega

theorem eight_gate_defect_is_one (C : Circuit 8 8)
    (hC : C.Computes (Mul 4))
    (hnr : ∀ i : Fin 8, NonredundantAt C i) :
    flagDefectRank C.finalWire (mulTarget 4) = 1 := by
  have hcount := circuit_flag_defect_count C (mulTarget 4) (j := 8) (by rfl)
    (by intro i _hi; exact hnr i)
  have ht := final_target_rank_four C hC
  have hfinal : circuitFlag C 8 = C.finalWire := rfl
  rw [hfinal, ht] at hcount
  omega

end

end Phase3
end UnrestrictedBooleanMul
