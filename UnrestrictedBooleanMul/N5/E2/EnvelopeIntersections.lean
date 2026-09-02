import UnrestrictedBooleanMul.N5.E2.EnvelopeSpaces

/-!
# Exact target intersections of the concrete two-defect envelopes

The five displayed target directions in each Section 10 envelope are not
merely contained in its seven-generator quadratic space: they are its entire
Hankel-target intersection.  The proof uses only equal-antidiagonal cross
coordinates.  In particular, it does not enumerate quadratic forms.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

noncomputable section

def crossCoordinate (i j : Fin 5) : TwoForm →ₗ[F₂] F₂ where
  toFun q := q (quadraticPair (aCoord i) (bCoord j)
    (aCoord_ne_bCoord i j))
  map_add' q r := by simp
  map_smul' a q := by simp

@[simp] theorem crossCoordinate_targetTwo (i j : Fin 5) (c : TargetCoeff) :
    crossCoordinate i j (targetTwo c) = c (hankelIndex i j) :=
  targetTwo_cross c i j

def crossDifference (i j k l : Fin 5) : TwoForm →ₗ[F₂] F₂ where
  toFun q := crossCoordinate i j q + crossCoordinate k l q
  map_add' q r := by
    simp [crossCoordinate]
    abel
  map_smul' a q := by
    simp [crossCoordinate]
    ring

private theorem crossDifference_01_10_target (c : TargetCoeff) :
    crossDifference 0 1 1 0 (targetTwo c) = 0 := by
  simp [crossDifference, hankelIndex, CharTwo.add_self_eq_zero]

private theorem crossDifference_02_11_target (c : TargetCoeff) :
    crossDifference 0 2 1 1 (targetTwo c) = 0 := by
  simp [crossDifference, hankelIndex, CharTwo.add_self_eq_zero]

private theorem crossDifference_11_02_target (c : TargetCoeff) :
    crossDifference 1 1 0 2 (targetTwo c) = 0 := by
  simp [crossDifference, hankelIndex, CharTwo.add_self_eq_zero]

private theorem crossDifference_33_24_target (c : TargetCoeff) :
    crossDifference 3 3 2 4 (targetTwo c) = 0 := by
  simp [crossDifference, hankelIndex, CharTwo.add_self_eq_zero]

private theorem crossDifference_22_04_target (c : TargetCoeff) :
    crossDifference 2 2 0 4 (targetTwo c) = 0 := by
  simp [crossDifference, hankelIndex, CharTwo.add_self_eq_zero]

private theorem crossDifference_01_10_wStarGenerator (i : Fin 7) :
    crossDifference 0 1 1 0 (wStarGenerator i) =
      ![0, 1, 1, 0, 0, 0, 0] i := by
  fin_cases i <;>
    simp [crossDifference, crossCoordinate, wStarGenerator, wStarX00,
      wStarX01, wStarX10, wStarX11, aStarZero, aStarOne,
      bStarZero, bStarOne, aLinear, bLinear, Pi.basisFun,
      hankelIndex, rZeroCoeff, rOneCoeff, rInfinityCoeff,
      CharTwo.add_self_eq_zero]

private theorem crossDifference_02_11_wStarGenerator (i : Fin 7) :
    crossDifference 0 2 1 1 (wStarGenerator i) =
      ![1, 1, 0, 1, 0, 0, 0] i := by
  fin_cases i <;>
    simp [crossDifference, crossCoordinate, wStarGenerator, wStarX00,
      wStarX01, wStarX10, wStarX11, aStarZero, aStarOne,
      bStarZero, bStarOne, aLinear, bLinear, Pi.basisFun,
      hankelIndex, rZeroCoeff, rOneCoeff, rInfinityCoeff,
      CharTwo.add_self_eq_zero]

private theorem crossDifference_11_02_wPQGenerator (i : Fin 7) :
    crossDifference 1 1 0 2 (wPQGenerator i) =
      ![0, 0, 1, 0, 0, 0, 0] i := by
  fin_cases i <;>
    simp [crossDifference, crossCoordinate, wPQGenerator, wPQZZero,
      wPQZInfinity, aLinear, bLinear, Pi.basisFun, hankelIndex,
      rZeroCoeff, jZeroCoeff, rInfinityCoeff, jInfinityCoeff, rOneCoeff,
      CharTwo.add_self_eq_zero]

private theorem crossDifference_33_24_wPQGenerator (i : Fin 7) :
    crossDifference 3 3 2 4 (wPQGenerator i) =
      ![0, 0, 0, 0, 0, 1, 0] i := by
  fin_cases i <;>
    simp [crossDifference, crossCoordinate, wPQGenerator, wPQZZero,
      wPQZInfinity, aLinear, bLinear, Pi.basisFun, hankelIndex,
      rZeroCoeff, jZeroCoeff, rInfinityCoeff, jInfinityCoeff, rOneCoeff,
      CharTwo.add_self_eq_zero]

private theorem crossDifference_11_02_wThreePGenerator (i : Fin 7) :
    crossDifference 1 1 0 2 (wThreePGenerator i) =
      ![0, 0, 0, 1, 0, 0, 0] i := by
  fin_cases i <;>
    simp [crossDifference, crossCoordinate, wThreePGenerator,
      wThreePSecondJet, wThreePUOne, wThreePUTwo, aLinear, bLinear,
      Pi.basisFun, hankelIndex, rZeroCoeff, jZeroCoeff, rOneCoeff,
      rInfinityCoeff, targetBasis, CharTwo.add_self_eq_zero]

private theorem crossDifference_22_04_wThreePGenerator (i : Fin 7) :
    crossDifference 2 2 0 4 (wThreePGenerator i) =
      ![0, 0, 0, 0, 1, 0, 0] i := by
  fin_cases i <;>
    simp [crossDifference, crossCoordinate, wThreePGenerator,
      wThreePSecondJet, wThreePUOne, wThreePUTwo, aLinear, bLinear,
      Pi.basisFun, hankelIndex, rZeroCoeff, jZeroCoeff, rOneCoeff,
      rInfinityCoeff, targetBasis, CharTwo.add_self_eq_zero]

theorem coeffTargetTwoSpan_le_targetTwoSpace {n : Nat}
    (v : Fin n → TargetCoeff) :
    coeffTargetTwoSpan v ≤ targetTwoSpace := by
  rw [coeffTargetTwoSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨v i, rfl⟩

private theorem combination_mem_coeffTargetTwoSpan {n : Nat}
    (v : Fin n → TargetCoeff) (f : Fin n → F₂) :
    ∑ i, f i • targetTwo (v i) ∈ coeffTargetTwoSpan v := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩)

/-! ## Degree-two place -/

theorem targetTwoSpace_inf_wStarTwoSpace :
    targetTwoSpace ⊓ wStarTwoSpace = wStarTargetBase := by
  apply le_antisymm
  · rintro q ⟨⟨c, rfl⟩, hq⟩
    rw [wStarTwoSpace] at hq
    rcases (Submodule.mem_span_range_iff_exists_fun
        (R := F₂) (v := wStarGenerator)
        (x := targetTwo c)).mp hq with ⟨f, hf⟩
    have h01 := congrArg (crossDifference 0 1 1 0) hf
    have h02 := congrArg (crossDifference 0 2 1 1) hf
    rw [map_sum, crossDifference_01_10_target] at h01
    rw [map_sum, crossDifference_02_11_target] at h02
    simp only [map_smul, smul_eq_mul,
      crossDifference_01_10_wStarGenerator] at h01
    simp only [map_smul, smul_eq_mul,
      crossDifference_02_11_wStarGenerator] at h02
    simp [Fin.sum_univ_succ] at h01 h02
    have hf2 : f 2 = f 1 := (CharTwo.add_eq_zero.mp h01).symm
    have hf3 : f 3 = f 0 + f 1 := by
      have h02' : (f 0 + f 1) + f 3 = 0 := by
        simpa [add_assoc] using h02
      exact (CharTwo.add_eq_zero.mp h02').symm
    let g : Fin 5 → F₂ := ![f 4, f 5, f 6, f 0, f 1]
    have hg := combination_mem_coeffTargetTwoSpan wStarBaseCoeff g
    change targetTwo c ∈ wStarTargetBase
    rw [← hf]
    have heq :
        ∑ i, f i • wStarGenerator i =
          ∑ i, g i • targetTwo (wStarBaseCoeff i) := by
      simp [g, wStarBaseCoeff, wStarGenerator, Fin.sum_univ_succ,
        targetTwo_outside8_eq, targetTwo_outside7_eq, hf2, hf3,
        smul_add]
      module
    rw [heq]
    simpa [wStarTargetBase] using hg
  · change coeffTargetTwoSpan wStarBaseCoeff ≤
      targetTwoSpace ⊓ wStarTwoSpace
    exact le_inf
      (coeffTargetTwoSpan_le_targetTwoSpace wStarBaseCoeff)
      wStarTargetBase_le

theorem wStar_target_intersection_finrank :
    Module.finrank F₂ ↑(targetTwoSpace ⊓ wStarTwoSpace) = 5 := by
  rw [targetTwoSpace_inf_wStarTwoSpace, wStarTargetBase_finrank]

/-! ## Two distinct rational places -/

theorem targetTwoSpace_inf_wPQTwoSpace :
    targetTwoSpace ⊓ wPQTwoSpace = wPQTargetBase := by
  apply le_antisymm
  · rintro q ⟨⟨c, rfl⟩, hq⟩
    rw [wPQTwoSpace] at hq
    rcases (Submodule.mem_span_range_iff_exists_fun
        (R := F₂) (v := wPQGenerator)
        (x := targetTwo c)).mp hq with ⟨f, hf⟩
    have h2 := congrArg (crossDifference 1 1 0 2) hf
    have h6 := congrArg (crossDifference 3 3 2 4) hf
    rw [map_sum, crossDifference_11_02_target] at h2
    rw [map_sum, crossDifference_33_24_target] at h6
    simp only [map_smul, smul_eq_mul,
      crossDifference_11_02_wPQGenerator] at h2
    simp only [map_smul, smul_eq_mul,
      crossDifference_33_24_wPQGenerator] at h6
    simp [Fin.sum_univ_succ] at h2 h6
    let g : Fin 5 → F₂ := ![f 0, f 1, f 3, f 4, f 6]
    have hg := combination_mem_coeffTargetTwoSpan wPQBaseCoeff g
    change targetTwo c ∈ wPQTargetBase
    rw [← hf]
    simpa [wPQTargetBase, g, wPQBaseCoeff, wPQGenerator, h2, h6,
      Fin.sum_univ_succ] using hg
  · change coeffTargetTwoSpan wPQBaseCoeff ≤
      targetTwoSpace ⊓ wPQTwoSpace
    exact le_inf
      (coeffTargetTwoSpan_le_targetTwoSpace wPQBaseCoeff)
      wPQTargetBase_le

theorem wPQ_target_intersection_finrank :
    Module.finrank F₂ ↑(targetTwoSpace ⊓ wPQTwoSpace) = 5 := by
  rw [targetTwoSpace_inf_wPQTwoSpace, wPQTargetBase_finrank]

/-! ## One rational place of length three -/

theorem targetTwoSpace_inf_wThreePTwoSpace :
    targetTwoSpace ⊓ wThreePTwoSpace = wThreePTargetBase := by
  apply le_antisymm
  · rintro q ⟨⟨c, rfl⟩, hq⟩
    rw [wThreePTwoSpace] at hq
    rcases (Submodule.mem_span_range_iff_exists_fun
        (R := F₂) (v := wThreePGenerator)
        (x := targetTwo c)).mp hq with ⟨f, hf⟩
    have h2 := congrArg (crossDifference 1 1 0 2) hf
    have h4 := congrArg (crossDifference 2 2 0 4) hf
    rw [map_sum, crossDifference_11_02_target] at h2
    rw [map_sum, crossDifference_22_04_target] at h4
    simp only [map_smul, smul_eq_mul,
      crossDifference_11_02_wThreePGenerator] at h2
    simp only [map_smul, smul_eq_mul,
      crossDifference_22_04_wThreePGenerator] at h4
    simp [Fin.sum_univ_succ] at h2 h4
    let g : Fin 5 → F₂ := ![f 0, f 1, f 2, f 5, f 6]
    have hg := combination_mem_coeffTargetTwoSpan wThreePBaseCoeff g
    change targetTwo c ∈ wThreePTargetBase
    rw [← hf]
    simpa [wThreePTargetBase, g, wThreePBaseCoeff, wThreePGenerator,
      wThreePSecondJet, h2, h4, Fin.sum_univ_succ] using hg
  · change coeffTargetTwoSpan wThreePBaseCoeff ≤
      targetTwoSpace ⊓ wThreePTwoSpace
    exact le_inf
      (coeffTargetTwoSpan_le_targetTwoSpace wThreePBaseCoeff)
      wThreePTargetBase_le

theorem wThreeP_target_intersection_finrank :
    Module.finrank F₂ ↑(targetTwoSpace ⊓ wThreePTwoSpace) = 5 := by
  rw [targetTwoSpace_inf_wThreePTwoSpace, wThreePTargetBase_finrank]

/-! ## Exact envelope dimensions -/

theorem wStarGenerator_linearIndependent :
    LinearIndependent F₂ wStarGenerator := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h01 := congrArg (crossDifference 0 1 1 0) hf
  have h02 := congrArg (crossDifference 0 2 1 1) hf
  rw [map_sum, map_zero] at h01 h02
  simp only [map_smul, smul_eq_mul,
    crossDifference_01_10_wStarGenerator] at h01
  simp only [map_smul, smul_eq_mul,
    crossDifference_02_11_wStarGenerator] at h02
  simp [Fin.sum_univ_succ] at h01 h02
  have hf2eq : f 2 = f 1 := (CharTwo.add_eq_zero.mp h01).symm
  have hf3eq : f 3 = f 0 + f 1 := by
    have h02' : (f 0 + f 1) + f 3 = 0 := by
      simpa [add_assoc] using h02
    exact (CharTwo.add_eq_zero.mp h02').symm
  let g : Fin 5 → F₂ := ![f 4, f 5, f 6, f 0, f 1]
  have heq :
      ∑ k, f k • wStarGenerator k =
        ∑ k, g k • targetTwo (wStarBaseCoeff k) := by
    simp [g, wStarBaseCoeff, wStarGenerator, Fin.sum_univ_succ,
      targetTwo_outside8_eq, targetTwo_outside7_eq, hf2eq, hf3eq,
      smul_add]
    module
  have hbase : ∑ k, g k • targetTwo (wStarBaseCoeff k) = 0 := by
    rw [← heq, hf]
  have hg := Fintype.linearIndependent_iff.mp
    (coeffTargetTwo_linearIndependent wStarBaseCoeff
      wStarBaseCoeff_linearIndependent) g hbase
  have hf0 : f 0 = 0 := by simpa [g] using hg (3 : Fin 5)
  have hf1 : f 1 = 0 := by simpa [g] using hg (4 : Fin 5)
  have hf2 : f 2 = 0 := hf2eq.trans hf1
  have hf3 : f 3 = 0 := by simpa [hf0, hf1] using hf3eq
  have hf4 : f 4 = 0 := by simpa [g] using hg (0 : Fin 5)
  have hf5 : f 5 = 0 := by simpa [g] using hg (1 : Fin 5)
  have hf6 : f 6 = 0 := by simpa [g] using hg (2 : Fin 5)
  fin_cases i <;> assumption

theorem wStarTwoSpace_finrank :
    Module.finrank F₂ wStarTwoSpace = 7 := by
  rw [wStarTwoSpace, finrank_span_eq_card wStarGenerator_linearIndependent]
  rfl

theorem wStar_quotient_dimension :
    Module.finrank F₂ wStarTwoSpace -
      Module.finrank F₂ wStarTargetBase = 2 := by
  rw [wStarTwoSpace_finrank, wStarTargetBase_finrank]

theorem wPQGenerator_linearIndependent :
    LinearIndependent F₂ wPQGenerator := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h2 := congrArg (crossDifference 1 1 0 2) hf
  have h6 := congrArg (crossDifference 3 3 2 4) hf
  rw [map_sum, map_zero] at h2 h6
  simp only [map_smul, smul_eq_mul,
    crossDifference_11_02_wPQGenerator] at h2
  simp only [map_smul, smul_eq_mul,
    crossDifference_33_24_wPQGenerator] at h6
  simp [Fin.sum_univ_succ] at h2 h6
  let g : Fin 5 → F₂ := ![f 0, f 1, f 3, f 4, f 6]
  have hbase : ∑ k, g k • targetTwo (wPQBaseCoeff k) = 0 := by
    simpa [g, wPQBaseCoeff, wPQGenerator, h2, h6,
      Fin.sum_univ_succ] using hf
  have hg := Fintype.linearIndependent_iff.mp
    (coeffTargetTwo_linearIndependent wPQBaseCoeff
      wPQBaseCoeff_linearIndependent) g hbase
  have hf0 : f 0 = 0 := by simpa [g] using hg (0 : Fin 5)
  have hf1 : f 1 = 0 := by simpa [g] using hg (1 : Fin 5)
  have hf3 : f 3 = 0 := by simpa [g] using hg (2 : Fin 5)
  have hf4 : f 4 = 0 := by simpa [g] using hg (3 : Fin 5)
  have hf6 : f 6 = 0 := by simpa [g] using hg (4 : Fin 5)
  fin_cases i <;> assumption

theorem wPQTwoSpace_finrank :
    Module.finrank F₂ wPQTwoSpace = 7 := by
  rw [wPQTwoSpace, finrank_span_eq_card wPQGenerator_linearIndependent]
  rfl

theorem wPQ_quotient_dimension :
    Module.finrank F₂ wPQTwoSpace -
      Module.finrank F₂ wPQTargetBase = 2 := by
  rw [wPQTwoSpace_finrank, wPQTargetBase_finrank]

theorem wThreePGenerator_linearIndependent :
    LinearIndependent F₂ wThreePGenerator := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h2 := congrArg (crossDifference 1 1 0 2) hf
  have h4 := congrArg (crossDifference 2 2 0 4) hf
  rw [map_sum, map_zero] at h2 h4
  simp only [map_smul, smul_eq_mul,
    crossDifference_11_02_wThreePGenerator] at h2
  simp only [map_smul, smul_eq_mul,
    crossDifference_22_04_wThreePGenerator] at h4
  simp [Fin.sum_univ_succ] at h2 h4
  let g : Fin 5 → F₂ := ![f 0, f 1, f 2, f 5, f 6]
  have hbase : ∑ k, g k • targetTwo (wThreePBaseCoeff k) = 0 := by
    simpa [g, wThreePBaseCoeff, wThreePGenerator, wThreePSecondJet,
      h2, h4, Fin.sum_univ_succ] using hf
  have hg := Fintype.linearIndependent_iff.mp
    (coeffTargetTwo_linearIndependent wThreePBaseCoeff
      wThreePBaseCoeff_linearIndependent) g hbase
  have hf0 : f 0 = 0 := by simpa [g] using hg (0 : Fin 5)
  have hf1 : f 1 = 0 := by simpa [g] using hg (1 : Fin 5)
  have hf2 : f 2 = 0 := by simpa [g] using hg (2 : Fin 5)
  have hf5 : f 5 = 0 := by simpa [g] using hg (3 : Fin 5)
  have hf6 : f 6 = 0 := by simpa [g] using hg (4 : Fin 5)
  fin_cases i <;> assumption

theorem wThreePTwoSpace_finrank :
    Module.finrank F₂ wThreePTwoSpace = 7 := by
  rw [wThreePTwoSpace,
    finrank_span_eq_card wThreePGenerator_linearIndependent]
  rfl

theorem wThreeP_quotient_dimension :
    Module.finrank F₂ wThreePTwoSpace -
      Module.finrank F₂ wThreePTargetBase = 2 := by
  rw [wThreePTwoSpace_finrank, wThreePTargetBase_finrank]

end
end E2
end N5
end UnrestrictedBooleanMul
