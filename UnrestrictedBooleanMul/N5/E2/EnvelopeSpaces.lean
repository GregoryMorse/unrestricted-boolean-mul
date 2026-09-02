import UnrestrictedBooleanMul.N5.E2.LowSetGeometry
import UnrestrictedBooleanMul.N5.Displacement

/-!
# Concrete maximal two-defect envelope spaces

This file places the three coordinate models from Section 10 inside the
existing 45-dimensional quadratic space.  It defines the displayed seven
generators and their five-dimensional target bases and proves the elementary
dimension and containment facts needed by the envelope/suffix interface.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

noncomputable section

def coeffTargetTwoSpan {n : Nat} (v : Fin n → TargetCoeff) :
    Submodule F₂ TwoForm :=
  Submodule.span F₂ (Set.range fun i => targetTwo (v i))

theorem coeffTargetTwo_linearIndependent {n : Nat} (v : Fin n → TargetCoeff)
    (hv : LinearIndependent F₂ v) :
    LinearIndependent F₂ (fun i => targetTwo (v i)) := by
  exact hv.map' targetTwoLinear
    (LinearMap.ker_eq_bot_of_injective targetTwo_injective)

theorem coeffTargetTwoSpan_finrank {n : Nat} (v : Fin n → TargetCoeff)
    (hv : LinearIndependent F₂ v) :
    Module.finrank F₂ (coeffTargetTwoSpan v) = n := by
  have hmap := coeffTargetTwo_linearIndependent v hv
  change Module.finrank F₂
      (Submodule.span F₂ (Set.range fun i => targetTwo (v i))) = n
  exact (finrank_span_eq_card hmap).trans (Fintype.card_fin n)

theorem envelopeSpan_finrank_le {n : Nat} (v : Fin n → TwoForm) :
    Module.finrank F₂ (Submodule.span F₂ (Set.range v)) ≤ n := by
  letI : Fintype (Set.range v) := Fintype.ofFinite _
  exact (finrank_span_le_card (Set.range v)).trans (by
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le v)

private theorem generator_mem_span {n : Nat} (v : Fin n → TwoForm)
    (i : Fin n) : v i ∈ Submodule.span F₂ (Set.range v) :=
  Submodule.subset_span ⟨i, rfl⟩

/-! ## Degree-two place -/

def wStarX00 : TwoForm := squarefreeWedge aStarZero bStarZero
def wStarX01 : TwoForm := squarefreeWedge aStarZero bStarOne
def wStarX10 : TwoForm := squarefreeWedge aStarOne bStarZero
def wStarX11 : TwoForm := squarefreeWedge aStarOne bStarOne

def wStarGenerator : Fin 7 → TwoForm :=
  ![wStarX00, wStarX01, wStarX10, wStarX11,
    targetTwo rZeroCoeff, targetTwo rOneCoeff, targetTwo rInfinityCoeff]

def wStarTwoSpace : Submodule F₂ TwoForm :=
  Submodule.span F₂ (Set.range wStarGenerator)

def wStarBaseCoeff : Fin 5 → TargetCoeff :=
  ![rZeroCoeff, rOneCoeff, rInfinityCoeff,
    outsideHankelWord 8, outsideHankelWord 7]

def wStarTargetBase : Submodule F₂ TwoForm :=
  coeffTargetTwoSpan wStarBaseCoeff

theorem wStarBaseCoeff_linearIndependent :
    LinearIndependent F₂ wStarBaseCoeff := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h0 := congrFun hf (0 : Fin 9)
  have h2 := congrFun hf (2 : Fin 9)
  have h3 := congrFun hf (3 : Fin 9)
  have h7 := congrFun hf (7 : Fin 9)
  have h8 := congrFun hf (8 : Fin 9)
  simp [wStarBaseCoeff, outsideHankelWord, rankTwoHankelWord,
    rZeroCoeff, rOneCoeff, rInfinityCoeff, dStarZeroCoeff,
    dStarOneCoeff, Fin.sum_univ_succ] at h0 h2 h3 h7 h8
  have h3' : f 1 + f 3 = 0 := by
    simpa [CharTwo.add_self_eq_zero] using h3
  have hf3eq : f 3 = f 1 := (CharTwo.add_eq_zero.mp h3').symm
  have hf4eq : f 4 = f 1 := (CharTwo.add_eq_zero.mp h7).symm
  have hf1 : f 1 = 0 := by
    simpa [hf3eq, hf4eq, CharTwo.add_self_eq_zero] using h2
  have hf3 : f 3 = 0 := hf3eq.trans hf1
  have hf4 : f 4 = 0 := hf4eq.trans hf1
  have hf2 : f 2 = 0 := by simpa [hf1, hf3, hf4] using h8
  have hf0 : f 0 = 0 := by
    simpa [hf1, hf3, hf4, CharTwo.add_self_eq_zero] using h0
  fin_cases i <;> assumption

theorem wStarTargetBase_finrank :
    Module.finrank F₂ wStarTargetBase = 5 :=
  coeffTargetTwoSpan_finrank wStarBaseCoeff
    wStarBaseCoeff_linearIndependent

theorem wStarTwoSpace_finrank_le_seven :
    Module.finrank F₂ wStarTwoSpace ≤ 7 :=
  envelopeSpan_finrank_le wStarGenerator

theorem targetTwo_outside8_eq :
    targetTwo (outsideHankelWord 8) = wStarX00 + wStarX11 := by
  rw [targetTwo_outsideHankelWord]
  simp [outsideHankelPlace, outsideHankelLocalCoord, localTwoForm,
    localKleinPair, closedPlaceLocalBasis, wStarX00, wStarX11,
    Fin.sum_univ_succ]

theorem targetTwo_outside7_eq :
    targetTwo (outsideHankelWord 7) =
      wStarX01 + wStarX10 + wStarX11 := by
  rw [targetTwo_outsideHankelWord]
  simp [outsideHankelPlace, outsideHankelLocalCoord, localTwoForm,
    localKleinPair, closedPlaceLocalBasis, wStarX01, wStarX10,
    wStarX11, Fin.sum_univ_succ, add_assoc]

theorem wStarTargetBase_le : wStarTargetBase ≤ wStarTwoSpace := by
  rw [wStarTargetBase, coeffTargetTwoSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hgen (k : Fin 7) : wStarGenerator k ∈ wStarTwoSpace := by
    rw [wStarTwoSpace]
    exact generator_mem_span wStarGenerator k
  fin_cases i
  · change targetTwo rZeroCoeff ∈ wStarTwoSpace
    simpa [wStarGenerator] using hgen (4 : Fin 7)
  · change targetTwo rOneCoeff ∈ wStarTwoSpace
    simpa [wStarGenerator] using hgen (5 : Fin 7)
  · change targetTwo rInfinityCoeff ∈ wStarTwoSpace
    simpa [wStarGenerator] using hgen (6 : Fin 7)
  · change targetTwo (outsideHankelWord 8) ∈ wStarTwoSpace
    rw [targetTwo_outside8_eq]
    exact Submodule.add_mem _
      (by simpa [wStarGenerator] using hgen (0 : Fin 7))
      (by simpa [wStarGenerator] using hgen (3 : Fin 7))
  · change targetTwo (outsideHankelWord 7) ∈ wStarTwoSpace
    rw [targetTwo_outside7_eq]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (by simpa [wStarGenerator] using hgen (1 : Fin 7))
        (by simpa [wStarGenerator] using hgen (2 : Fin 7)))
      (by simpa [wStarGenerator] using hgen (3 : Fin 7))

theorem wStar_quotient_dimension_le_two :
    Module.finrank F₂ wStarTwoSpace -
      Module.finrank F₂ wStarTargetBase ≤ 2 := by
  rw [wStarTargetBase_finrank]
  have h := wStarTwoSpace_finrank_le_seven
  omega

/-! ## Two distinct rational places -/

def wPQZZero : TwoForm := squarefreeWedge (aLinear 1) (bLinear 1)
def wPQZInfinity : TwoForm := squarefreeWedge (aLinear 3) (bLinear 3)

def wPQGenerator : Fin 7 → TwoForm :=
  ![targetTwo rZeroCoeff, targetTwo jZeroCoeff, wPQZZero,
    targetTwo rInfinityCoeff, targetTwo jInfinityCoeff, wPQZInfinity,
    targetTwo rOneCoeff]

def wPQTwoSpace : Submodule F₂ TwoForm :=
  Submodule.span F₂ (Set.range wPQGenerator)

def wPQBaseCoeff : Fin 5 → TargetCoeff :=
  ![rZeroCoeff, jZeroCoeff, rInfinityCoeff, jInfinityCoeff, rOneCoeff]

def wPQTargetBase : Submodule F₂ TwoForm :=
  coeffTargetTwoSpan wPQBaseCoeff

theorem wPQBaseCoeff_linearIndependent :
    LinearIndependent F₂ wPQBaseCoeff := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h0 := congrFun hf (0 : Fin 9)
  have h1 := congrFun hf (1 : Fin 9)
  have h2 := congrFun hf (2 : Fin 9)
  have h7 := congrFun hf (7 : Fin 9)
  have h8 := congrFun hf (8 : Fin 9)
  simp [wPQBaseCoeff, rZeroCoeff, jZeroCoeff, rInfinityCoeff,
    jInfinityCoeff, rOneCoeff, Fin.sum_univ_succ] at h0 h1 h2 h7 h8
  have hf4 : f 4 = 0 := h7
  have hf0 : f 0 = 0 := by simpa [hf4] using h0
  have hf2 : f 2 = 0 := by simpa [hf4] using h8
  have hf3 : f 3 = 0 := by simpa [hf4] using h2
  have hf1 : f 1 = 0 := by simpa [hf3, hf4] using h1
  fin_cases i <;> assumption

theorem wPQTargetBase_finrank :
    Module.finrank F₂ wPQTargetBase = 5 :=
  coeffTargetTwoSpan_finrank wPQBaseCoeff wPQBaseCoeff_linearIndependent

theorem wPQTwoSpace_finrank_le_seven :
    Module.finrank F₂ wPQTwoSpace ≤ 7 :=
  envelopeSpan_finrank_le wPQGenerator

theorem wPQTargetBase_le : wPQTargetBase ≤ wPQTwoSpace := by
  rw [wPQTargetBase, coeffTargetTwoSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact generator_mem_span wPQGenerator 0
  · exact generator_mem_span wPQGenerator 1
  · exact generator_mem_span wPQGenerator 3
  · exact generator_mem_span wPQGenerator 4
  · exact generator_mem_span wPQGenerator 6

theorem wPQ_quotient_dimension_le_two :
    Module.finrank F₂ wPQTwoSpace -
      Module.finrank F₂ wPQTargetBase ≤ 2 := by
  rw [wPQTargetBase_finrank]
  have h := wPQTwoSpace_finrank_le_seven
  omega

/-! ## One rational place of length three -/

def wThreePSecondJet : TwoForm := targetTwo (targetBasis 2)
def wThreePUOne : TwoForm := squarefreeWedge (aLinear 1) (bLinear 1)
def wThreePUTwo : TwoForm := squarefreeWedge (aLinear 2) (bLinear 2)

def wThreePGenerator : Fin 7 → TwoForm :=
  ![targetTwo rZeroCoeff, targetTwo jZeroCoeff, wThreePSecondJet,
    wThreePUOne, wThreePUTwo, targetTwo rOneCoeff,
    targetTwo rInfinityCoeff]

def wThreePTwoSpace : Submodule F₂ TwoForm :=
  Submodule.span F₂ (Set.range wThreePGenerator)

def wThreePBaseCoeff : Fin 5 → TargetCoeff :=
  ![rZeroCoeff, jZeroCoeff, targetBasis 2, rOneCoeff, rInfinityCoeff]

def wThreePTargetBase : Submodule F₂ TwoForm :=
  coeffTargetTwoSpan wThreePBaseCoeff

theorem wThreePBaseCoeff_linearIndependent :
    LinearIndependent F₂ wThreePBaseCoeff := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h0 := congrFun hf (0 : Fin 9)
  have h1 := congrFun hf (1 : Fin 9)
  have h2 := congrFun hf (2 : Fin 9)
  have h3 := congrFun hf (3 : Fin 9)
  have h8 := congrFun hf (8 : Fin 9)
  simp [wThreePBaseCoeff, rZeroCoeff, jZeroCoeff, rOneCoeff,
    rInfinityCoeff, targetBasis, Pi.basisFun,
    Fin.sum_univ_succ] at h0 h1 h2 h3 h8
  have hf3 : f 3 = 0 := h3
  have hf4 : f 4 = 0 := by simpa [hf3] using h8
  have hf2 : f 2 = 0 := by simpa [hf3] using h2
  have hf1 : f 1 = 0 := by simpa [hf3] using h1
  have hf0 : f 0 = 0 := by simpa [hf3] using h0
  fin_cases i <;> assumption

theorem wThreePTargetBase_finrank :
    Module.finrank F₂ wThreePTargetBase = 5 :=
  coeffTargetTwoSpan_finrank wThreePBaseCoeff
    wThreePBaseCoeff_linearIndependent

theorem wThreePTwoSpace_finrank_le_seven :
    Module.finrank F₂ wThreePTwoSpace ≤ 7 :=
  envelopeSpan_finrank_le wThreePGenerator

theorem wThreePTargetBase_le : wThreePTargetBase ≤ wThreePTwoSpace := by
  rw [wThreePTargetBase, coeffTargetTwoSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact generator_mem_span wThreePGenerator 0
  · exact generator_mem_span wThreePGenerator 1
  · exact generator_mem_span wThreePGenerator 2
  · exact generator_mem_span wThreePGenerator 5
  · exact generator_mem_span wThreePGenerator 6

theorem wThreeP_quotient_dimension_le_two :
    Module.finrank F₂ wThreePTwoSpace -
      Module.finrank F₂ wThreePTargetBase ≤ 2 := by
  rw [wThreePTargetBase_finrank]
  have h := wThreePTwoSpace_finrank_le_seven
  omega

end
end E2
end N5
end UnrestrictedBooleanMul
