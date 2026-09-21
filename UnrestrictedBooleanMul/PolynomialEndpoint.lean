import UnrestrictedBooleanMul.BilinearRestriction
import UnrestrictedBooleanMul.BilinearOutput

/-! The a₀=0 restriction of the square six-term polynomial product is
exactly the rectangular product with an extra zero output. -/
namespace UnrestrictedBooleanMul
noncomputable section

def firstCoordinateNormal (a : Nat) : Fin (a + 1) → F₂ :=
  fun i => if i = 0 then 1 else 0

theorem firstCoordinateNormal_pivot (a : Nat) : firstCoordinateNormal a 0 = 1 := by
  simp [firstCoordinateNormal]

theorem firstCoordinateMatrix {a : Nat} (i : Fin (a + 1)) (u : Fin a) :
    leftHyperplaneMatrix (firstCoordinateNormal a) 0 i u = if i = u.succ then 1 else 0 := by
  unfold leftHyperplaneMatrix
  by_cases hi : i = 0
  · subst i
    rw [if_pos rfl]
    unfold firstCoordinateNormal
    rw [if_neg (Fin.succAbove_ne 0 u), if_neg (Fin.succ_ne_zero u).symm]
  · rw [if_neg hi]
    exact congrArg (fun v : Fin (a + 1) => if i = v then (1 : F₂) else 0)
      (Fin.zero_succAbove u)

namespace N6

def endpointTensor : BilinearTensor 5 6 11 :=
  (polynomialTensor 6 6).restrictLeft (leftHyperplaneMatrix (firstCoordinateNormal 5) 0)

theorem endpointTensor_coefficient (s : Fin 11) (i : Fin 5) (j : Fin 6) :
    endpointTensor s i j = if i.val + 1 + j.val = s.val then 1 else 0 := by
  simp only [endpointTensor, BilinearTensor.restrictLeft, firstCoordinateMatrix,
    ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

theorem endpointTensor_eq_padded_rectangle :
    endpointTensor = (polynomialTensor 5 6).prependZero := by
  funext s i j
  refine Fin.cases ?_ (fun t => ?_) s
  · rw [endpointTensor_coefficient]
    simp [BilinearTensor.prependZero]
  · rw [endpointTensor_coefficient]
    change (if i.val + 1 + j.val = t.val + 1 then (1 : F₂) else 0) =
      (if i.val + j.val = t.val then 1 else 0)
    have hindex : i.val + 1 + j.val = t.val + 1 ↔ i.val + j.val = t.val := by omega
    simp only [hindex]

theorem bilinearRank_endpoint : bilinearRank endpointTensor = bilinearRank (polynomialTensor 5 6) := by
  rw [endpointTensor_eq_padded_rectangle, bilinearRank_prependZero]

def rectangleFormula_of_endpoint {r : Nat} (F : BilinearFormula endpointTensor r) :
    BilinearFormula (polynomialTensor 5 6) r := by
  have F' : BilinearFormula (polynomialTensor 5 6).prependZero r :=
    endpointTensor_eq_padded_rectangle ▸ F
  simpa only [BilinearTensor.prependZero_select_succ] using F'.selectOutputs Fin.succ

def endpointFormula_of_rectangle {r : Nat} (F : BilinearFormula (polynomialTensor 5 6) r) :
    BilinearFormula endpointTensor r := by
  rw [endpointTensor_eq_padded_rectangle]
  exact F.prependZero

theorem hasBilinearFormula_endpoint_iff (r : Nat) :
    HasBilinearFormula endpointTensor r ↔ HasBilinearFormula (polynomialTensor 5 6) r :=
  ⟨fun ⟨F⟩ => ⟨rectangleFormula_of_endpoint F⟩, fun ⟨F⟩ => ⟨endpointFormula_of_rectangle F⟩⟩

/-- Restriction costs no additional products and padding loses no outputs.
This is rank equality, not a claimed rectangular lower bound. -/
theorem bilinearRank_rational_endpoint (p : Fin 6) (hp : firstCoordinateNormal 5 p = 1) :
    bilinearRank ((polynomialTensor 6 6).restrictLeft
      (leftHyperplaneMatrix (firstCoordinateNormal 5) p)) =
        bilinearRank (polynomialTensor 5 6) := by
  rw [bilinearRank_hyperplane_pivot_eq _ _ p 0 hp (firstCoordinateNormal_pivot 5)]
  exact bilinearRank_endpoint

end N6
#check firstCoordinateNormal_pivot
#check firstCoordinateMatrix
#check N6.endpointTensor_coefficient
#check N6.endpointTensor_eq_padded_rectangle
#check N6.bilinearRank_endpoint
#check N6.rectangleFormula_of_endpoint
#check N6.endpointFormula_of_rectangle
#check N6.hasBilinearFormula_endpoint_iff
#check N6.bilinearRank_rational_endpoint
#print axioms firstCoordinateNormal_pivot
#print axioms firstCoordinateMatrix
#print axioms N6.endpointTensor_coefficient
#print axioms N6.endpointTensor_eq_padded_rectangle
#print axioms N6.bilinearRank_endpoint
#print axioms N6.rectangleFormula_of_endpoint
#print axioms N6.endpointFormula_of_rectangle
#print axioms N6.hasBilinearFormula_endpoint_iff
#print axioms N6.bilinearRank_rational_endpoint
end
end UnrestrictedBooleanMul
