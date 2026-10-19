module

public import UnrestrictedBooleanMul.N3.Basis

@[expose] public section

namespace UnrestrictedBooleanMul
open N3Certificate
noncomputable section

def rationalSpace : Submodule F₂ (ANF 6) :=
  Submodule.span F₂ (Set.range rationalBasis)

def ambientSpace : Submodule F₂ (ANF 6) :=
  Submodule.span F₂ (Set.range ambientBasis)

theorem mem_rationalSpace_iff {p : ANF 6} :
    p ∈ rationalSpace ↔ ∃ c : Fin 10 → F₂, rationalRep c = p := by
  simpa [rationalSpace, rationalRep] using
    (Submodule.mem_span_range_iff_exists_fun (R := F₂) (v := rationalBasis) (x := p))

theorem mem_ambientSpace_iff {p : ANF 6} :
    p ∈ ambientSpace ↔ ∃ c : Fin 12 → F₂, ambientRep c = p := by
  simpa [ambientSpace, ambientRep] using
    (Submodule.mem_span_range_iff_exists_fun (R := F₂) (v := ambientBasis) (x := p))

def ambientAnchor : Fin 12 → Monomial 6 :=
  ![⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{2}⟩, ⟨{3}⟩, ⟨{4}⟩, ⟨{5}⟩,
    ⟨{0, 3}⟩, ⟨{0, 4}⟩, ⟨{0, 5}⟩, ⟨{1, 5}⟩, ⟨{2, 5}⟩]

def ambientProjection : ANF 6 →ₗ[F₂] (Fin 12 → F₂) :=
  coefficientProjection ambientAnchor

set_option maxHeartbeats 1000000 in
theorem ambientProjection_basis (i : Fin 12) :
    ambientProjection (ambientBasis i) = (Pi.basisFun F₂ (Fin 12)) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [ambientProjection, coefficientProjection, ambientAnchor, ambientBasis,
      UnrestrictedBooleanMul.Mul, mulCoefficient, aVar, bVar, X, monomial_mul,
      Pi.basisFun, Fin.sum_univ_succ] <;> decide

@[simp] theorem ambientProjection_one :
    ambientProjection 1 = (Pi.basisFun F₂ (Fin 12)) 0 := by
  simpa [ambientBasis] using ambientProjection_basis 0

@[simp] theorem ambientProjection_X_zero :
    ambientProjection (X 0) = (Pi.basisFun F₂ (Fin 12)) 1 := by
  simpa [ambientBasis] using ambientProjection_basis 1

@[simp] theorem ambientProjection_X_one :
    ambientProjection (X 1) = (Pi.basisFun F₂ (Fin 12)) 2 := by
  simpa [ambientBasis] using ambientProjection_basis 2

@[simp] theorem ambientProjection_X_two :
    ambientProjection (X 2) = (Pi.basisFun F₂ (Fin 12)) 3 := by
  simpa [ambientBasis] using ambientProjection_basis 3

@[simp] theorem ambientProjection_X_three :
    ambientProjection (X 3) = (Pi.basisFun F₂ (Fin 12)) 4 := by
  simpa [ambientBasis] using ambientProjection_basis 4

@[simp] theorem ambientProjection_X_four :
    ambientProjection (X 4) = (Pi.basisFun F₂ (Fin 12)) 5 := by
  simpa [ambientBasis] using ambientProjection_basis 5

@[simp] theorem ambientProjection_X_five :
    ambientProjection (X 5) = (Pi.basisFun F₂ (Fin 12)) 6 := by
  simpa [ambientBasis] using ambientProjection_basis 6

@[simp] theorem ambientProjection_mul_zero :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 0) = (Pi.basisFun F₂ (Fin 12)) 7 := by
  simpa [ambientBasis] using ambientProjection_basis 7

@[simp] theorem ambientProjection_mul_one :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 1) = (Pi.basisFun F₂ (Fin 12)) 8 := by
  simpa [ambientBasis] using ambientProjection_basis 8

@[simp] theorem ambientProjection_mul_two :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 2) = (Pi.basisFun F₂ (Fin 12)) 9 := by
  simpa [ambientBasis] using ambientProjection_basis 9

@[simp] theorem ambientProjection_mul_three :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 3) = (Pi.basisFun F₂ (Fin 12)) 10 := by
  simpa [ambientBasis] using ambientProjection_basis 10

@[simp] theorem ambientProjection_mul_four :
    ambientProjection (UnrestrictedBooleanMul.Mul 3 4) = (Pi.basisFun F₂ (Fin 12)) 11 := by
  simpa [ambientBasis] using ambientProjection_basis 11


end

end UnrestrictedBooleanMul
