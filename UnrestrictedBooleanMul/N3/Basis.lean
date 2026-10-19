module

public import UnrestrictedBooleanMul.N3Certificate
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace UnrestrictedBooleanMul

open N3Certificate

noncomputable section

def targetSum : ANF 6 := ∑ i : Fin 5, UnrestrictedBooleanMul.Mul 3 i

def rationalBasis : Fin 10 → ANF 6 :=
  ![1, X 0, X 1, X 2, X 3, X 4, X 5,
    UnrestrictedBooleanMul.Mul 3 0, UnrestrictedBooleanMul.Mul 3 4, targetSum]

def ambientBasis : Fin 12 → ANF 6 :=
  ![1, X 0, X 1, X 2, X 3, X 4, X 5,
    UnrestrictedBooleanMul.Mul 3 0, UnrestrictedBooleanMul.Mul 3 1,
    UnrestrictedBooleanMul.Mul 3 2, UnrestrictedBooleanMul.Mul 3 3,
    UnrestrictedBooleanMul.Mul 3 4]

def rationalRep (c : Fin 10 → F₂) : ANF 6 := ∑ i, c i • rationalBasis i
def ambientRep (c : Fin 12 → F₂) : ANF 6 := ∑ i, c i • ambientBasis i

macro "solve_product_coeff" : tactic =>
  `(tactic|
    (simp [rationalRep, rationalBasis, targetSum, UnrestrictedBooleanMul.Mul,
      mulCoefficient, aVar, bVar, X, monomial_mul, Fin.sum_univ_succ,
      N3Certificate.c3, N3Certificate.c20, N3Certificate.c25,
      N3Certificate.c30, N3Certificate.c31, N3Certificate.c32,
      N3Certificate.c34, N3Certificate.g0, N3Certificate.g1,
      N3Certificate.ab]
     ring_nf
     simp +decide [monomial_mul, coeff_monomial]
     ring_nf
     all_goals simp only [N3Certificate.two_eq_zero_f2, mul_zero, add_zero, zero_add]))


end

end UnrestrictedBooleanMul
