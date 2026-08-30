import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Boolean algebraic normal forms

A squarefree monomial is a finite set of input variables. Multiplication is
set union, so the resulting monoid algebra over `ZMod 2` is exactly the Boolean
ANF quotient in canonical normal form.
-/

namespace UnrestrictedBooleanMul

noncomputable section

abbrev F₂ := ZMod 2

/-- A squarefree monomial in `m` Boolean variables. -/
@[ext]
structure Monomial (m : Nat) where
  vars : Finset (Fin m)
deriving DecidableEq

namespace Monomial

def equivFinset {m : Nat} : Monomial m ≃ Finset (Fin m) where
  toFun := Monomial.vars
  invFun := Monomial.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance {m : Nat} : Fintype (Monomial m) :=
  Fintype.ofEquiv (Finset (Fin m)) equivFinset.symm

end Monomial

instance {m : Nat} : CommMonoid (Monomial m) where
  one := ⟨∅⟩
  mul s t := ⟨s.vars ∪ t.vars⟩
  one_mul s := by apply Monomial.ext; exact Finset.empty_union s.vars
  mul_one s := by apply Monomial.ext; exact Finset.union_empty s.vars
  mul_assoc r s t := by apply Monomial.ext; exact Finset.union_assoc r.vars s.vars t.vars
  mul_comm s t := by apply Monomial.ext; exact Finset.union_comm s.vars t.vars

@[simp]
theorem Monomial.one_vars {m : Nat} : (1 : Monomial m).vars = ∅ := rfl

@[simp]
theorem Monomial.mul_vars {m : Nat} (s t : Monomial m) : (s * t).vars = s.vars ∪ t.vars := rfl

@[simp]
theorem Monomial.singleton_mul_singleton {m : Nat} (i j : Fin m) :
    (⟨{i}⟩ : Monomial m) * ⟨{j}⟩ = ⟨{i, j}⟩ := by
  apply Monomial.ext
  simp

/-- Canonical Boolean algebraic normal forms in `m` variables. -/
abbrev ANF (m : Nat) := MonoidAlgebra F₂ (Monomial m)

/-- The ANF consisting of one squarefree monomial. -/
def monomial {m : Nat} (s : Finset (Fin m)) : ANF m :=
  MonoidAlgebra.single ⟨s⟩ 1

@[simp]
theorem coeff_monomial {m : Nat} (s t : Finset (Fin m)) :
    (monomial s : ANF m).coeff ⟨t⟩ = if s = t then 1 else 0 := by
  rw [monomial]
  change (Finsupp.single (⟨s⟩ : Monomial m) (1 : F₂)) (⟨t⟩ : Monomial m) =
    if s = t then 1 else 0
  rw [Finsupp.single_apply]
  simp only [Monomial.mk.injEq]

/-- The `i`th input variable. -/
def X {m : Nat} (i : Fin m) : ANF m := monomial {i}

@[simp]
theorem monomial_mul {m : Nat} (s t : Finset (Fin m)) :
    monomial s * monomial t = monomial (s ∪ t) := by
  rw [monomial, monomial, MonoidAlgebra.single_mul_single]
  change MonoidAlgebra.single (⟨s ∪ t⟩ : Monomial m) (1 * 1) =
    MonoidAlgebra.single (⟨s ∪ t⟩ : Monomial m) 1
  rw [one_mul]

@[simp]
theorem X_mul_self {m : Nat} (i : Fin m) : X i * X i = X i := by
  simp [X]

@[simp]
theorem anf_add_self {m : Nat} (p : ANF m) : p + p = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext s
  exact CharTwo.add_self_eq_zero (p.coeff s)

@[simp]
theorem anf_two_eq_zero {m : Nat} : (2 : ANF m) = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext s
  simp [CharTwo.two_eq_zero]

@[simp]
theorem anf_four_eq_zero {m : Nat} : (4 : ANF m) = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext s
  simp [CharTwo.ofNat_eq_mod]

/-- Evaluation of a canonical ANF on a Boolean input. -/
def eval {m : Nat} (p : ANF m) (x : Fin m → F₂) : F₂ :=
  p.coeff.sum fun s c => c * ∏ i ∈ s.vars, x i

@[simp]
theorem eval_monomial {m : Nat} (s : Finset (Fin m)) (x : Fin m → F₂) :
    eval (monomial s) x = ∏ i ∈ s, x i := by
  simp [eval, monomial]

@[simp]
theorem eval_X {m : Nat} (i : Fin m) (x : Fin m → F₂) : eval (X i) x = x i := by
  simp [X]

/-- The subspace of constants and input-linear functions. -/
noncomputable def affine (m : Nat) : Submodule F₂ (ANF m) :=
  Submodule.span F₂ ({1} ∪ Set.range X)

theorem one_mem_affine (m : Nat) : (1 : ANF m) ∈ affine m := by
  apply Submodule.subset_span
  exact Set.mem_union_left _ (Set.mem_singleton 1)

theorem X_mem_affine {m : Nat} (i : Fin m) : X i ∈ affine m := by
  apply Submodule.subset_span
  exact Set.mem_union_right _ ⟨i, rfl⟩

end

end UnrestrictedBooleanMul
