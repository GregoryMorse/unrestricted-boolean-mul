import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

/-!
# Unrestricted Boolean polynomial multiplication through four terms

Statement of record for arXiv:2608.30238v1, Definition 2.1,
Propositions 2.3 and 2.4, and Theorem 9.1.

Coefficients are in F₂. Squarefree monomials multiply by union, imposing
Boolean idempotence. XOR and constants are free; either input of each paid
AND gate may use arbitrary previously computed nonlinear wires. This is
not a restriction to bilinear, quadratic, homogeneous or formula circuits.

The definitions below reproduce the intended proof-development definitions.
Comparator compares the six declarations with their existing proofs imported
by Solution.lean. Only the six theorem proofs here are deliberate holes.
For n=0, natural subtraction gives zero outputs. The fallback value zero in
the definition of complexity is irrelevant to these computable targets.
No claim about n=5, n=6 or the general Boyar--Find question is submitted.
-/

namespace UnrestrictedBooleanMul
noncomputable section

/-- The coefficient field with two elements. -/
abbrev F₂ := ZMod 2

/-- A squarefree monomial is the finite set of variables it contains. -/
@[ext]
structure Monomial (m : Nat) where
  vars : Finset (Fin m)
deriving DecidableEq

instance {m : Nat} : CommMonoid (Monomial m) where
  one := ⟨∅⟩
  mul s t := ⟨s.vars ∪ t.vars⟩
  one_mul s := by apply Monomial.ext; exact Finset.empty_union s.vars
  mul_one s := by apply Monomial.ext; exact Finset.union_empty s.vars
  mul_assoc r s t := by apply Monomial.ext; exact Finset.union_assoc r.vars s.vars t.vars
  mul_comm s t := by apply Monomial.ext; exact Finset.union_comm s.vars t.vars

/-- Boolean algebraic normal forms, with monomials multiplied by union. -/
abbrev ANF (m : Nat) := MonoidAlgebra F₂ (Monomial m)

/-- The ANF of a single squarefree monomial. -/
def monomial {m : Nat} (s : Finset (Fin m)) : ANF m :=
  MonoidAlgebra.single ⟨s⟩ 1

/-- The i-th original input variable. -/
def X {m : Nat} (i : Fin m) : ANF m := monomial {i}

/-- Free affine functions: constants and linear combinations of inputs. -/
noncomputable def affine (m : Nat) : Submodule F₂ (ANF m) :=
  Submodule.span F₂ ({1} ∪ Set.range X)

/-- Paid outputs strictly before a given gate index. -/
def prefixGates {m r : Nat} (g : Fin r → ANF m) (j : Nat) : Set (ANF m) :=
  {p | ∃ i : Fin r, i.val < j ∧ g i = p}

/-- All functions available before gate j, including earlier nonlinear outputs. -/
def wireSpace {m r : Nat} (g : Fin r → ANF m) (j : Nat) : Submodule F₂ (ANF m) :=
  affine m ⊔ Submodule.span F₂ (prefixGates g j)

/-- An unrestricted XOR--AND circuit with m inputs and exactly r AND gates. -/
structure Circuit (m r : Nat) where
  gate : Fin r → ANF m
  left : Fin r → ANF m
  right : Fin r → ANF m
  left_mem : ∀ j, left j ∈ wireSpace gate j.val
  right_mem : ∀ j, right j ∈ wireSpace gate j.val
  gate_eq : ∀ j, gate j = left j * right j

/-- Available outputs after every paid gate has been evaluated. -/
def Circuit.finalWire {m r : Nat} (C : Circuit m r) : Submodule F₂ (ANF m) :=
  wireSpace C.gate r

/-- Each target output is a free affine/XOR combination of available wires. -/
def Circuit.Computes {m r o : Nat} (C : Circuit m r) (target : Fin o → ANF m) : Prop :=
  ∀ i, target i ∈ C.finalWire

/-- Existence of a circuit with exactly r paid AND gates for the target. -/
def HasCircuit {m o : Nat} (target : Fin o → ANF m) (r : Nat) : Prop :=
  Nonempty {C : Circuit m r // C.Computes target}

/-- Minimum AND count if a circuit exists, with zero as the unused fallback. -/
def multiplicativeComplexity {m o : Nat} (target : Fin o → ANF m) : Nat :=
  by
    classical
    exact if h : ∃ r, HasCircuit target r then Nat.find h else 0

notation "MC(" target ")" => multiplicativeComplexity target

/-- Coefficient a_i in the first input polynomial. -/
def aVar (n : Nat) (i : Fin n) : ANF (2 * n) := X ⟨i.val, by omega⟩

/-- Coefficient b_j in the second input polynomial. -/
def bVar (n : Nat) (j : Fin n) : ANF (2 * n) := X ⟨n + j.val, by omega⟩

/-- Coefficient s of the ordinary polynomial product, not integer multiplication. -/
def mulCoefficient (n : Nat) (s : Nat) : ANF (2 * n) :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i.val + j.val = s then aVar n i * bVar n j else 0

/-- All 2n-1 product coefficients, with no outputs in the n=0 convention. -/
def Mul (n : Nat) : Fin (2 * n - 1) → ANF (2 * n) :=
  fun s => mulCoefficient n s.val

/-- Empty-input convention, Proposition 2.3. -/
theorem mc_mul_zero : MC(Mul 0) = 0 := by sorry

/-- One product is necessary and sufficient, Proposition 2.3. -/
theorem mc_mul_one : MC(Mul 1) = 1 := by sorry

/-- Three products are necessary and sufficient, Proposition 2.3. -/
theorem mc_mul_two : MC(Mul 2) = 3 := by sorry

/-- Unrestricted three-term complexity, Proposition 2.4. -/
theorem mc_mul_three : MC(Mul 3) = 6 := by sorry

namespace N4
/-- The eight-gate obstruction in the proof of Theorem 9.1. -/
theorem no_eight_gate_circuit : ¬ HasCircuit (Mul 4) 8 := by sorry

/-- Theorem 9.1: four-term multiplication has unrestricted complexity nine. -/
theorem mc_mul_four : MC(Mul 4) = 9 := by sorry
end N4
end
end UnrestrictedBooleanMul
