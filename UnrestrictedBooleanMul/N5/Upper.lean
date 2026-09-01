import UnrestrictedBooleanMul.N5.Target
import Mathlib.Tactic.Ring

/-!
# Explicit thirteen-AND circuit for five-term multiplication

This module records the symmetric five-way binary formula displayed in the
manuscript.  All thirteen gates multiply affine linear forms in the original
inputs, so the construction is bilinear and therefore also legal in the
unrestricted circuit model.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Supports of the thirteen linear forms used on each input side. -/
def fiveLinearSupport : Fin 13 → Finset (Fin 5) :=
  ![{0}, {1}, {0, 1}, {2}, {0, 2}, {3}, {0, 2, 3},
    {4}, {2, 4}, {1, 2, 4}, {3, 4}, {0, 1, 3, 4}, {0, 1, 2, 3, 4}]

def fiveLeft (i : Fin 13) : ANF 10 :=
  ∑ k ∈ fiveLinearSupport i, aVar 5 k

def fiveRight (i : Fin 13) : ANF 10 :=
  ∑ k ∈ fiveLinearSupport i, bVar 5 k

theorem fiveLeft_mem_affine (i : Fin 13) : fiveLeft i ∈ affine 10 := by
  exact Submodule.sum_mem _ fun k _ => aVar_mem_affine 5 k

theorem fiveRight_mem_affine (i : Fin 13) : fiveRight i ∈ affine 10 := by
  exact Submodule.sum_mem _ fun k _ => bVar_mem_affine 5 k

/-- The thirteen multiplication gates. -/
def five : Circuit 10 13 :=
  Circuit.ofAffineProducts fiveLeft fiveRight
    fiveLeft_mem_affine fiveRight_mem_affine

/-- Gate indices XORed to obtain each of the nine output coefficients. -/
def fiveOutputSupport : Fin 9 → Finset (Fin 13) :=
  ![{0},
    {0, 1, 2},
    {0, 1, 3, 4},
    {0, 3, 5, 6, 7, 8, 11, 12},
    {0, 1, 2, 5, 6, 7, 9, 10, 12},
    {0, 1, 3, 4, 7, 9, 11, 12},
    {3, 5, 7, 8},
    {5, 7, 10},
    {7}]

def fiveRecombine (s : Fin 9) : ANF 10 :=
  ∑ i ∈ fiveOutputSupport s, five.gate i

/-- Characteristic-two normalization needed by three recombination rows. -/
private theorem three_eq_one_anf : (3 : ANF 10) = 1 := by
  calc
    (3 : ANF 10) = 2 + 1 := by norm_num
    _ = 1 := by simp

/-- The nine recombination identities, proved inside the Boolean ANF ring. -/
theorem five_formula : Mul 5 = fiveRecombine := by
  funext s
  fin_cases s <;>
    simp [Mul, mulCoefficient, Fin.sum_univ_succ, fiveRecombine,
      fiveOutputSupport, five, fiveLeft, fiveRight, fiveLinearSupport,
      Circuit.ofAffineProducts] <;> ring_nf <;> simp [three_eq_one_anf]

theorem five_computes : five.Computes (Mul 5) := by
  rw [five_formula]
  intro s
  exact Submodule.sum_mem _ fun i _ => gate_mem_finalWire five i

/-- The displayed bilinear construction is a legal unrestricted circuit. -/
theorem mul_five_upper : HasCircuit (Mul 5) 13 :=
  ⟨⟨five, five_computes⟩⟩

end

end N5
end UnrestrictedBooleanMul
