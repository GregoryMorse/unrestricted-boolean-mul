import UnrestrictedBooleanMul.N5.ColourNormalization

/-!
# Algebraic three-colour birth and budget

This module packages the colour-count part of manuscript Theorem 12.3.  Two
independent normalized colours and their product give three linearly
independent high directions.  Consequently the old-product branch under the
total budget `e + s ≤ 3` has quadratic defect zero.

The later target-shadow saturation statement is deliberately separate; no
finite colour-state enumeration is used here.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def twoColourDirections (alpha beta : Fin 4 → F₂) : Fin 2 → ANF 10 :=
  ![colourCombination alpha, colourCombination beta]

/-- Over `F₂`, two nonzero unequal colour-coordinate vectors give two
independent actual cubic colours. -/
theorem twoColourDirections_linearIndependent
    (alpha beta : Fin 4 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hne : alpha ≠ beta) :
    LinearIndependent F₂ (twoColourDirections alpha beta) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  rcases f2_eq_zero_or_one (f 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (f 1) with h1 | h1
  · fin_cases i <;> assumption
  · have hcomb : colourCombination beta = 0 := by
      simpa [twoColourDirections, Fin.sum_univ_succ, h0, h1] using hf
    have hbeta0 : beta = 0 := colourCombination_injective (by
      simpa using hcomb)
    exact (hbeta hbeta0).elim
  · have hcomb : colourCombination alpha = 0 := by
      simpa [twoColourDirections, Fin.sum_univ_succ, h0, h1] using hf
    have halpha0 : alpha = 0 := colourCombination_injective (by
      simpa using hcomb)
    exact (halpha halpha0).elim
  · have hcomb : colourCombination alpha + colourCombination beta = 0 := by
      simpa [twoColourDirections, Fin.sum_univ_succ, h0, h1] using hf
    have neg_eq_self (x : ANF 10) : -x = x := by
      have hx : x + x = 0 := by
        have htwo : (1 + 1 : F₂) = 0 := by decide
        calc
          x + x = (1 + 1 : F₂) • x := by rw [add_smul, one_smul]
          _ = 0 := by rw [htwo, zero_smul]
      exact (add_eq_zero_iff_eq_neg.mp hx).symm
    have hab : colourCombination alpha = colourCombination beta :=
      (add_eq_zero_iff_eq_neg.mp hcomb).trans (neg_eq_self _)
    exact (hne (colourCombination_injective hab)).elim

def bornThreeColourDirections (alpha beta : Fin 4 → F₂) :
    Fin 3 → ANF 10 :=
  ![colourCombination alpha, colourCombination beta,
    colourCombination alpha * colourCombination beta]

/-- Kernel-checked third-direction statement behind the rank-two colour
branch of Theorem 12.3. -/
theorem bornThreeColourDirections_linearIndependent
    (alpha beta : Fin 4 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hne : alpha ≠ beta) :
    LinearIndependent F₂ (bornThreeColourDirections alpha beta) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have hpair := twoColourDirections_linearIndependent alpha beta
    halpha hbeta hne
  have hx0 : colourQuarticProjection (colourCombination alpha) = 0 :=
    (LinearMap.mem_ker).mp
      (colourSpace_le_colourQuarticProjection_ker
        (colourCombination_mem_colourSpace alpha))
  have hy0 : colourQuarticProjection (colourCombination beta) = 0 :=
    (LinearMap.mem_ker).mp
      (colourSpace_le_colourQuarticProjection_ker
        (colourCombination_mem_colourSpace beta))
  rcases f2_eq_zero_or_one (f 2) with h2 | h2
  · let g : Fin 2 → F₂ := ![f 0, f 1]
    have hsum : ∑ k : Fin 2,
        g k • twoColourDirections alpha beta k = 0 := by
      simpa [g, bornThreeColourDirections, twoColourDirections,
        Fin.sum_univ_succ, h2] using hf
    have hg := Fintype.linearIndependent_iff.mp hpair g hsum
    fin_cases i
    · exact hg 0
    · exact hg 1
    · exact h2
  · have hprojected := congrArg colourQuarticProjection hf
    have hproductZero : colourQuarticProjection
        (colourCombination alpha * colourCombination beta) = 0 := by
      simpa [bornThreeColourDirections, Fin.sum_univ_succ,
        h2, hx0, hy0] using hprojected
    exact (independentColours_product_high_ne_zero alpha beta
      halpha hbeta hne hproductZero).elim

/-- In the old-product branch there are already three high directions, so
the manuscript budget `e+s≤3` forces `e=0`. -/
theorem oldProductColour_forces_defect_zero
    {e s : Nat} (hbudget : e + s ≤ 3) (hthree : 3 ≤ s) : e = 0 := by
  omega

end
end N5
end UnrestrictedBooleanMul
