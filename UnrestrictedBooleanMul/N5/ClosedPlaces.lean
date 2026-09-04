import UnrestrictedBooleanMul.N5.RelationMap

/-!
# Closed-place target directions

The four length-two place types used by the five-term argument are represented
by their coefficient subspaces: three rational first-jet lines and the
two-dimensional degree-two place.  The final rank-eight theorem is a direct
pivot proof on the displayed coefficient words.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- First Hasse jet at the rational place zero. -/
def jZeroCoeff : TargetCoeff :=
  ![0, 1, 0, 0, 0, 0, 0, 0, 0]

/-- First Hasse jet at the rational place one. -/
def jOneCoeff : TargetCoeff :=
  ![0, 0, 1, 0, 1, 0, 1, 0, 0]

/-- First Hasse jet at the rational place infinity, reduced modulo rational
evaluation directions. -/
def jInfinityCoeff : TargetCoeff :=
  ![0, 1, 1, 1, 1, 1, 1, 0, 0]

/-- First basis direction at the degree-two closed point. -/
def dStarZeroCoeff : TargetCoeff :=
  ![0, 0, 1, 0, 0, 1, 0, 0, 0]

/-- Second basis direction at the degree-two closed point. -/
def dStarOneCoeff : TargetCoeff :=
  ![0, 0, 0, 1, 0, 0, 1, 0, 0]

/- The generated return-history certificate predates the row reduction used
for `jOneCoeff` and `jInfinityCoeff` above.  Its parameter coordinates use
these two original jet representatives. -/
def historyJOneCoeff : TargetCoeff :=
  ![0, 1, 0, 1, 0, 1, 0, 1, 0]

def historyJInfinityCoeff : TargetCoeff :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- Target words in the exact coordinate order used by the raw history
certificate. -/
def returnHistoryCorrectionDirections : Fin 8 → TargetCoeff :=
  ![rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff, historyJOneCoeff,
    historyJInfinityCoeff, dStarZeroCoeff, dStarOneCoeff]

def jZeroSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ {jZeroCoeff}

def jOneSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ {jOneCoeff}

def jInfinitySpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ {jInfinityCoeff}

def dStarSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ {dStarZeroCoeff, dStarOneCoeff}

/-- The eight displayed rational, jet, and degree-two directions. -/
def closedPlaceDirections : Fin 8 → TargetCoeff :=
  ![rZeroCoeff, rOneCoeff, rInfinityCoeff, jZeroCoeff, jOneCoeff,
    jInfinityCoeff, dStarZeroCoeff, dStarOneCoeff]

def closedPlaceCoeffSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ (Set.range closedPlaceDirections)

/-- The displayed closed-place directions are independent.  Coordinates 7,
8, and 0 first remove the rational directions; coordinates 1 through 6 then
give a triangular pivot chain for the five infinitesimal directions. -/
theorem closedPlaceDirections_linearIndependent :
    LinearIndependent F₂ closedPlaceDirections := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  have h0 := congrFun h (0 : Fin 9)
  have h1 := congrFun h (1 : Fin 9)
  have h2 := congrFun h (2 : Fin 9)
  have h3 := congrFun h (3 : Fin 9)
  have h4 := congrFun h (4 : Fin 9)
  have h5 := congrFun h (5 : Fin 9)
  have h6 := congrFun h (6 : Fin 9)
  have h7 := congrFun h (7 : Fin 9)
  have h8 := congrFun h (8 : Fin 9)
  simp [closedPlaceDirections, rZeroCoeff, rOneCoeff, rInfinityCoeff,
    jZeroCoeff, jOneCoeff, jInfinityCoeff, dStarZeroCoeff,
    dStarOneCoeff, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hf1 : f 1 = 0 := h7
  have hf0 : f 0 = 0 := by simpa [hf1] using h0
  have hf2 : f 2 = 0 := by simpa [hf1] using h8
  have hf45 : f 4 = f 5 := by
    have hh : f 4 + f 5 = 0 := by simpa [hf1] using h4
    rw [← CharTwo.sub_eq_add] at hh
    exact sub_eq_zero.mp hh
  have hf56 : f 5 = f 6 := by
    have hh : f 5 + f 6 = 0 := by simpa [hf1] using h5
    rw [← CharTwo.sub_eq_add] at hh
    exact sub_eq_zero.mp hh
  have hf5 : f 5 = 0 := by
    have ht : f 6 + (f 6 + f 6) = 0 := by
      simpa [hf1, hf45, hf56] using h2
    have hself : f 6 + f 6 = 0 := CharTwo.add_self_eq_zero _
    have hf6 : f 6 = 0 := by simpa [hself] using ht
    exact hf56.trans hf6
  have hf4 : f 4 = 0 := hf45.trans hf5
  have hf6 : f 6 = 0 := hf56.symm.trans hf5
  have hf3 : f 3 = 0 := by simpa [hf1, hf5] using h1
  have hf7 : f 7 = 0 := by simpa [hf1, hf5] using h3
  fin_cases i <;> assumption

/-- Manuscript Lemma 4.1, final independence clause. -/
theorem closedPlaceCoeffSpace_finrank :
    Module.finrank F₂ closedPlaceCoeffSpace = 8 := by
  exact finrank_span_eq_card closedPlaceDirections_linearIndependent

/-- The rational-place space has dimension three. -/
theorem rationalCoeffSpace_finrank :
    Module.finrank F₂ rationalCoeffSpace = 3 := by
  let rationalDirections : Fin 3 → TargetCoeff :=
    ![rZeroCoeff, rOneCoeff, rInfinityCoeff]
  have hLI : LinearIndependent F₂ rationalDirections := by
    rw [Fintype.linearIndependent_iff]
    intro f h i
    have h0 := congrFun h (0 : Fin 9)
    have h7 := congrFun h (7 : Fin 9)
    have h8 := congrFun h (8 : Fin 9)
    simp [rationalDirections, rZeroCoeff, rOneCoeff, rInfinityCoeff,
      Fin.sum_univ_succ] at h0 h7 h8
    have hf1 : f 1 = 0 := h7
    have hf0 : f 0 = 0 := by simpa [hf1] using h0
    have hf2 : f 2 = 0 := by simpa [hf1] using h8
    fin_cases i <;> assumption
  have hspan : rationalCoeffSpace =
      Submodule.span F₂ (Set.range rationalDirections) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x (rfl | rfl | rfl)
      · exact Submodule.subset_span ⟨0, by simp [rationalDirections]⟩
      · exact Submodule.subset_span ⟨1, by simp [rationalDirections]⟩
      · exact Submodule.subset_span ⟨2, by simp [rationalDirections]⟩
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact Submodule.subset_span
          (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rw [hspan]
  exact finrank_span_eq_card hLI

end

end N5
end UnrestrictedBooleanMul
