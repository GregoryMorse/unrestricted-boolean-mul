import UnrestrictedBooleanMul.N5.ColourNormalization
import UnrestrictedBooleanMul.N5.HighDefect

/-!
# Algebraic factor-colour trichotomy

Two vectors over `F₂` are either both zero, contained in one nonzero line, or
linearly independent.  Applied to the quotient by quadratic ANFs, this is the
exact zero/rank-one/rank-two split for the factors of a later AND gate.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def pairDirections {H : Type*} (x y : H) : Fin 2 → H := ![x, y]

private theorem add_self_eq_zero_module
    {H : Type*} [AddCommGroup H] [Module F₂ H] (x : H) : x + x = 0 := by
  calc
    x + x = ((1 : F₂) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]

/-- Two nonzero unequal vectors over `F₂` are linearly independent. -/
theorem pairDirections_linearIndependent
    {H : Type*} [AddCommGroup H] [Module F₂ H]
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndependent F₂ (pairDirections x y) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  rcases f2_eq_zero_or_one (f 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (f 1) with h1 | h1
  · fin_cases i <;> assumption
  · have : y = 0 := by
      simpa [pairDirections, Fin.sum_univ_succ, h0, h1] using hf
    exact (hy this).elim
  · have : x = 0 := by
      simpa [pairDirections, Fin.sum_univ_succ, h0, h1] using hf
    exact (hx this).elim
  · have hsum : x + y = 0 := by
      simpa [pairDirections, Fin.sum_univ_succ, h0, h1] using hf
    have heq : x = y := by
      calc
        x = x + 0 := by rw [add_zero]
        _ = x + (y + y) := by rw [add_self_eq_zero_module]
        _ = (x + y) + y := by ac_rfl
        _ = y := by rw [hsum, zero_add]
    exact (hxy heq).elim

/-- Exact trichotomy for two factor colours under any linear colour map. -/
theorem factorColour_trichotomy
    {H : Type*} [AddCommGroup H] [Module F₂ H]
    (χ : ANF 10 →ₗ[F₂] H) (X Y : ANF 10) :
    (χ X = 0 ∧ χ Y = 0) ∨
      (∃ g : H, g ≠ 0 ∧ RankOneColourPattern χ g X Y) ∨
      LinearIndependent F₂ (pairDirections (χ X) (χ Y)) := by
  by_cases hX : χ X = 0
  · by_cases hY : χ Y = 0
    · exact Or.inl ⟨hX, hY⟩
    · exact Or.inr (Or.inl ⟨χ Y, hY, Or.inr (Or.inl ⟨hX, rfl⟩)⟩)
  · by_cases hY : χ Y = 0
    · exact Or.inr (Or.inl ⟨χ X, hX, Or.inl ⟨rfl, hY⟩⟩)
    · by_cases hXY : χ X = χ Y
      · exact Or.inr (Or.inl
          ⟨χ X, hX, Or.inr (Or.inr ⟨rfl, hXY.symm⟩)⟩)
      · exact Or.inr (Or.inr
          (pairDirections_linearIndependent (χ X) (χ Y) hX hY hXY))

/-- Circuit-facing version: factor colours are their literal classes modulo
all degree-at-most-two ANFs. -/
theorem highQuotient_factor_trichotomy (X Y : ANF 10) :
    (X ∈ N4.quadraticANFSpace 10 ∧ Y ∈ N4.quadraticANFSpace 10) ∨
      (∃ g : (ANF 10) ⧸ N4.quadraticANFSpace 10,
        g ≠ 0 ∧
        RankOneColourPattern
          (Submodule.mkQ (N4.quadraticANFSpace 10)) g X Y) ∨
      LinearIndependent F₂
        (pairDirections
          (Submodule.mkQ (N4.quadraticANFSpace 10) X)
          (Submodule.mkQ (N4.quadraticANFSpace 10) Y)) := by
  rcases factorColour_trichotomy
      (Submodule.mkQ (N4.quadraticANFSpace 10)) X Y with
    hzero | hrankOne | hrankTwo
  · exact Or.inl
      ⟨(Submodule.Quotient.mk_eq_zero _).mp hzero.1,
        (Submodule.Quotient.mk_eq_zero _).mp hzero.2⟩
  · exact Or.inr (Or.inl hrankOne)
  · exact Or.inr (Or.inr hrankTwo)

end
end N5
end UnrestrictedBooleanMul
