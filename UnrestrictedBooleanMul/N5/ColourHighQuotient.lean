import UnrestrictedBooleanMul.N5.ThreeColour
import UnrestrictedBooleanMul.N5.HighDefect

/-!
# Three-colour birth in the high quotient

The circuit ledger counts directions modulo all degree-at-most-two ANFs.
This module upgrades the explicit colour-birth certificate to exactly that
quotient and converts it into a lower bound for `stateHighRank`.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem colourCubicCoordinate_eq_zero_of_quadratic
    (r : Fin 4) {p : ANF 10} (hp : p ∈ N4.quadraticANFSpace 10) :
    colourCubicCoordinate r p = 0 := by
  apply hp ⟨colourCubicRow r⟩
  fin_cases r <;> decide

theorem colourQuarticProjection_eq_zero_of_quadratic
    {p : ANF 10} (hp : p ∈ N4.quadraticANFSpace 10) :
    colourQuarticProjection p = 0 := by
  funext r
  apply hp ⟨colourQuarticRow r⟩
  fin_cases r <;> decide

@[simp] theorem colourCubicCoordinate_colourCombination
    (r : Fin 4) (alpha : Fin 4 → F₂) :
    colourCubicCoordinate r (colourCombination alpha) = alpha r := by
  change colourCubicCoordinate r
    (∑ i : Fin 4, alpha i • colourDirection i) = alpha r
  rw [map_sum]
  simp only [map_smul, smul_eq_mul,
    colourDirection_cubic_coefficient]
  rw [Finset.sum_eq_single r]
  · simp
  · intro i _hi hir
    simp [Ne.symm hir]
  · simp

/-- The normalized cubic-colour space embeds in the quotient by quadratic
ANFs. -/
def colourHighCombination :
    (Fin 4 → F₂) →ₗ[F₂]
      ((ANF 10) ⧸ N4.quadraticANFSpace 10) :=
  (Submodule.mkQ (N4.quadraticANFSpace 10)).comp colourCombination

theorem colourHighCombination_injective :
    Function.Injective colourHighCombination := by
  rw [LinearMap.ker_eq_bot.symm]
  ext alpha
  constructor
  · intro halpha
    have hquot := (LinearMap.mem_ker).mp halpha
    change Submodule.mkQ (N4.quadraticANFSpace 10)
      (colourCombination alpha) = 0 at hquot
    have hquad : colourCombination alpha ∈ N4.quadraticANFSpace 10 :=
      (Submodule.Quotient.mk_eq_zero
        (N4.quadraticANFSpace 10)).mp hquot
    rw [Submodule.mem_bot]
    funext r
    have hcoord := colourCubicCoordinate_eq_zero_of_quadratic r hquad
    simpa using hcoord
  · intro halpha
    rw [Submodule.mem_bot] at halpha
    subst alpha
    exact (LinearMap.mem_ker).2 (map_zero colourHighCombination)

/-- The three born colours as directions in the literal high quotient. -/
def bornThreeHighDirections (alpha beta : Fin 4 → F₂) :
    Fin 3 → ((ANF 10) ⧸ N4.quadraticANFSpace 10) :=
  fun i => Submodule.mkQ (N4.quadraticANFSpace 10)
    (bornThreeColourDirections alpha beta i)

/-- Independent colours and their product remain three independent
directions after quotienting by all quadratic ANFs. -/
theorem bornThreeHighDirections_linearIndependent
    (alpha beta : Fin 4 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hne : alpha ≠ beta) :
    LinearIndependent F₂ (bornThreeHighDirections alpha beta) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have hsumQuad :
      (∑ k : Fin 3, f k • bornThreeColourDirections alpha beta k) ∈
        N4.quadraticANFSpace 10 := by
    apply (Submodule.Quotient.mk_eq_zero
      (N4.quadraticANFSpace 10)).mp
    change Submodule.mkQ (N4.quadraticANFSpace 10)
      (∑ k : Fin 3, f k • bornThreeColourDirections alpha beta k) = 0
    rw [map_sum]
    simp only [map_smul]
    change (∑ k : Fin 3, f k •
      bornThreeHighDirections alpha beta k) = 0
    exact hf
  rcases f2_eq_zero_or_one (f 2) with h2 | h2
  · let gamma : Fin 4 → F₂ := f 0 • alpha + f 1 • beta
    have hgammaHigh : colourHighCombination gamma = 0 := by
      change Submodule.mkQ (N4.quadraticANFSpace 10)
        (colourCombination gamma) = 0
      apply (Submodule.Quotient.mk_eq_zero
        (N4.quadraticANFSpace 10)).mpr
      have hcolourQuad : colourCombination gamma ∈
          N4.quadraticANFSpace 10 := by
        simpa [gamma, bornThreeColourDirections, Fin.sum_univ_succ,
          h2, map_add, map_smul] using hsumQuad
      exact hcolourQuad
    have hgamma : gamma = 0 := by
      apply colourHighCombination_injective
      rw [hgammaHigh, map_zero]
    rcases f2_eq_zero_or_one (f 0) with h0 | h0 <;>
      rcases f2_eq_zero_or_one (f 1) with h1 | h1
    · fin_cases i <;> assumption
    · have hbeta0 : beta = 0 := by
        simpa [gamma, h0, h1] using hgamma
      exact (hbeta hbeta0).elim
    · have halpha0 : alpha = 0 := by
        simpa [gamma, h0, h1] using hgamma
      exact (halpha halpha0).elim
    · have hab0 : alpha + beta = 0 := by
        simpa [gamma, h0, h1] using hgamma
      have hab : alpha = beta := by
        funext r
        exact CharTwo.add_eq_zero.mp (congrFun hab0 r)
      exact (hne hab).elim
  · have hx0 : colourQuarticProjection
        (colourCombination alpha) = 0 :=
      (LinearMap.mem_ker).mp
        (colourSpace_le_colourQuarticProjection_ker
          (colourCombination_mem_colourSpace alpha))
    have hy0 : colourQuarticProjection
        (colourCombination beta) = 0 :=
      (LinearMap.mem_ker).mp
        (colourSpace_le_colourQuarticProjection_ker
          (colourCombination_mem_colourSpace beta))
    have hproductZero : colourQuarticProjection
        (colourCombination alpha * colourCombination beta) = 0 := by
      have hprojected :=
        colourQuarticProjection_eq_zero_of_quadratic hsumQuad
      simpa [bornThreeColourDirections, Fin.sum_univ_succ,
        h2, hx0, hy0] using hprojected
    exact (independentColours_product_high_ne_zero alpha beta
      halpha hbeta hne hproductZero).elim

/-- If a wire state contains two independent normalized colours and their
product, its high quotient has dimension at least three. -/
theorem three_le_stateHighRank_of_bornColours_mem
    (V : Submodule F₂ (ANF 10)) (alpha beta : Fin 4 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hne : alpha ≠ beta)
    (hmem : ∀ i, bornThreeColourDirections alpha beta i ∈ V) :
    3 ≤ stateHighRank V := by
  have hspan : Submodule.span F₂
      (Set.range (bornThreeHighDirections alpha beta)) ≤ stateHighImage V := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact ⟨bornThreeColourDirections alpha beta i, hmem i, rfl⟩
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card
      (bornThreeHighDirections_linearIndependent alpha beta
        halpha hbeta hne),
    stateHighImage_finrank] at hdim
  simpa using hdim

/-- Circuit-ledger form of the old-product-colour conclusion: above a
quadratic base, the presence of the three born colours forces the base
quadratic defect to be zero. -/
theorem quadraticBase_defect_eq_zero_of_bornColours_mem
    {W V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix W V)
    (hWquad : W ≤ N4.quadraticANFSpace 10)
    (alpha beta : Fin 4 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hne : alpha ≠ beta)
    (hmem : ∀ i, bornThreeColourDirections alpha beta i ∈ V) :
    N4.flagDefectRank W (mulTarget 5) = 0 := by
  have hbudget := hreach.quadraticDefect_add_high_le_three hWquad
  have hthree := three_le_stateHighRank_of_bornColours_mem
    V alpha beta halpha hbeta hne hmem
  omega

end
end N5
end UnrestrictedBooleanMul
