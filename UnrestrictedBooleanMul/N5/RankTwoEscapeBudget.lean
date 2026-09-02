import UnrestrictedBooleanMul.N5.FirstOrderColourReduction
import UnrestrictedBooleanMul.N5.ColourHighQuotient
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Rank-two escape and the third high direction

At a target-producing step the product high class is old.  If it lies outside
the span of two independent factor classes, the current state already contains
three independent high directions.  The exact defect/high-rank ledger then
forces a canonical anchored base to have zero quadratic defect.  This is the
chronology-free budget half of the rank-two branch in manuscript Theorem 12.3.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private abbrev HighQuotient :=
  (ANF 10) ⧸ N4.quadraticANFSpace 10

/-- Append a proposed third direction to the two factor directions. -/
def highTripleDirections (x y z : HighQuotient) : Fin 3 → HighQuotient :=
  Fin.snoc (pairDirections x y) z

theorem highTripleDirections_linearIndependent
    (x y z : HighQuotient)
    (hxy : LinearIndependent F₂ (pairDirections x y))
    (hz : z ∉ Submodule.span F₂
      (Set.range (pairDirections x y))) :
    LinearIndependent F₂ (highTripleDirections x y z) := by
  simpa [highTripleDirections] using hxy.finSnoc hz

/-- Three independent high classes contained in a state give high rank at
least three. -/
theorem three_le_stateHighRank_of_independent_high_triple
    (V : Submodule F₂ (ANF 10))
    (x y z : HighQuotient)
    (hx : x ∈ stateHighImage V)
    (hy : y ∈ stateHighImage V)
    (hz : z ∈ stateHighImage V)
    (hxy : LinearIndependent F₂ (pairDirections x y))
    (hzspan : z ∉ Submodule.span F₂
      (Set.range (pairDirections x y))) :
    3 ≤ stateHighRank V := by
  have htriple : LinearIndependent F₂ (highTripleDirections x y z) :=
    highTripleDirections_linearIndependent x y z hxy hzspan
  have hspan : Submodule.span F₂
      (Set.range (highTripleDirections x y z)) ≤ stateHighImage V := by
    rw [Submodule.span_le]
    rintro w ⟨i, rfl⟩
    fin_cases i
    · simpa [highTripleDirections, pairDirections] using hx
    · simpa [highTripleDirections, pairDirections] using hy
    · simpa [highTripleDirections, pairDirections] using hz
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card htriple, stateHighImage_finrank] at hdim
  simpa using hdim

/-- Any quadratic base below a legal state containing three high directions
has zero target-quotient defect. -/
theorem quadraticBase_defect_eq_zero_of_three_highRank
    {W V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix W V)
    (hWquad : W ≤ N4.quadraticANFSpace 10)
    (hthree : 3 ≤ stateHighRank V) :
    N4.flagDefectRank W (mulTarget 5) = 0 := by
  have hbudget := hreach.quadraticDefect_add_high_le_three hWquad
  omega

/-- For a canonical anchored base, three high directions force the anchor
itself to be target-valued; equivalently the base defect is zero. -/
theorem anchor_mem_targetTwoSpace_of_three_highRank
    (q : TwoForm) (hqdec : IsDecomposableTwo q)
    {V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix (firstOrderAnchorState q) V)
    (hthree : 3 ≤ stateHighRank V) :
    q ∈ targetTwoSpace := by
  by_contra hqT
  have hzero := quadraticBase_defect_eq_zero_of_three_highRank hreach
    (E2.quadraticEnvelopeState_le_quadraticANFSpace
      (firstOrderAnchorTwoSpace q)) hthree
  rw [firstOrderAnchorState_defectRank_of_not_mem_target q hqdec hqT] at hzero
  omega

/-- Rank-two first-escape form: if the product class is genuinely third, the
anchor defect must vanish.  The target-correction equation supplies oldness
of the product class, rather than any chronological assumption. -/
theorem rankTwo_escape_anchor_mem_target_of_product_outside_pair
    (q : TwoForm) (hqdec : IsDecomposableTwo q)
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hreach : DefectLegalSuffix (firstOrderAnchorState q) V)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hescape : ¬ (andExtend V X Y ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState))
    (hpair : LinearIndependent F₂
      (pairDirections
        (Submodule.mkQ (N4.quadraticANFSpace 10) X)
        (Submodule.mkQ (N4.quadraticANFSpace 10) Y)))
    (hproduct : Submodule.mkQ (N4.quadraticANFSpace 10) (X * Y) ∉
      Submodule.span F₂
        (Set.range (pairDirections
          (Submodule.mkQ (N4.quadraticANFSpace 10) X)
          (Submodule.mkQ (N4.quadraticANFSpace 10) Y)))) :
    q ∈ targetTwoSpace := by
  rcases exists_product_correction_of_targetStep_escape X Y hold hescape with
    ⟨t, v, ht, _htU, hv, heq⟩
  have hxImage : Submodule.mkQ (N4.quadraticANFSpace 10) X ∈
      stateHighImage V := ⟨X, hX, rfl⟩
  have hyImage : Submodule.mkQ (N4.quadraticANFSpace 10) Y ∈
      stateHighImage V := ⟨Y, hY, rfl⟩
  have hpImage : Submodule.mkQ (N4.quadraticANFSpace 10) (X * Y) ∈
      stateHighImage V :=
    productHighClass_mem_stateHighImage_of_target_add_old
      V X Y t v ht hv heq
  have hthree : 3 ≤ stateHighRank V :=
    three_le_stateHighRank_of_independent_high_triple V _ _ _
      hxImage hyImage hpImage hpair hproduct
  exact anchor_mem_targetTwoSpace_of_three_highRank q hqdec hreach hthree

/-- Once the two factor classes and their product have been localized to the
four-dimensional rational colour module, the invertible colour-birth matrix
supplies the independent third class.  Hence the rank-two escape budget forces
the anchor defect to vanish. -/
theorem rankTwo_escape_anchor_mem_target_of_localColours
    (q : TwoForm) (hqdec : IsDecomposableTwo q)
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hreach : DefectLegalSuffix (firstOrderAnchorState q) V)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hescape : ¬ (andExtend V X Y ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState))
    (alpha beta : Fin 4 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hab : alpha ≠ beta)
    (hXcolour : Submodule.mkQ (N4.quadraticANFSpace 10) X =
      colourHighCombination alpha)
    (hYcolour : Submodule.mkQ (N4.quadraticANFSpace 10) Y =
      colourHighCombination beta)
    (hproductColour :
      Submodule.mkQ (N4.quadraticANFSpace 10) (X * Y) =
        Submodule.mkQ (N4.quadraticANFSpace 10)
          (colourCombination alpha * colourCombination beta)) :
    q ∈ targetTwoSpace := by
  have hbirth₀ := bornThreeHighDirections_linearIndependent
    alpha beta halpha hbeta hab
  have hbirth : LinearIndependent F₂
      (highTripleDirections
        (colourHighCombination alpha)
        (colourHighCombination beta)
        (Submodule.mkQ (N4.quadraticANFSpace 10)
          (colourCombination alpha * colourCombination beta))) := by
    have heq : highTripleDirections
        (colourHighCombination alpha)
        (colourHighCombination beta)
        (Submodule.mkQ (N4.quadraticANFSpace 10)
          (colourCombination alpha * colourCombination beta)) =
        bornThreeHighDirections alpha beta := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact hbirth₀
  have hbirthXY : LinearIndependent F₂
      (highTripleDirections
        (Submodule.mkQ (N4.quadraticANFSpace 10) X)
        (Submodule.mkQ (N4.quadraticANFSpace 10) Y)
        (Submodule.mkQ (N4.quadraticANFSpace 10) (X * Y))) := by
    rw [hXcolour, hYcolour, hproductColour]
    exact hbirth
  have hsplit :
      LinearIndependent F₂
          (pairDirections
            (Submodule.mkQ (N4.quadraticANFSpace 10) X)
            (Submodule.mkQ (N4.quadraticANFSpace 10) Y)) ∧
        Submodule.mkQ (N4.quadraticANFSpace 10) (X * Y) ∉
          Submodule.span F₂
            (Set.range (pairDirections
              (Submodule.mkQ (N4.quadraticANFSpace 10) X)
              (Submodule.mkQ (N4.quadraticANFSpace 10) Y))) := by
    exact linearIndependent_finSnoc.mp (by
      simpa [highTripleDirections] using hbirthXY)
  exact rankTwo_escape_anchor_mem_target_of_product_outside_pair
    q hqdec V X Y hreach hX hY hold hescape hsplit.1 hsplit.2

end
end N5
end UnrestrictedBooleanMul
