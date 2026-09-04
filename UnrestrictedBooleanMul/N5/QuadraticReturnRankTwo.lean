import UnrestrictedBooleanMul.N5.QuadraticReturnFeedback
import UnrestrictedBooleanMul.N5.RankOneZeroQuadraticDefect
import UnrestrictedBooleanMul.N5.RankTwoEscapeBudget

/-!
# Rank-two feedback after a quadratic return

An unpopulated return supplies a genuine quadratic-defect direction.  If a
later target escape uses two independent localized high colours, colour birth
supplies a third independent high direction.  The exact decomposition of
total defect into quadratic defect plus high rank then gives `1 + 3 > 3`.

This argument is purely algebraic.  It does not enumerate circuits, Boolean
assignments, or quadratic forms.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private abbrev HighQuotient :=
  (ANF 10) ⧸ N4.quadraticANFSpace 10

/-- An unpopulated quadratic section cannot itself be target-valued. -/
theorem unpopulatedQuadraticSection_not_mem_targetTwoSpace
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z) :
    z ∉ targetTwoSpace := by
  intro hz
  apply hunpopulated 0 decomposableTwo_zero
  simpa using hz

/-- If a state contains a quadratic representative of an unpopulated return,
then its quadratic defect is positive. -/
theorem one_le_stateQuadraticDefectRank_of_unpopulatedReturn
    (z : TwoForm) (hunpopulated : UnpopulatedQuadraticSection z)
    (V : Submodule F₂ (ANF 10)) (p : ANF 10)
    (hpV : p ∈ V) (hpquad : p ∈ N4.quadraticANFSpace 10)
    (hpz : quadraticProjection 10 p = z) :
    1 ≤ stateQuadraticDefectRank V := by
  have hzNotTarget :=
    unpopulatedQuadraticSection_not_mem_targetTwoSpace z hunpopulated
  by_contra hnot
  have hzero : stateQuadraticDefectRank V = 0 := by omega
  have hpTarget : p ∈ N4.targetAmbient 10 (mulTarget 5) :=
    quadratic_mem_targetAmbient_of_stateQuadraticDefectRank_eq_zero
      V hzero hpV hpquad
  have hpProjectionTarget : quadraticProjection 10 p ∈ targetTwoSpace :=
    quadraticProjection_mem_targetTwoSpace_of_mem_targetAmbient hpTarget
  apply hzNotTarget
  rw [← hpz]
  exact hpProjectionTarget

/-- At positive quadratic defect, an escaping target gate cannot have two
independent factor classes whose product is a genuinely third high class. -/
theorem rankTwo_escape_impossible_of_positive_quadraticDefect
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hdef : N4.flagDefectRank (andExtend V X Y) (mulTarget 5) ≤ 3)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hescape : ¬ (andExtend V X Y ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState))
    (hquadPositive : 1 ≤ stateQuadraticDefectRank V)
    (hpair : LinearIndependent F₂
      (pairDirections
        (Submodule.mkQ (N4.quadraticANFSpace 10) X)
        (Submodule.mkQ (N4.quadraticANFSpace 10) Y)))
    (hproduct : Submodule.mkQ (N4.quadraticANFSpace 10) (X * Y) ∉
      Submodule.span F₂
        (Set.range (pairDirections
          (Submodule.mkQ (N4.quadraticANFSpace 10) X)
          (Submodule.mkQ (N4.quadraticANFSpace 10) Y)))) : False := by
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
  have hVnext : V ≤ andExtend V X Y := le_sup_left
  have hVdef : N4.flagDefectRank V (mulTarget 5) ≤ 3 :=
    (flagDefectRank_mono hVnext).trans hdef
  have hsplit := flagDefectRank_eq_quadratic_add_high V
  omega

/-- The preceding contradiction in the localized rational-colour form used
by the n=5 fixed-block analysis. -/
theorem rankTwo_escape_impossible_of_positive_quadraticDefect_localColours
    (V : Submodule F₂ (ANF 10)) (X Y : ANF 10)
    (hX : X ∈ V) (hY : Y ∈ V)
    (hdef : N4.flagDefectRank (andExtend V X Y) (mulTarget 5) ≤ 3)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState)
    (hescape : ¬ (andExtend V X Y ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState))
    (hquadPositive : 1 ≤ stateQuadraticDefectRank V)
    (alpha beta : Fin 4 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hab : alpha ≠ beta)
    (hXcolour : Submodule.mkQ (N4.quadraticANFSpace 10) X =
      colourHighCombination alpha)
    (hYcolour : Submodule.mkQ (N4.quadraticANFSpace 10) Y =
      colourHighCombination beta)
    (hproductColour :
      Submodule.mkQ (N4.quadraticANFSpace 10) (X * Y) =
        Submodule.mkQ (N4.quadraticANFSpace 10)
          (colourCombination alpha * colourCombination beta)) : False := by
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
              (Submodule.mkQ (N4.quadraticANFSpace 10) Y))) :=
    linearIndependent_finSnoc.mp (by
      simpa [highTripleDirections] using hbirthXY)
  exact rankTwo_escape_impossible_of_positive_quadraticDefect
    V X Y hX hY hdef hold hescape hquadPositive hsplit.1 hsplit.2

end
end N5
end UnrestrictedBooleanMul
