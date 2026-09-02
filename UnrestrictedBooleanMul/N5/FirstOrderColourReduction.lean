import UnrestrictedBooleanMul.N5.FirstOrderAnchorState
import UnrestrictedBooleanMul.N5.FirstOrderEscapeBudget
import UnrestrictedBooleanMul.N5.ColourCases
import UnrestrictedBooleanMul.N5.RankOneCircuitEscape
import UnrestrictedBooleanMul.N5.RankOneEnvelopeCorrection

/-!
# Reduction of first-order saturation to the three factor-colour branches

This module follows the proof order of manuscript Theorem 12.3.  At a first
target escape, the two factor classes modulo quadratic ANFs have rank zero,
one, or two.  The three branch predicates below retain the actual suffix
state and the global defect bound; their conjunction is sufficient for the
canonical anchored-state stability theorem.

The rank-one branch is reduced further to the exact localization data
consumed by the checked target-clean absorption contradiction.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private abbrev HighQuotient :=
  (ANF 10) ⧸ N4.quadraticANFSpace 10

/-- No target escape is possible when both factors have zero literal high
class.  This is the zero-colour branch of Theorem 12.3. -/
def ZeroColourStepClosed (q : TwoForm) : Prop :=
  ∀ V X Y,
    DefectLegalSuffix (firstOrderAnchorState q) V →
    X ∈ V → Y ∈ V →
    N4.flagDefectRank (andExtend V X Y) (mulTarget 5) ≤ 3 →
    V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState →
    X ∈ N4.quadraticANFSpace 10 →
    Y ∈ N4.quadraticANFSpace 10 →
    andExtend V X Y ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState

/-- No target escape is possible when the two factor high classes span one
nonzero line.  The equal-colour case remains explicit through
`RankOneColourPattern`. -/
def RankOneColourStepClosed (q : TwoForm) : Prop :=
  ∀ V X Y (g : HighQuotient),
    DefectLegalSuffix (firstOrderAnchorState q) V →
    X ∈ V → Y ∈ V →
    N4.flagDefectRank (andExtend V X Y) (mulTarget 5) ≤ 3 →
    V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState →
    g ≠ 0 →
    RankOneColourPattern
      (Submodule.mkQ (N4.quadraticANFSpace 10)) g X Y →
    andExtend V X Y ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState

/-- No target escape is possible when the two factor high classes are
linearly independent.  This is the rank-two/old-product-colour branch. -/
def RankTwoColourStepClosed (q : TwoForm) : Prop :=
  ∀ V X Y,
    DefectLegalSuffix (firstOrderAnchorState q) V →
    X ∈ V → Y ∈ V →
    N4.flagDefectRank (andExtend V X Y) (mulTarget 5) ≤ 3 →
    V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState →
    LinearIndependent F₂
      (pairDirections
        (Submodule.mkQ (N4.quadraticANFSpace 10) X)
        (Submodule.mkQ (N4.quadraticANFSpace 10) Y)) →
    andExtend V X Y ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState

/-- The exact extra localization needed after the already checked rank-one
normalization: the old quadratic factor lies in the target-clean second-jet
space plus the anchor direction, and the remaining correction lies in the
first-order target envelope. -/
def RankOneEscapeLocalized (q : TwoForm) : Prop :=
  ∀ V X Y (g : HighQuotient),
    DefectLegalSuffix (firstOrderAnchorState q) V →
    X ∈ V → Y ∈ V →
    N4.flagDefectRank (andExtend V X Y) (mulTarget 5) ≤ 3 →
    V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ firstOrderEnvelopeState →
    g ≠ 0 →
    RankOneColourPattern
      (Submodule.mkQ (N4.quadraticANFSpace 10)) g X Y →
    ¬ (andExtend V X Y ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState) →
    ∃ (U c : ANF 10) (a : F₂) (ell : LinearForm)
        (u : TargetCoeff) (v : ANF 10),
      U ∈ V ∧ U ∉ N4.quadraticANFSpace 10 ∧
      c ∈ V ∧ c ∈ N4.quadraticANFSpace 10 ∧
      u ∈ firstOrderEnvelopeCoeffSpace ∧
      v ∈ firstOrderEnvelopeState ∧
      andExtend V U c = andExtend V X Y ∧
      U * (U * c) = U * c ∧ (U * c) * c = U * c ∧
      U * c = quadraticCoordinateANF a ell
        (targetTwo (firstOrderMissingCoeff + u)) + v ∧
      quadraticProjection 10 c ∈
        targetCleanSecondJetSpace ⊔
          Submodule.span F₂ ({q} : Set TwoForm)

/-- The target-clean terminal contradiction closes the entire rank-one branch
once the preceding localization statement is available. -/
theorem rankOneColourStepClosed_of_localized
    (q : TwoForm) (hqdec : IsDecomposableTwo q)
    (hloc : RankOneEscapeLocalized q) :
    RankOneColourStepClosed q := by
  intro V X Y g hreach hX hY hdef hold hg hpattern
  by_contra hescape
  rcases hloc V X Y g hreach hX hY hdef hold hg hpattern hescape with
    ⟨U, c, a, ell, u, v, _hUV, hUhigh, _hcV, hcquad, hu, hv,
      _hextend, _hleft, habsorb, hproduct, hclean⟩
  exact rankOne_envelopeCorrected_escape_impossible
    U c hUhigh hcquad a ell u hu q hqdec hclean v hv hproduct habsorb

/-- The three colour branches imply one-step closure of the first-order
target envelope above a canonical anchored base. -/
theorem targetStepClosed_firstOrderAnchor_of_colourBranches
    (q : TwoForm)
    (hzero : ZeroColourStepClosed q)
    (hone : RankOneColourStepClosed q)
    (htwo : RankTwoColourStepClosed q) :
    TargetStepClosed (firstOrderAnchorState q) firstOrderEnvelopeState := by
  intro V X Y hreach hX hY hdef hold
  rw [sup_eq_right.mpr affine_le_firstOrderEnvelopeState] at hold ⊢
  rcases highQuotient_factor_trichotomy X Y with
    hquadratic | hrankOne | hrankTwo
  · exact hzero V X Y hreach hX hY hdef hold
      hquadratic.1 hquadratic.2
  · rcases hrankOne with ⟨g, hg, hpattern⟩
    exact hone V X Y g hreach hX hY hdef hold hg hpattern
  · exact htwo V X Y hreach hX hY hdef hold hrankTwo

/-- Canonical anchored-state stability follows from the three algebraic
factor-colour branches. -/
theorem stableFirstOrderAnchor_of_colourBranches
    (q : TwoForm) (hqdec : IsDecomposableTwo q)
    (hzero : ZeroColourStepClosed q)
    (hone : RankOneColourStepClosed q)
    (htwo : RankTwoColourStepClosed q) :
    StableTargetSubspace (firstOrderAnchorState q)
      firstOrderEnvelopeState := by
  apply stableTargetSubspace_of_targetStepClosed
  · exact (firstOrderAnchorState_inf_targetAmbient_le_firstOrderEnvelopeState
      q hqdec).trans le_sup_right
  · exact targetStepClosed_firstOrderAnchor_of_colourBranches
      q hzero hone htwo

end
end N5
end UnrestrictedBooleanMul
