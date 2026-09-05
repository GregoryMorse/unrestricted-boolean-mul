import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnSymmetry

/-!
# Simultaneous rational factor-pair classification

The nonzero rational rank-one quadratic directions form the three points of
`P¹(F₂)`.  Swapping the two factors and applying one rational-place
coordinate change reduces every nonzero ordered pair of rank-one-or-zero
directions to `(0,1)`, `(1,1)`, or `(1,2)`.  The separate `(1,3)` chart has
rank-two right colour `r0 + r1`; it is deliberately not confused with the
third rank-one point `r∞`.  This is a finite algebraic classification of
quadratic forms; it does not enumerate circuits or Boolean functions.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Zero together with the three rational rank-one directions. -/
inductive RationalOrZeroDirection where
  | zero
  | rZero
  | rOne
  | rInfinity
  deriving DecidableEq

def RationalOrZeroDirection.two : RationalOrZeroDirection → TwoForm
  | .zero => 0
  | .rZero => targetTwo rZeroCoeff
  | .rOne => targetTwo rOneCoeff
  | .rInfinity => targetTwo rInfinityCoeff

/-- Whether the two factors are retained in order or exchanged. -/
inductive FactorPairOrder where
  | direct
  | swapped
  deriving DecidableEq

def FactorPairOrder.leftTwo (order : FactorPairOrder)
    (q c : TwoForm) : TwoForm :=
  match order with
  | .direct => q
  | .swapped => c

def FactorPairOrder.rightTwo (order : FactorPairOrder)
    (q c : TwoForm) : TwoForm :=
  match order with
  | .direct => c
  | .swapped => q

/-- Data witnessing reduction of a rational factor pair to one checked
history chart. -/
structure RationalFactorPairNormalization
    (q c : TwoForm) where
  order : FactorPairOrder
  word : RationalPlaceWord
  kind : MixedReturnFactorPair
  left_eq : word.twoForm (order.leftTwo q c) = kind.leftTwo
  right_eq : word.twoForm (order.rightTwo q c) = kind.rightTwo

local macro "close_rational_factor_pair" : tactic =>
  `(tactic|
    simp [RationalOrZeroDirection.two, FactorPairOrder.leftTwo,
      FactorPairOrder.rightTwo, RationalPlaceWord.twoForm,
      MixedReturnFactorPair.leftTwo, MixedReturnFactorPair.rightTwo,
      rationalPlaceTwoFormLinear_targetTwo, rationalTargetCoeffChange,
      rZeroCoeff, rOneCoeff, rInfinityCoeff] <;> ring_nf <;>
      simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2,
        N3Certificate.eight_eq_zero_f2])

/-- Every pair containing a nonzero rational rank-one direction has one of
the rank-one simultaneous normal forms used by the return-history chart. -/
def rationalFactorPairNormalization
    (q c : RationalOrZeroDirection)
    (hnonzero : q ≠ .zero ∨ c ≠ .zero) :
    RationalFactorPairNormalization q.two c.two := by
  cases q <;> cases c
  · simp at hnonzero
  · exact ⟨.direct, .identity, .zeroOne, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .translation, .zeroOne, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .reversal, .zeroOne, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.swapped, .identity, .zeroOne, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .identity, .oneOneDifference, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .identity, .oneTwo, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .translationReversalTranslation, .oneTwo, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.swapped, .translation, .zeroOne, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .translation, .oneTwo, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .translation, .oneOneDifference, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .translationReversal, .oneTwo, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.swapped, .reversal, .zeroOne, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .reversalTranslation, .oneTwo, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .reversal, .oneTwo, by
      close_rational_factor_pair, by close_rational_factor_pair⟩
  · exact ⟨.direct, .reversal, .oneOneDifference, by
      close_rational_factor_pair, by close_rational_factor_pair⟩

/-- A nonzero rational rank-one colour, with no artificial ordering of the
three rational places. -/
inductive RationalRankOneDirection where
  | rZero
  | rOne
  | rInfinity
  deriving DecidableEq

def RationalRankOneDirection.two : RationalRankOneDirection → TwoForm
  | .rZero => targetTwo rZeroCoeff
  | .rOne => targetTwo rOneCoeff
  | .rInfinity => targetTwo rInfinityCoeff

/-- An ordered pair of distinct rational rank-one colours. -/
structure DistinctRationalDirections where
  left : RationalRankOneDirection
  right : RationalRankOneDirection
  ne : left ≠ right

/-- The factor-colour pairs that occur in the four rational return charts.
The incident constructors retain the rank-two colour `left + right`; this is
the source of the genuine `(1,3)` chart. -/
inductive AdmissibleRationalFactorPair where
  | zeroLeft (r : RationalRankOneDirection)
  | zeroRight (r : RationalRankOneDirection)
  | equal (r : RationalRankOneDirection)
  | distinct (p : DistinctRationalDirections)
  | incidentRight (p : DistinctRationalDirections)
  | incidentLeft (p : DistinctRationalDirections)

def AdmissibleRationalFactorPair.leftTwo :
    AdmissibleRationalFactorPair → TwoForm
  | .zeroLeft _ => 0
  | .zeroRight r => r.two
  | .equal r => r.two
  | .distinct p => p.left.two
  | .incidentRight p => p.left.two
  | .incidentLeft p => p.left.two + p.right.two

def AdmissibleRationalFactorPair.rightTwo :
    AdmissibleRationalFactorPair → TwoForm
  | .zeroLeft r => r.two
  | .zeroRight _ => 0
  | .equal r => r.two
  | .distinct p => p.right.two
  | .incidentRight p => p.left.two + p.right.two
  | .incidentLeft p => p.left.two

def RationalRankOneDirection.normalizationWord :
    RationalRankOneDirection → RationalPlaceWord
  | .rZero => .identity
  | .rOne => .translation
  | .rInfinity => .reversal

theorem RationalRankOneDirection.normalizationWord_two
    (r : RationalRankOneDirection) :
    r.normalizationWord.twoForm r.two = targetTwo rZeroCoeff := by
  cases r <;>
    simp [RationalRankOneDirection.normalizationWord,
      RationalRankOneDirection.two, RationalPlaceWord.twoForm,
      rationalPlaceTwoFormLinear_targetTwo, rationalTargetCoeffChange,
      rZeroCoeff, rOneCoeff, rInfinityCoeff] <;>
    ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2]

def DistinctRationalDirections.normalizationWord
    (p : DistinctRationalDirections) : RationalPlaceWord :=
  match p.left, p.right with
  | .rZero, .rOne => .identity
  | .rZero, .rInfinity => .translationReversalTranslation
  | .rOne, .rZero => .translation
  | .rOne, .rInfinity => .translationReversal
  | .rInfinity, .rZero => .reversalTranslation
  | .rInfinity, .rOne => .reversal
  | _, _ => .identity

local macro "close_distinct_rational_pair" : tactic =>
  `(tactic|
    simp [RationalRankOneDirection.two,
      DistinctRationalDirections.normalizationWord,
      RationalPlaceWord.twoForm,
      rationalPlaceTwoFormLinear_targetTwo, rationalTargetCoeffChange,
      rZeroCoeff, rOneCoeff, rInfinityCoeff] <;> ring_nf <;>
      simp [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2,
        N3Certificate.eight_eq_zero_f2])

theorem DistinctRationalDirections.normalizationWord_left
    (p : DistinctRationalDirections) :
    p.normalizationWord.twoForm p.left.two = targetTwo rZeroCoeff := by
  rcases p with ⟨left, right, hne⟩
  cases left <;> cases right
  · simp at hne
  · close_distinct_rational_pair
  · close_distinct_rational_pair
  · close_distinct_rational_pair
  · simp at hne
  · close_distinct_rational_pair
  · close_distinct_rational_pair
  · close_distinct_rational_pair
  · simp at hne

theorem DistinctRationalDirections.normalizationWord_right
    (p : DistinctRationalDirections) :
    p.normalizationWord.twoForm p.right.two = targetTwo rOneCoeff := by
  rcases p with ⟨left, right, hne⟩
  cases left <;> cases right
  · simp at hne
  · close_distinct_rational_pair
  · close_distinct_rational_pair
  · close_distinct_rational_pair
  · simp at hne
  · close_distinct_rational_pair
  · close_distinct_rational_pair
  · close_distinct_rational_pair
  · simp at hne

@[simp] theorem RationalPlaceWord.twoForm_add
    (word : RationalPlaceWord) (q c : TwoForm) :
    word.twoForm (q + c) = word.twoForm q + word.twoForm c := by
  cases word <;> simp [RationalPlaceWord.twoForm, map_add]

@[simp] theorem RationalPlaceWord.twoForm_zero
    (word : RationalPlaceWord) : word.twoForm 0 = 0 := by
  cases word <;> simp [RationalPlaceWord.twoForm, map_zero]

/-- Exact finite classification of every admissible rational factor-colour
pair into the four history charts.  The theorem acts only on quadratic forms;
it performs no circuit or truth-table enumeration. -/
def AdmissibleRationalFactorPair.normalization
    (pair : AdmissibleRationalFactorPair) :
    RationalFactorPairNormalization pair.leftTwo pair.rightTwo := by
  cases pair with
  | zeroLeft r =>
      exact ⟨.direct, r.normalizationWord, .zeroOne,
        by change r.normalizationWord.twoForm 0 = 0; simp,
        by change r.normalizationWord.twoForm r.two = targetTwo rZeroCoeff
           exact r.normalizationWord_two⟩
  | zeroRight r =>
      exact ⟨.swapped, r.normalizationWord, .zeroOne,
        by change r.normalizationWord.twoForm 0 = 0; simp,
        by change r.normalizationWord.twoForm r.two = targetTwo rZeroCoeff
           exact r.normalizationWord_two⟩
  | equal r =>
      exact ⟨.direct, r.normalizationWord, .oneOneDifference,
        by change r.normalizationWord.twoForm r.two = targetTwo rZeroCoeff
           exact r.normalizationWord_two,
        by change r.normalizationWord.twoForm r.two = targetTwo rZeroCoeff
           exact r.normalizationWord_two⟩
  | distinct p =>
      exact ⟨.direct, p.normalizationWord, .oneTwo,
        by change p.normalizationWord.twoForm p.left.two = targetTwo rZeroCoeff
           exact p.normalizationWord_left,
        by change p.normalizationWord.twoForm p.right.two = targetTwo rOneCoeff
           exact p.normalizationWord_right⟩
  | incidentRight p =>
      exact ⟨.direct, p.normalizationWord, .oneThree,
        by change p.normalizationWord.twoForm p.left.two = targetTwo rZeroCoeff
           exact p.normalizationWord_left,
        by
          change p.normalizationWord.twoForm (p.left.two + p.right.two) =
            targetTwo (rZeroCoeff + rOneCoeff)
          rw [RationalPlaceWord.twoForm_add,
            p.normalizationWord_left, p.normalizationWord_right]
          exact (targetTwoLinear.map_add _ _).symm⟩
  | incidentLeft p =>
      exact ⟨.swapped, p.normalizationWord, .oneThree,
        by change p.normalizationWord.twoForm p.left.two = targetTwo rZeroCoeff
           exact p.normalizationWord_left,
        by
          change p.normalizationWord.twoForm (p.left.two + p.right.two) =
            targetTwo (rZeroCoeff + rOneCoeff)
          rw [RationalPlaceWord.twoForm_add,
            p.normalizationWord_left, p.normalizationWord_right]
          exact (targetTwoLinear.map_add _ _).symm⟩

end
end N5
end UnrestrictedBooleanMul
