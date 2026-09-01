import UnrestrictedBooleanMul.N5.LocalSecantPivots

/-!
# Principal degree-two local secant pivot

The three algebraic Pfaffian certificates on the q₂ = 1 chart are kept
in a separate module so Lean can release their elaboration state before
checking the remaining degree-two charts.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-! ## Degree-two local secant equations -/

/-- The principal degree-two effectiveness chart, retaining both possible
same-side coefficients.  Effectiveness on this chart is the single equation
`q0*q3=0`. -/
def degreeEffectiveQ2 (q0 q1 q3 : F₂) : LocalKleinParam :=
  ![q0, q1, 1, q3]

set_option maxRecDepth 10000 in
/-- First degree-two secant pivot on the `q₂=1` chart. -/
theorem degreeQ2_secant_constraint_zero_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) (hq : q0 * q3 = 0) :
    c 1 + c 2 + c 4 + c 5 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveQ2 q0 q1 q3) c i j k l m n
      E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 7 +
      c 4 * E 0 1 2 5 6 7 +
      c 6 * E 0 1 2 5 6 7 +
      c 7 * E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 8 +
      c 3 * E 0 1 2 5 6 8 +
      q1 * E 0 1 2 5 6 9 +
      E 0 1 2 5 7 8 +
      c 2 * E 0 1 2 5 7 8 +
      c 2 * E 0 1 2 5 7 9 +
      c 3 * E 0 1 2 5 8 9 +
      c 3 * E 0 1 2 6 7 8 +
      c 3 * E 0 1 2 6 7 9 +
      E 0 1 2 6 8 9 +
      c 2 * E 0 1 2 6 8 9 +
      c 4 * E 0 1 2 6 8 9 +
      c 0 * E 0 1 2 7 8 9 +
      c 2 * E 0 1 3 5 6 7 +
      c 4 * E 0 1 3 5 6 7 +
      c 6 * E 0 1 3 5 6 7 +
      q1 * E 0 1 3 5 6 8 +
      E 0 1 3 5 6 9 +
      c 2 * E 0 1 3 5 6 9 +
      E 0 1 3 5 7 8 +
      c 2 * E 0 1 3 5 7 8 +
      E 0 1 3 5 7 9 +
      E 0 1 3 5 8 9 +
      c 3 * E 0 1 3 6 7 9 +
      E 0 1 3 6 8 9 +
      q1 * E 0 1 3 6 8 9 +
      c 3 * E 0 1 3 6 8 9 +
      c 0 * E 0 1 3 7 8 9 +
      E 0 2 3 5 6 8 +
      E 0 2 3 5 7 8 +
      c 3 * E 0 2 3 5 7 8 +
      c 3 * E 0 2 4 6 7 8 +
      E 1 2 3 6 7 8 := by
  rcases mul_eq_zero.mp hq with hq0 | hq3
  · subst q0
    simp [normalizedLocalSecantEquation, secantPfaffianValue,
      ambientTwoCoeff,
      closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
      targetTwo_pair_eq_explicitTargetCoeff,
      explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
      explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
      degreeEffectiveQ2, localKleinPair, Fin.sum_univ_succ]
    ring_nf
    simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
      secant_pow_four_f2]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, secant_five_eq_one_f2,
      secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
      secant_thirteen_eq_one_f2,
      secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
      secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
      secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
      secant_twenty_eight_eq_zero_f2]
  · subst q3
    simp [normalizedLocalSecantEquation, secantPfaffianValue,
      ambientTwoCoeff,
      closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
      targetTwo_pair_eq_explicitTargetCoeff,
      explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
      explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
      degreeEffectiveQ2, localKleinPair, Fin.sum_univ_succ]
    ring_nf
    simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
      secant_pow_four_f2]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, secant_five_eq_one_f2,
      secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
      secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
      secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
      secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
      secant_twenty_eight_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- Second degree-two secant pivot on the `q₂=1` chart. -/
theorem degreeQ2_secant_constraint_one_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) (hq : q0 * q3 = 0) :
    c 1 + c 3 + c 4 + c 6 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveQ2 q0 q1 q3) c i j k l m n
      c 2 * E 0 1 2 5 6 7 +
      c 3 * E 0 1 2 5 6 7 +
      c 4 * E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 8 +
      E 0 1 2 5 6 9 +
      c 4 * E 0 1 2 5 6 9 +
      c 5 * E 0 1 2 5 6 9 +
      c 7 * E 0 1 2 5 6 9 +
      c 2 * E 0 1 2 5 7 8 +
      c 5 * E 0 1 2 5 7 8 +
      c 6 * E 0 1 2 5 7 9 +
      c 7 * E 0 1 2 5 7 9 +
      c 2 * E 0 1 2 5 8 9 +
      c 3 * E 0 1 2 5 8 9 +
      E 0 1 2 6 7 8 +
      c 4 * E 0 1 2 6 7 8 +
      c 6 * E 0 1 2 6 7 9 +
      c 7 * E 0 1 2 6 7 9 +
      c 5 * E 0 1 2 6 8 9 +
      c 6 * E 0 1 2 6 8 9 +
      c 3 * E 0 1 3 5 6 7 +
      E 0 1 3 5 6 8 +
      q1 * E 0 1 3 5 6 8 +
      c 2 * E 0 1 3 5 6 8 +
      c 5 * E 0 1 3 5 6 8 +
      c 7 * E 0 1 3 5 6 8 +
      E 0 1 3 5 6 9 +
      q1 * E 0 1 3 5 7 8 +
      c 3 * E 0 1 3 5 7 8 +
      c 6 * E 0 1 3 5 7 8 +
      c 7 * E 0 1 3 5 7 8 +
      c 7 * E 0 1 3 5 7 9 +
      c 4 * E 0 1 3 5 8 9 +
      c 7 * E 0 1 3 6 7 8 +
      q1 * E 0 1 3 6 7 9 +
      c 1 * E 0 1 3 6 7 9 +
      c 5 * E 0 1 3 6 7 9 +
      c 7 * E 0 1 3 6 7 9 +
      q1 * E 0 1 3 6 8 9 +
      c 5 * E 0 1 3 6 8 9 +
      c 6 * E 0 1 3 6 8 9 +
      c 7 * E 0 1 3 6 8 9 +
      c 6 * E 0 1 3 7 8 9 +
      E 0 1 4 5 7 8 +
      E 0 1 4 6 7 8 +
      c 5 * E 0 2 3 5 6 9 +
      c 3 * E 0 2 3 5 7 8 +
      E 0 2 3 5 7 9 +
      E 0 2 3 5 8 9 +
      c 6 * E 0 2 3 6 7 9 +
      c 7 * E 0 2 3 6 7 9 +
      E 0 2 3 6 8 9 +
      c 6 * E 1 2 3 6 7 8 +
      c 7 * E 1 2 3 6 7 8 +
      E 1 2 3 6 8 9 := by
  rcases mul_eq_zero.mp hq with hq0 | hq3 <;> subst_vars
  all_goals
    simp [normalizedLocalSecantEquation, secantPfaffianValue,
      ambientTwoCoeff,
      closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
      targetTwo_pair_eq_explicitTargetCoeff,
      explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
      explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
      degreeEffectiveQ2, localKleinPair, Fin.sum_univ_succ]
    ring_nf
    simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
      secant_pow_four_f2]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, secant_five_eq_one_f2,
      secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
      secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
      secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
      secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
      secant_twenty_eight_eq_zero_f2]
    simpa [secant_three_eq_one_f2, secant_thirteen_eq_one_f2,
      secant_thirty_eq_zero_f2, secant_thirty_two_eq_zero_f2,
      secant_forty_eq_zero_f2, secant_forty_four_eq_zero_f2,
      secant_fifty_two_eq_zero_f2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Third degree-two secant pivot on the `q₂=1` chart. -/
theorem degreeQ2_secant_constraint_two_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) (hq : q0 * q3 = 0) :
    c 1 + c 7 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveQ2 q0 q1 q3) c i j k l m n
      E 0 1 2 5 6 7 +
      q1 * E 0 1 2 5 6 7 +
      c 3 * E 0 1 2 5 6 7 +
      E 0 1 2 5 6 8 +
      c 8 * E 0 1 2 5 6 8 +
      c 2 * E 0 1 2 5 7 8 +
      c 3 * E 0 1 2 5 7 8 +
      c 6 * E 0 1 2 5 7 8 +
      c 2 * E 0 1 2 5 7 9 +
      c 7 * E 0 1 2 5 7 9 +
      c 2 * E 0 1 2 5 8 9 +
      c 6 * E 0 1 2 5 8 9 +
      q1 * E 0 1 2 6 7 8 +
      c 4 * E 0 1 2 6 7 8 +
      c 1 * E 0 1 2 6 7 9 +
      c 2 * E 0 1 2 6 7 9 +
      c 5 * E 0 1 2 6 7 9 +
      c 8 * E 0 1 2 6 7 9 +
      E 0 1 2 6 8 9 +
      c 3 * E 0 1 2 6 8 9 +
      c 5 * E 0 1 2 6 8 9 +
      c 6 * E 0 1 2 6 8 9 +
      c 2 * E 0 1 3 5 6 7 +
      c 3 * E 0 1 3 5 6 7 +
      c 4 * E 0 1 3 5 6 7 +
      c 8 * E 0 1 3 5 6 7 +
      c 3 * E 0 1 3 5 6 8 +
      c 4 * E 0 1 3 5 6 8 +
      c 8 * E 0 1 3 5 6 8 +
      c 5 * E 0 1 3 5 6 9 +
      c 7 * E 0 1 3 5 6 9 +
      c 6 * E 0 1 3 5 7 8 +
      E 0 1 3 5 7 9 +
      c 3 * E 0 1 3 5 7 9 +
      c 4 * E 0 1 3 5 8 9 +
      c 5 * E 0 1 3 5 8 9 +
      c 6 * E 0 1 3 5 8 9 +
      c 8 * E 0 1 3 5 8 9 +
      E 0 1 3 6 7 8 +
      c 8 * E 0 1 3 6 7 8 +
      q1 * E 0 1 3 6 7 9 +
      c 2 * E 0 1 3 6 7 9 +
      c 5 * E 0 1 3 6 7 9 +
      c 7 * E 0 1 3 6 7 9 +
      E 0 1 3 6 8 9 +
      q1 * E 0 1 3 6 8 9 +
      c 7 * E 0 1 3 6 8 9 +
      c 4 * E 0 1 3 7 8 9 +
      c 6 * E 0 1 3 7 8 9 +
      c 8 * E 0 1 3 7 8 9 +
      c 2 * E 0 1 4 5 6 9 +
      c 4 * E 0 1 4 5 6 9 +
      c 6 * E 0 1 4 5 6 9 +
      c 8 * E 0 1 4 5 6 9 +
      E 0 1 4 5 7 9 +
      c 3 * E 0 1 4 5 7 9 +
      c 6 * E 0 1 4 5 7 9 +
      c 2 * E 0 1 4 5 8 9 +
      c 3 * E 0 1 4 5 8 9 +
      c 8 * E 0 1 4 5 8 9 +
      c 7 * E 0 1 4 6 7 9 +
      c 8 * E 0 1 4 6 7 9 +
      c 7 * E 0 1 4 7 8 9 +
      q1 * E 0 2 3 5 6 7 +
      c 7 * E 0 2 3 5 6 8 +
      c 7 * E 0 2 3 5 6 9 +
      c 8 * E 0 2 3 5 7 9 +
      E 0 2 3 5 8 9 +
      c 3 * E 0 2 3 5 8 9 +
      c 7 * E 0 2 3 5 8 9 +
      c 7 * E 0 2 3 6 7 9 +
      c 6 * E 0 2 3 6 8 9 +
      c 7 * E 0 2 3 6 8 9 +
      c 7 * E 0 2 3 7 8 9 +
      c 6 * E 0 2 4 5 6 9 +
      c 3 * E 0 2 4 5 7 9 +
      c 8 * E 0 2 4 6 7 9 +
      c 8 * E 0 3 4 5 7 8 +
      E 0 3 4 5 8 9 +
      E 0 3 4 6 8 9 +
      E 1 2 3 5 7 8 +
      c 8 * E 1 2 3 5 7 8 +
      c 1 * E 1 2 3 5 8 9 +
      E 1 2 3 6 7 8 +
      c 8 * E 1 2 3 6 7 8 +
      c 4 * E 1 2 4 5 7 8 +
      c 8 * E 1 2 4 5 7 8 +
      E 1 2 4 6 7 8 +
      c 8 * E 1 2 4 6 7 9 +
      E 1 3 4 6 8 9 +
      c 7 * E 2 3 4 5 6 7 := by
  rcases mul_eq_zero.mp hq with hq0 | hq3 <;> subst_vars
  all_goals
    simp [normalizedLocalSecantEquation, secantPfaffianValue,
      ambientTwoCoeff,
      closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
      targetTwo_pair_eq_explicitTargetCoeff,
      explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
      explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
      degreeEffectiveQ2, localKleinPair, Fin.sum_univ_succ]
    ring_nf
    simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
      secant_pow_four_f2]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, secant_five_eq_one_f2,
      secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
      secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
      secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
      secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
      secant_twenty_eight_eq_zero_f2]
    simpa [secant_three_eq_one_f2, secant_thirteen_eq_one_f2,
      secant_thirty_eq_zero_f2, secant_thirty_two_eq_zero_f2,
      secant_forty_eq_zero_f2, secant_forty_four_eq_zero_f2,
      secant_fifty_two_eq_zero_f2]

/-- On the principal degree-two chart, every normalized two-wedge
presentation satisfies the three defining norm-block constraints. -/
theorem degreeQ2_normalizedLocalSecant_mem
    (q0 q1 q3 : F₂) (c : TargetCoeff) (hq : q0 * q3 = 0)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift 3 (degreeEffectiveQ2 q0 q1 q3) + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ degreeTwoSecantCoeffSpace := by
  have hE (i j k l m n : Fin 10) :
      normalizedLocalSecantEquation 3
        (degreeEffectiveQ2 q0 q1 q3) c i j k l m n = 0 :=
    normalizedLocalSecantEquation_eq_zero 3
      (degreeEffectiveQ2 q0 q1 q3) c i j k l m n hsecant
  change degreeTwoSecantConstraint c = 0
  ext t
  fin_cases t
  · change c 1 + c 2 + c 4 + c 5 = 0
    have hid := degreeQ2_secant_constraint_zero_identity q0 q1 q3 c hq
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 1 + c 3 + c 4 + c 6 = 0
    have hid := degreeQ2_secant_constraint_one_identity q0 q1 q3 c hq
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 1 + c 7 = 0
    have hid := degreeQ2_secant_constraint_two_identity q0 q1 q3 c hq
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid


end

end N5
end UnrestrictedBooleanMul

