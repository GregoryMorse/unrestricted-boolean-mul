import UnrestrictedBooleanMul.N5.DegreeTwoSecantQ2

/-!
# Remaining degree-two local secant pivots

The D chart and exceptional G parameter complete the algebraic
classification, after which the normalized result is returned to the
original affine local-secant coordinates.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxRecDepth 10000 in
/-- First degree-two secant pivot on the `q₁=1,q₂=0` chart. -/
theorem degreeD_secant_constraint_zero_identity
    (q0 q3 : F₂) (c : TargetCoeff) :
    c 1 + c 2 + c 4 + c 5 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveD q0 q3) c i j k l m n
      c 4 * E 0 1 2 5 6 7 +
      c 6 * E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 8 +
      c 4 * E 0 1 2 5 6 8 +
      c 1 * E 0 1 2 5 6 9 +
      c 3 * E 0 1 2 5 6 9 +
      c 4 * E 0 1 2 5 6 9 +
      c 1 * E 0 1 2 5 7 8 +
      c 3 * E 0 1 2 5 7 8 +
      c 4 * E 0 1 2 5 7 8 +
      E 0 1 2 5 7 9 +
      c 2 * E 0 1 2 5 7 9 +
      c 6 * E 0 1 2 5 7 9 +
      E 0 1 2 5 8 9 +
      c 0 * E 0 1 2 5 8 9 +
      c 4 * E 0 1 2 5 8 9 +
      c 5 * E 0 1 2 5 8 9 +
      c 0 * E 0 1 2 6 7 9 +
      c 4 * E 0 1 2 6 7 9 +
      c 4 * E 0 1 2 6 8 9 +
      E 0 1 4 5 6 7 +
      c 0 * E 0 2 3 5 6 8 +
      c 0 * E 1 2 3 5 6 7 +
      E 1 2 3 5 7 8 +
      c 5 * E 1 2 4 5 6 7 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    degreeEffectiveD, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, secant_three_eq_one_f2,
    secant_nine_eq_one_f2,
    secant_five_eq_one_f2, secant_ten_eq_zero_f2,
    secant_twelve_eq_zero_f2, secant_thirteen_eq_one_f2,
    secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
    secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
    secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
    secant_twenty_eight_eq_zero_f2, secant_thirty_eq_zero_f2,
    secant_thirty_two_eq_zero_f2, secant_thirty_six_eq_zero_f2,
    secant_forty_eq_zero_f2,
    secant_forty_four_eq_zero_f2, secant_fifty_two_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- Second degree-two secant pivot on the `q₁=1,q₂=0` chart. -/
theorem degreeD_secant_constraint_one_identity
    (q0 q3 : F₂) (c : TargetCoeff) :
    c 1 + c 3 + c 4 + c 6 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveD q0 q3) c i j k l m n
      q3 * E 0 1 2 3 5 7 +
      q3 * E 0 1 2 3 6 8 +
      q3 * E 0 1 2 4 7 8 +
      E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 7 +
      c 5 * E 0 1 2 5 6 7 +
      c 3 * E 0 1 2 5 6 9 +
      c 2 * E 0 1 2 5 7 8 +
      c 7 * E 0 1 2 5 7 8 +
      c 1 * E 0 1 2 5 7 9 +
      c 6 * E 0 1 2 5 7 9 +
      c 7 * E 0 1 2 5 7 9 +
      c 1 * E 0 1 2 5 8 9 +
      c 6 * E 0 1 2 5 8 9 +
      c 7 * E 0 1 2 6 7 8 +
      c 5 * E 0 1 2 6 7 9 +
      E 0 1 2 6 8 9 +
      c 5 * E 0 1 2 6 8 9 +
      c 6 * E 0 1 2 6 8 9 +
      c 7 * E 0 1 2 6 8 9 +
      c 5 * E 0 1 2 7 8 9 +
      c 3 * E 0 1 3 5 6 7 +
      c 4 * E 0 1 3 5 6 7 +
      E 0 1 3 5 6 9 +
      c 1 * E 0 1 3 5 6 9 +
      c 6 * E 0 1 3 5 6 9 +
      E 0 1 3 5 7 9 +
      c 1 * E 0 1 3 5 7 9 +
      c 7 * E 0 1 3 5 7 9 +
      E 0 1 3 5 8 9 +
      c 0 * E 0 1 3 5 8 9 +
      c 7 * E 0 1 3 5 8 9 +
      c 5 * E 0 1 3 6 8 9 +
      c 6 * E 0 1 3 6 8 9 +
      c 3 * E 0 1 4 5 6 7 +
      c 7 * E 0 1 4 5 6 7 +
      E 0 2 3 5 6 8 +
      c 7 * E 0 2 3 5 6 8 +
      E 0 2 3 5 6 9 +
      c 0 * E 0 2 3 5 6 9 +
      c 6 * E 0 2 3 5 8 9 +
      E 0 2 3 6 8 9 +
      E 0 2 4 5 7 8 +
      c 6 * E 1 2 3 5 7 8 +
      c 7 * E 1 2 3 5 7 8 +
      E 1 2 3 5 8 9 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    degreeEffectiveD, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, secant_three_eq_one_f2,
    secant_nine_eq_one_f2, secant_five_eq_one_f2,
    secant_seven_eq_one_f2,
    secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
    secant_thirteen_eq_one_f2, secant_fourteen_eq_zero_f2,
    secant_sixteen_eq_zero_f2, secant_eighteen_eq_zero_f2,
    secant_twenty_eq_zero_f2, secant_twenty_two_eq_zero_f2,
    secant_twenty_four_eq_zero_f2, secant_twenty_six_eq_zero_f2,
    secant_twenty_eight_eq_zero_f2,
    secant_thirty_eq_zero_f2, secant_thirty_two_eq_zero_f2,
    secant_forty_eq_zero_f2, secant_forty_four_eq_zero_f2,
    secant_fifty_two_eq_zero_f2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Third degree-two secant pivot on the `q₁=1,q₂=0` chart. -/
theorem degreeD_secant_constraint_two_identity
    (q0 q3 : F₂) (c : TargetCoeff) :
    c 1 + c 7 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveD q0 q3) c i j k l m n
      q3 * E 0 1 2 3 5 7 +
      q3 * E 0 1 2 3 6 9 +
      E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 7 +
      c 4 * E 0 1 2 5 6 7 +
      c 6 * E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 8 +
      c 6 * E 0 1 2 5 6 8 +
      c 5 * E 0 1 2 5 6 9 +
      c 1 * E 0 1 2 5 7 8 +
      E 0 1 2 5 7 9 +
      c 4 * E 0 1 2 5 7 9 +
      c 7 * E 0 1 2 5 7 9 +
      c 2 * E 0 1 2 5 8 9 +
      c 6 * E 0 1 2 5 8 9 +
      c 3 * E 0 1 2 6 7 8 +
      c 7 * E 0 1 2 6 7 8 +
      c 8 * E 0 1 2 6 7 8 +
      c 1 * E 0 1 2 6 7 9 +
      c 3 * E 0 1 2 6 7 9 +
      c 5 * E 0 1 2 6 8 9 +
      c 6 * E 0 1 2 6 8 9 +
      q3 * E 0 1 3 4 5 9 +
      c 4 * E 0 1 3 5 6 7 +
      c 5 * E 0 1 3 5 6 7 +
      c 0 * E 0 1 3 5 6 8 +
      c 8 * E 0 1 3 5 6 8 +
      c 0 * E 0 1 3 5 6 9 +
      c 3 * E 0 1 3 5 7 8 +
      E 0 1 3 5 8 9 +
      c 7 * E 0 1 3 6 7 9 +
      c 7 * E 0 1 3 6 8 9 +
      c 8 * E 0 1 3 6 8 9 +
      c 4 * E 0 1 3 7 8 9 +
      c 7 * E 0 1 3 7 8 9 +
      c 2 * E 0 1 4 5 6 8 +
      c 0 * E 0 1 4 5 6 9 +
      c 2 * E 0 1 4 5 6 9 +
      c 6 * E 0 1 4 5 6 9 +
      E 0 1 4 5 8 9 +
      c 5 * E 0 1 4 5 8 9 +
      c 8 * E 0 1 4 6 7 9 +
      c 7 * E 0 1 4 7 8 9 +
      c 8 * E 0 1 4 7 8 9 +
      c 7 * E 0 2 3 5 6 8 +
      c 7 * E 0 2 3 5 8 9 +
      c 6 * E 0 2 3 6 8 9 +
      c 7 * E 0 2 3 7 8 9 +
      c 8 * E 0 2 3 7 8 9 +
      c 5 * E 0 2 4 5 7 9 +
      c 8 * E 0 2 4 5 7 9 +
      c 7 * E 0 2 4 6 7 9 +
      E 0 3 4 6 8 9 +
      c 6 * E 1 2 3 5 7 8 +
      c 4 * E 1 2 3 5 8 9 +
      c 8 * E 1 2 4 5 7 9 +
      E 1 3 4 5 8 9 +
      q0 * E 1 4 5 7 8 9 +
      c 8 * E 2 3 4 5 6 8 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    degreeEffectiveD, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, secant_three_eq_one_f2,
    secant_nine_eq_one_f2, secant_five_eq_one_f2,
    secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
    secant_thirteen_eq_one_f2, secant_fourteen_eq_zero_f2,
    secant_sixteen_eq_zero_f2, secant_eighteen_eq_zero_f2,
    secant_twenty_eq_zero_f2, secant_twenty_two_eq_zero_f2,
    secant_twenty_four_eq_zero_f2, secant_twenty_six_eq_zero_f2,
    secant_twenty_eight_eq_zero_f2, secant_thirty_eq_zero_f2,
    secant_thirty_two_eq_zero_f2, secant_thirty_six_eq_zero_f2,
    secant_forty_eq_zero_f2,
    secant_forty_four_eq_zero_f2, secant_fifty_two_eq_zero_f2]

/-- On the `q₁=1,q₂=0` degree-two chart, every normalized two-wedge
presentation satisfies the three defining norm-block constraints. -/
theorem degreeD_normalizedLocalSecant_mem
    (q0 q3 : F₂) (c : TargetCoeff)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift 3 (degreeEffectiveD q0 q3) + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ degreeTwoSecantCoeffSpace := by
  have hE (i j k l m n : Fin 10) :
      normalizedLocalSecantEquation 3
        (degreeEffectiveD q0 q3) c i j k l m n = 0 :=
    normalizedLocalSecantEquation_eq_zero 3
      (degreeEffectiveD q0 q3) c i j k l m n hsecant
  change degreeTwoSecantConstraint c = 0
  ext t
  fin_cases t
  · change c 1 + c 2 + c 4 + c 5 = 0
    have hid := degreeD_secant_constraint_zero_identity q0 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 1 + c 3 + c 4 + c 6 = 0
    have hid := degreeD_secant_constraint_one_identity q0 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 1 + c 7 = 0
    have hid := degreeD_secant_constraint_two_identity q0 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid

set_option maxRecDepth 10000 in
/-- First degree-two secant pivot at the exceptional effective parameter. -/
theorem degreeG_secant_constraint_zero_identity (c : TargetCoeff) :
    c 1 + c 2 + c 4 + c 5 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        degreeEffectiveG c i j k l m n
      c 1 * E 0 1 2 3 5 6 +
      E 0 1 2 3 6 7 +
      c 1 * E 0 1 2 3 6 7 +
      E 0 1 2 3 7 8 +
      c 3 * E 0 1 2 3 7 8 +
      c 4 * E 0 1 2 3 7 8 +
      c 4 * E 0 1 2 4 5 6 +
      c 0 * E 0 1 5 7 8 9 +
      c 5 * E 0 2 3 4 5 6 +
      c 2 * E 1 2 3 4 6 7 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    degreeEffectiveG, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, secant_three_eq_one_f2,
    secant_nine_eq_one_f2, secant_five_eq_one_f2,
    secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
    secant_thirteen_eq_one_f2, secant_fourteen_eq_zero_f2,
    secant_sixteen_eq_zero_f2, secant_eighteen_eq_zero_f2,
    secant_twenty_eq_zero_f2, secant_twenty_two_eq_zero_f2,
    secant_twenty_four_eq_zero_f2, secant_twenty_six_eq_zero_f2,
    secant_twenty_eight_eq_zero_f2, secant_thirty_eq_zero_f2,
    secant_thirty_two_eq_zero_f2, secant_thirty_six_eq_zero_f2,
    secant_forty_eq_zero_f2, secant_forty_four_eq_zero_f2,
    secant_fifty_two_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- Second degree-two secant pivot at the exceptional effective parameter. -/
theorem degreeG_secant_constraint_one_identity (c : TargetCoeff) :
    c 1 + c 3 + c 4 + c 6 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        degreeEffectiveG c i j k l m n
      E 0 1 2 3 5 6 +
      c 3 * E 0 1 2 3 5 7 +
      c 6 * E 0 1 2 3 5 7 +
      E 0 1 2 3 5 8 +
      c 4 * E 0 1 2 3 5 8 +
      c 6 * E 0 1 2 3 5 8 +
      c 3 * E 0 1 2 3 5 9 +
      c 4 * E 0 1 2 3 5 9 +
      c 1 * E 0 1 2 3 6 7 +
      c 5 * E 0 1 2 3 6 7 +
      c 5 * E 0 1 2 3 6 9 +
      c 1 * E 0 1 2 3 7 8 +
      c 6 * E 0 1 2 3 7 8 +
      E 0 1 2 3 8 9 +
      c 0 * E 0 1 3 4 5 8 +
      c 7 * E 0 1 3 4 5 8 +
      c 0 * E 0 1 3 4 6 7 +
      c 7 * E 0 2 3 4 6 7 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    degreeEffectiveG, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, secant_three_eq_one_f2,
    secant_nine_eq_one_f2, secant_five_eq_one_f2,
    secant_seven_eq_one_f2,
    secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
    secant_thirteen_eq_one_f2, secant_fourteen_eq_zero_f2,
    secant_sixteen_eq_zero_f2, secant_eighteen_eq_zero_f2,
    secant_twenty_eq_zero_f2, secant_twenty_two_eq_zero_f2,
    secant_twenty_four_eq_zero_f2, secant_twenty_six_eq_zero_f2,
    secant_twenty_eight_eq_zero_f2, secant_thirty_eq_zero_f2,
    secant_thirty_two_eq_zero_f2, secant_thirty_six_eq_zero_f2,
    secant_forty_eq_zero_f2, secant_forty_four_eq_zero_f2,
    secant_fifty_two_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- Third degree-two secant pivot at the exceptional effective parameter. -/
theorem degreeG_secant_constraint_two_identity (c : TargetCoeff) :
    c 1 + c 7 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        degreeEffectiveG c i j k l m n
      E 0 1 2 3 5 6 +
      c 3 * E 0 1 2 3 5 7 +
      c 7 * E 0 1 2 3 5 7 +
      c 8 * E 0 1 2 3 5 7 +
      E 0 1 2 3 5 9 +
      c 3 * E 0 1 2 3 5 9 +
      c 4 * E 0 1 2 3 5 9 +
      c 8 * E 0 1 2 3 5 9 +
      E 0 1 2 3 6 7 +
      c 1 * E 0 1 2 3 6 9 +
      c 7 * E 0 1 2 3 6 9 +
      c 2 * E 0 1 2 4 5 6 +
      c 3 * E 0 1 2 4 5 9 +
      c 7 * E 0 1 2 4 5 9 +
      c 8 * E 0 1 2 4 6 9 +
      c 0 * E 0 1 2 4 7 9 +
      c 1 * E 0 1 2 4 7 9 +
      c 8 * E 0 1 2 4 7 9 +
      c 8 * E 0 1 3 4 6 7 +
      E 0 1 3 4 8 9 +
      c 0 * E 0 1 3 4 8 9 +
      c 1 * E 0 1 3 4 8 9 +
      E 0 1 4 5 6 9 +
      E 1 3 4 6 8 9 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    degreeEffectiveG, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, secant_three_eq_one_f2,
    secant_nine_eq_one_f2, secant_five_eq_one_f2,
    secant_seven_eq_one_f2,
    secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
    secant_thirteen_eq_one_f2, secant_fourteen_eq_zero_f2,
    secant_sixteen_eq_zero_f2, secant_eighteen_eq_zero_f2,
    secant_twenty_eq_zero_f2, secant_twenty_two_eq_zero_f2,
    secant_twenty_four_eq_zero_f2, secant_twenty_six_eq_zero_f2,
    secant_twenty_eight_eq_zero_f2, secant_thirty_eq_zero_f2,
    secant_thirty_two_eq_zero_f2, secant_thirty_six_eq_zero_f2,
    secant_forty_eq_zero_f2, secant_forty_four_eq_zero_f2,
    secant_fifty_two_eq_zero_f2]

/-- At the exceptional degree-two parameter, every normalized two-wedge
presentation satisfies the three defining norm-block constraints. -/
theorem degreeG_normalizedLocalSecant_mem
    (c : TargetCoeff)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift 3 degreeEffectiveG + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ degreeTwoSecantCoeffSpace := by
  have hE (i j k l m n : Fin 10) :
      normalizedLocalSecantEquation 3 degreeEffectiveG c i j k l m n = 0 :=
    normalizedLocalSecantEquation_eq_zero 3 degreeEffectiveG c
      i j k l m n hsecant
  change degreeTwoSecantConstraint c = 0
  ext t
  fin_cases t
  · change c 1 + c 2 + c 4 + c 5 = 0
    have hid := degreeG_secant_constraint_zero_identity c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 1 + c 3 + c 4 + c 6 = 0
    have hid := degreeG_secant_constraint_one_identity c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 1 + c 7 = 0
    have hid := degreeG_secant_constraint_two_identity c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid

/-- Algebraic degree-two-place pivot: effectiveness and a normalized
two-wedge presentation force the correction into the codimension-three
degree-two secant coefficient space. -/
theorem degreeTwo_normalizedLocalSecant_mem
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    (c : TargetCoeff)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift 3 q + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ degreeTwoSecantCoeffSpace := by
  rcases degreeTwoLocalEffective_cases q hq with hL | hrest
  · rcases hL with ⟨q1, q3, rfl⟩
    apply degreeQ2_normalizedLocalSecant_mem 0 q1 q3 c (by simp)
    simpa [degreeEffectiveQ2, degreeEffectiveL] using hsecant
  · rcases hrest with hM | hrest
    · rcases hM with ⟨q0, q1, rfl⟩
      apply degreeQ2_normalizedLocalSecant_mem q0 q1 0 c (by simp)
      simpa [degreeEffectiveQ2, degreeEffectiveM] using hsecant
    · rcases hrest with hD | hG
      · rcases hD with ⟨q0, q3, _hprod, rfl⟩
        exact degreeD_normalizedLocalSecant_mem q0 q3 c hsecant
      · rw [hG] at hsecant
        exact degreeG_normalizedLocalSecant_mem c hsecant

/-- The actual degree-two-place target-plane translation belongs to the five
local coefficient directions used in the quotient pivot. -/
theorem closedPlaceTargetCoeff_three_mem_degreeTwoLocalCoeffSpace
    (z : LocalTargetParam) :
    closedPlaceTargetCoeff 3 z ∈ degreeTwoLocalCoeffSpace := by
  have hdir (i : Fin 5) :
      degreeTwoLocalCoeffDirection i ∈ degreeTwoLocalCoeffSpace := by
    exact Submodule.subset_span (Set.mem_range_self i)
  have h8 : outsideHankelWord 8 ∈ degreeTwoLocalCoeffSpace := by
    have hsum := degreeTwoLocalCoeffSpace.add_mem
      (degreeTwoLocalCoeffSpace.add_mem
        (degreeTwoLocalCoeffSpace.add_mem (hdir 0) (hdir 2)) (hdir 3))
      (hdir 4)
    simpa [degreeTwoLocalCoeffDirection, closedPlaceDirections,
      outsideHankelWord, rankTwoHankelWord] using hsum
  have h7 : outsideHankelWord 7 ∈ degreeTwoLocalCoeffSpace := by
    have hsum := degreeTwoLocalCoeffSpace.add_mem
      (degreeTwoLocalCoeffSpace.add_mem (hdir 0) (hdir 1)) (hdir 4)
    simpa [degreeTwoLocalCoeffDirection, closedPlaceDirections,
      outsideHankelWord, rankTwoHankelWord] using hsum
  simpa [closedPlaceTargetCoeff] using
    degreeTwoLocalCoeffSpace.add_mem
      (degreeTwoLocalCoeffSpace.smul_mem (z 0) h8)
      (degreeTwoLocalCoeffSpace.smul_mem (z 1) h7)

/-- Degree-two-place local pivot in the original affine coordinates: the
target correction itself lies in the six-dimensional secant space. -/
theorem degreeTwo_localSecantCorrection_mem
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    (z : LocalTargetParam) (c : TargetCoeff)
    (hsecant : ∃ u v x y : LinearForm,
      localSecantCandidate 3 q z c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ degreeTwoSecantCoeffSpace := by
  let d := closedPlaceTargetCoeff 3 z + c
  have hnormalized : ∃ u v x y : LinearForm,
      closedPlaceLift 3 q + targetTwo d =
        squarefreeWedge u v + squarefreeWedge x y := by
    simpa only [d, localSecantCandidate_eq_lift_add_target] using hsecant
  have hd : d ∈ degreeTwoSecantCoeffSpace :=
    degreeTwo_normalizedLocalSecant_mem q hq d hnormalized
  have hz : closedPlaceTargetCoeff 3 z ∈ degreeTwoSecantCoeffSpace :=
    degreeTwoLocalCoeffSpace_le_secant
      (closedPlaceTargetCoeff_three_mem_degreeTwoLocalCoeffSpace z)
  have hsum := degreeTwoSecantCoeffSpace.add_mem hd hz
  have hcancel : d + closedPlaceTargetCoeff 3 z = c := by
    funext i
    simp only [d, Pi.add_apply]
    simp [add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero]
  rw [hcancel] at hsum
  exact hsum


end

end N5
end UnrestrictedBooleanMul

