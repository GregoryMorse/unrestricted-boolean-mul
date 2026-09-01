import UnrestrictedBooleanMul.N5.MixedPlaceDegreeOne

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-!
# Mixed-place exclusion at the rational place infinity

This module supplies compact Boolean-ideal certificates for the pair formed
by the doubled rational place `2P∞` and the degree-two place `P⋆`.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem degree_pow_three_f2 (x : F₂) : x ^ 3 = x := by
  rw [show 3 = 2 + 1 by omega, pow_succ, N3Certificate.pow_two_f2,
    N3Certificate.mul_self_f2]

private theorem five_eq_one_f2 : (5 : F₂) = 1 := by decide
private theorem ten_eq_zero_f2 : (10 : F₂) = 0 := by decide
private theorem twelve_eq_zero_f2 : (12 : F₂) = 0 := by decide
private theorem fourteen_eq_zero_f2 : (14 : F₂) = 0 := by decide
private theorem sixteen_eq_zero_f2 : (16 : F₂) = 0 := by decide
private theorem eighteen_eq_zero_f2 : (18 : F₂) = 0 := by decide
private theorem twenty_eq_zero_f2 : (20 : F₂) = 0 := by decide
private theorem twentyTwo_eq_zero_f2 : (22 : F₂) = 0 := by decide
private theorem twentyFour_eq_zero_f2 : (24 : F₂) = 0 := by decide
private theorem twentySix_eq_zero_f2 : (26 : F₂) = 0 := by decide
private theorem twentyEight_eq_zero_f2 : (28 : F₂) = 0 := by decide
private theorem thirty_eq_zero_f2 : (30 : F₂) = 0 := by decide
private theorem thirtyTwo_eq_zero_f2 : (32 : F₂) = 0 := by decide
private theorem thirtyFour_eq_zero_f2 : (34 : F₂) = 0 := by decide

abbrev DegreeInfinityAmbientQuad := Fin 4 → Fin 10

def mixed23Quad : Fin 15 → DegreeInfinityAmbientQuad :=
  ![![0, 3, 5, 8], ![0, 3, 6, 9], ![1, 4, 6, 9],
    ![1, 4, 7, 8], ![2, 3, 7, 9], ![2, 3, 8, 9],
    ![3, 4, 8, 9], ![1, 4, 5, 8], ![2, 3, 6, 7],
    ![3, 4, 7, 8], ![0, 4, 5, 9], ![2, 3, 4, 9],
    ![1, 2, 7, 9], ![1, 3, 5, 8], ![0, 3, 4, 6]]

def mixed23Equation (q r : LocalKleinParam) (c : TargetCoeff)
    (t : Fin 15) : F₂ :=
  mixedPluckerValue 2 q 3 r c (mixed23Quad t 0) (mixed23Quad t 1)
    (mixed23Quad t 2) (mixed23Quad t 3)

def Mixed23PluckerZero (q r : LocalKleinParam) (c : TargetCoeff) : Prop :=
  ∀ t : Fin 15, mixed23Equation q r c t = 0

theorem mixed23PluckerZero_of_decomposable (q r : LocalKleinParam)
    (c : TargetCoeff)
    (hdec : IsDecomposableTwo
      (closedPlaceLift 2 q + closedPlaceLift 3 r + targetTwo c)) :
    Mixed23PluckerZero q r c := by
  intro t
  refine mixedPluckerValue_eq_zero_of_decomposable 2 q 3 r c
    (mixed23Quad t 0) (mixed23Quad t 1) (mixed23Quad t 2) (mixed23Quad t 3)
    ?_ ?_ ?_ ?_ ?_ ?_ hdec
  all_goals fin_cases t <;> decide

theorem mixed23_AL_identity (q0 q1 q3 r1 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed23Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveL r1 r3) c t
      (1 + c 8 + c 6 * c 8) * E 0 + (r1 * c 6 + r1 * c 7) * E 1 +
      (1 + q1 + q1 * r1 + r1 * c 1 + q1 * c 3 + c 5 + c 3 * c 5 +
        c 1 * c 6 + c 6 * c 7) * E 3 +
      (c 1 + c 1 * c 5 + c 5 * c 6) * E 4 +
      (1 + r1 * c 3 + q1 * c 6 + c 4 * c 6 + q1 * c 7) * E 5 +
      (c 3 + c 3 * c 6) * E 6 +
      (q1 * c 3 + c 6 + r1 * c 6 + c 3 * c 7) * E 7 +
      (q1 * r1 + c 1 + q1 * c 3 + q1 * c 5 + c 1 * c 5 + c 4 * c 5 +
        c 5 * c 6 + c 7) * E 8 +
      (c 7 + c 6 * c 7) * E 9 + (1 + c 6) * E 10 +
      (q3 * c 3 + r3 * c 3 + r3 * c 7) * E 11 +
      (r1 * c 1 + q1 * c 4 + c 3 * c 4 + c 6 + r1 * c 6 + c 3 * c 6 +
        c 1 * c 7) * E 12 +
      (q1 * c 3 + r1 * c 6 + c 3 * c 6 + c 7) * E 13 := by
  simp [mixed23Equation, mixed23Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeEffectiveL,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2,
    sixteen_eq_zero_f2, eighteen_eq_zero_f2, twenty_eq_zero_f2,
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentySix_eq_zero_f2,
    twentyEight_eq_zero_f2, thirty_eq_zero_f2, thirtyTwo_eq_zero_f2,
    thirtyFour_eq_zero_f2, five_eq_one_f2]

theorem mixed23_AM_identity (q0 q1 q3 r0 r1 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed23Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveM r0 r1) c t
      (1 + c 8 + c 6 * c 8) * E 0 + (q1 * r1 + c 4 + q1 * c 6) * E 1 +
      c 7 * c 8 * E 2 +
      (q1 * r1 + c 4 * c 5 + r1 * c 6 + c 1 * c 6 + r1 * c 7) * E 3 +
      (r1 * c 1 + c 1 * c 4 + c 5 + c 3 * c 5 + c 4 * c 6 +
        c 1 * c 7 + c 8 + c 4 * c 8) * E 4 +
      c 7 * c 8 * E 5 + (c 7 + c 6 * c 7) * E 6 +
      (r1 * c 1 + q1 * c 5 + c 4 * c 5 + q1 * c 6 + c 3 * c 6 +
        r1 * c 7) * E 7 +
      (r1 + q1 * c 4 + c 3 * c 5 + c 6 + q1 * c 6 + c 4 * c 7 + c 8 +
        c 6 * c 8) * E 8 +
      (1 + r1 * c 1 + c 3 + r1 * c 3 + c 1 * c 4 + c 3 * c 4 +
        r1 * c 5 + c 4 * c 5 + c 1 * c 6 + q1 * c 7 + c 1 * c 7) * E 9 +
      (1 + c 6 + c 4 * c 8 + c 6 * c 8 + c 7 * c 8) * E 10 +
      q3 * c 7 * E 11 +
      (1 + c 3 + c 4 + r1 * c 4 + q1 * c 5 + c 4 * c 6 + c 8 +
        c 5 * c 8 + c 6 * c 8) * E 12 +
      (r1 + c 4 + q1 * c 5 + c 4 * c 5 + c 6) * E 13 := by
  simp [mixed23Equation, mixed23Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeEffectiveM,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2,
    sixteen_eq_zero_f2, eighteen_eq_zero_f2, twenty_eq_zero_f2,
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentySix_eq_zero_f2,
    twentyEight_eq_zero_f2, thirty_eq_zero_f2, thirtyTwo_eq_zero_f2,
    thirtyFour_eq_zero_f2, five_eq_one_f2]

theorem mixed23_AD_identity (q0 q1 q3 r0 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed23Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveD r0 r3) c t
      c 6 * E 0 + (c 3 + c 5) * E 3 + c 5 * E 7 +
      (q1 + c 3 + c 7) * E 8 + c 1 * E 9 + c 6 * E 12 +
      (1 + c 6) * E 13 + r3 * E 14 +
      (q1 + c 3 + c 4 + c 6 + c 7) * (r0 * r3) := by
  simp [mixed23Equation, mixed23Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2,
    sixteen_eq_zero_f2, eighteen_eq_zero_f2, twenty_eq_zero_f2,
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentySix_eq_zero_f2,
    twentyEight_eq_zero_f2, thirty_eq_zero_f2, thirtyTwo_eq_zero_f2,
    thirtyFour_eq_zero_f2, five_eq_one_f2]

theorem mixed23_AG_identity (q0 q1 q3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed23Equation (rationalEffectiveA q0 q1 q3)
        degreeEffectiveG c t
      c 6 * E 0 + c 1 * E 3 + (c 3 + c 5) * E 7 + c 1 * E 9 +
      E 12 + c 4 * E 13 + c 1 * E 14 := by
  simp [mixed23Equation, mixed23Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeEffectiveG,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]

theorem mixed23_DL_identity (q0 q3 r1 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed23Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveL r1 r3) c t
      (c 3 + r1 * c 4 + c 0 * c 6 + c 4 * c 6 + c 6 * c 8) * E 0 +
      (c 1 + c 4 + c 1 * c 4 + c 3 * c 5 + c 1 * c 6 + c 7) * E 1 +
      (1 + r1 * c 4 + r1 * c 6) * E 3 +
      (c 3 + c 3 * c 4 + c 7) * E 4 +
      (r1 * c 1 + c 1 * c 3 + c 6 + c 7 + c 3 * c 7) * E 5 +
      c 3 * c 6 * E 6 + (r1 + c 6 + c 3 * c 7) * E 7 +
      (r1 * c 1 + c 3) * E 9 + c 0 * c 6 * E 10 + r3 * c 3 * E 11 +
      (c 3 * c 5 + c 3 * c 6) * E 12 + (1 + c 4) * E 13 +
      r1 * r3 * E 14 + c 3 * c 6 * (q0 * q3) := by
  simp [mixed23Equation, mixed23Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeEffectiveL,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2,
    sixteen_eq_zero_f2, eighteen_eq_zero_f2, twenty_eq_zero_f2,
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentySix_eq_zero_f2,
    twentyEight_eq_zero_f2, thirty_eq_zero_f2, thirtyTwo_eq_zero_f2,
    thirtyFour_eq_zero_f2, five_eq_one_f2]

theorem mixed23_DM_identity (q0 q3 r0 r1 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed23Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveM r0 r1) c t
      (1 + c 5 + c 5 * c 6 + c 6 * c 8) * E 0 +
      (1 + r1 * c 4 + r1 * c 7 + c 1 * c 7) * E 1 +
      (c 6 * c 8 + c 7 * c 8) * E 2 +
      (1 + c 1 * c 4 + c 3 * c 4 + c 4 * c 6 + r1 * c 7 + c 3 * c 7 +
        c 4 * c 7) * E 3 +
      (1 + c 3 * c 7 + c 8 + r1 * c 8) * E 4 +
      (c 3 * c 6 + c 7) * E 5 + (c 6 + c 3 * c 6 + c 8) * E 6 +
      (r1 + c 3 * c 4) * E 7 +
      (c 4 + c 3 * c 4 + r1 * c 5 + c 6 + c 7) * E 8 +
      (c 4 * c 7 + c 5 * c 8) * E 9 + (c 6 + c 7 * c 8) * E 10 +
      q3 * r0 * E 11 + (1 + c 3 + c 4 + r1 * c 7) * E 12 +
      (r1 + r1 * c 4 + r1 * c 6 + c 4 * c 6) * E 13 +
      (q3 * r0 + c 6 + r0 * c 6 + c 3 * c 6 + q0 * c 8) *
        (q0 * q3) := by
  simp [mixed23Equation, mixed23Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeEffectiveM,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2,
    sixteen_eq_zero_f2, eighteen_eq_zero_f2, twenty_eq_zero_f2,
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentySix_eq_zero_f2,
    twentyEight_eq_zero_f2, thirty_eq_zero_f2, thirtyTwo_eq_zero_f2,
    thirtyFour_eq_zero_f2, five_eq_one_f2]

theorem mixed23_DD_identity (q0 q3 r0 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed23Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveD r0 r3) c t
      E 0 + (1 + c 3) * E 1 + c 7 * E 3 + (1 + c 6) * E 4 +
      c 0 * E 5 + c 0 * E 6 + (1 + c 3) * E 7 + c 0 * E 9 +
      (1 + c 0 + c 6) * E 10 + c 0 * (q0 * q3) := by
  simp [mixed23Equation, mixed23Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2,
    sixteen_eq_zero_f2, eighteen_eq_zero_f2, twenty_eq_zero_f2,
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentySix_eq_zero_f2,
    twentyEight_eq_zero_f2, thirty_eq_zero_f2, thirtyTwo_eq_zero_f2,
    thirtyFour_eq_zero_f2, five_eq_one_f2]

theorem mixed23_DG_identity (q0 q3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed23Equation (rationalEffectiveD q0 q3)
        degreeEffectiveG c t
      (1 + c 8) * E 2 + c 7 * E 3 + (c 6 + c 7) * E 4 +
      (1 + c 8) * E 5 + (1 + c 8) * E 6 + c 7 * E 7 +
      (1 + c 6 + c 8) * E 9 + E 11 + (q0 + c 8) * (q0 * q3) := by
  simp [mixed23Equation, mixed23Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeEffectiveG,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2,
    sixteen_eq_zero_f2, eighteen_eq_zero_f2, twenty_eq_zero_f2,
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentySix_eq_zero_f2,
    twentyEight_eq_zero_f2, thirty_eq_zero_f2, thirtyTwo_eq_zero_f2,
    thirtyFour_eq_zero_f2, five_eq_one_f2]

/-! ## The `2P∞ + P⋆` obstruction -/

theorem mixed23_AL_obstruction (q0 q1 q3 r1 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed23PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveL r1 r3) c := by
  intro h
  unfold Mixed23PluckerZero at h
  have hid := mixed23_AL_identity q0 q1 q3 r1 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed23_AM_obstruction (q0 q1 q3 r0 r1 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed23PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveM r0 r1) c := by
  intro h
  unfold Mixed23PluckerZero at h
  have hid := mixed23_AM_identity q0 q1 q3 r0 r1 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed23_AD_obstruction (q0 q1 q3 r0 r3 : F₂)
    (c : TargetCoeff) (hr03 : r0 * r3 = 0) :
    ¬ Mixed23PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveD r0 r3) c := by
  intro h
  unfold Mixed23PluckerZero at h
  have hid := mixed23_AD_identity q0 q1 q3 r0 r3 c
  dsimp only at hid
  simp only [h, hr03] at hid
  simp at hid

theorem mixed23_AG_obstruction (q0 q1 q3 : F₂) (c : TargetCoeff) :
    ¬ Mixed23PluckerZero (rationalEffectiveA q0 q1 q3)
      degreeEffectiveG c := by
  intro h
  unfold Mixed23PluckerZero at h
  have hid := mixed23_AG_identity q0 q1 q3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed23_DL_obstruction (q0 q3 r1 r3 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) :
    ¬ Mixed23PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveL r1 r3) c := by
  intro h
  unfold Mixed23PluckerZero at h
  have hid := mixed23_DL_identity q0 q3 r1 r3 c
  dsimp only at hid
  simp only [h, hq03] at hid
  simp at hid

theorem mixed23_DM_obstruction (q0 q3 r0 r1 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) :
    ¬ Mixed23PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveM r0 r1) c := by
  intro h
  unfold Mixed23PluckerZero at h
  have hid := mixed23_DM_identity q0 q3 r0 r1 c
  dsimp only at hid
  simp only [h, hq03] at hid
  simp at hid

theorem mixed23_DD_obstruction (q0 q3 r0 r3 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) :
    ¬ Mixed23PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveD r0 r3) c := by
  intro h
  unfold Mixed23PluckerZero at h
  have hid := mixed23_DD_identity q0 q3 r0 r3 c
  dsimp only at hid
  simp only [h, hq03] at hid
  simp at hid

theorem mixed23_DG_obstruction (q0 q3 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) :
    ¬ Mixed23PluckerZero (rationalEffectiveD q0 q3)
      degreeEffectiveG c := by
  intro h
  unfold Mixed23PluckerZero at h
  have hid := mixed23_DG_identity q0 q3 c
  dsimp only at hid
  simp only [h, hq03] at hid
  simp at hid

theorem mixed23_plucker_obstruction (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : DegreeTwoLocalEffective r)
    (c : TargetCoeff) : ¬ Mixed23PluckerZero q r c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, hq03, rfl⟩
  · rcases degreeTwoLocalEffective_cases r hr with hL | hrest
    · rcases hL with ⟨r1, r3, rfl⟩
      exact mixed23_AL_obstruction q0 q1 q3 r1 r3 c
    · rcases hrest with hM | hrest
      · rcases hM with ⟨r0, r1, rfl⟩
        exact mixed23_AM_obstruction q0 q1 q3 r0 r1 c
      · rcases hrest with hD | hG
        · rcases hD with ⟨r0, r3, hr03, rfl⟩
          exact mixed23_AD_obstruction q0 q1 q3 r0 r3 c hr03
        · rw [hG]
          exact mixed23_AG_obstruction q0 q1 q3 c
  · rcases degreeTwoLocalEffective_cases r hr with hL | hrest
    · rcases hL with ⟨r1, r3, rfl⟩
      exact mixed23_DL_obstruction q0 q3 r1 r3 c hq03
    · rcases hrest with hM | hrest
      · rcases hM with ⟨r0, r1, rfl⟩
        exact mixed23_DM_obstruction q0 q3 r0 r1 c hq03
      · rcases hrest with hD | hG
        · rcases hD with ⟨r0, r3, _, rfl⟩
          exact mixed23_DD_obstruction q0 q3 r0 r3 c hq03
        · rw [hG]
          exact mixed23_DG_obstruction q0 q3 c hq03

/-- No decomposable target correction exists for a doubled rational place at
`P∞` together with the unique degree-two place. -/
theorem rational23_mixed_decomposableFiber_empty (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : DegreeTwoLocalEffective r) :
    decomposableFiber
      (closedPlaceQuotientPoint 2 q + closedPlaceQuotientPoint 3 r) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_mixedCandidate_of_mem_decomposableFiber 2 3 q r p hp with
    ⟨c, hpc⟩
  have hdec : IsDecomposableTwo
      (closedPlaceLift 2 q + closedPlaceLift 3 r + targetTwo c) := by
    rw [← hpc]
    exact hp.1
  exact mixed23_plucker_obstruction q r hq hr c
    (mixed23PluckerZero_of_decomposable q r c hdec)

theorem mem_effectiveParamsAt_rational (place : Fin 4) (hp : place ≠ 3)
    (q : LocalKleinParam) :
    q ∈ effectiveParamsAt place ↔ RationalLocalEffective q := by
  simp [effectiveParamsAt, hp, rationalEffectiveParams]

theorem mem_effectiveParamsAt_degreeTwo (q : LocalKleinParam) :
    q ∈ effectiveParamsAt 3 ↔ DegreeTwoLocalEffective q := by
  simp [effectiveParamsAt, degreeTwoEffectiveParams]

theorem fin_four_lt_cases (i j : Fin 4) (hij : i < j) :
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
    (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
  omega

/-- Ordered form of the strong mixed-place exclusion.  Isolating the six
strictly ordered pairs keeps the dependent chart case split small. -/
theorem strongMixedPlace_of_lt (x y : ClosedPlaceEffectiveParam)
    (hxy : x.1 < y.1) :
    decomposableFiber (closedPlaceEffectivePoint x +
      closedPlaceEffectivePoint y) = ∅ := by
  rcases x with ⟨place, ⟨q, hq⟩⟩
  rcases y with ⟨place', ⟨r, hr⟩⟩
  dsimp [closedPlaceEffectivePoint]
  rcases fin_four_lt_cases place place' hxy with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rational01_mixed_decomposableFiber_empty q r
      ((mem_effectiveParamsAt_rational 0 (by decide) q).1 hq)
      ((mem_effectiveParamsAt_rational 1 (by decide) r).1 hr)
  · exact rational02_mixed_decomposableFiber_empty q r
      ((mem_effectiveParamsAt_rational 0 (by decide) q).1 hq)
      ((mem_effectiveParamsAt_rational 2 (by decide) r).1 hr)
  · exact rational03_mixed_decomposableFiber_empty q r
      ((mem_effectiveParamsAt_rational 0 (by decide) q).1 hq)
      ((mem_effectiveParamsAt_degreeTwo r).1 hr)
  · exact rational12_mixed_decomposableFiber_empty q r
      ((mem_effectiveParamsAt_rational 1 (by decide) q).1 hq)
      ((mem_effectiveParamsAt_rational 2 (by decide) r).1 hr)
  · exact rational13_mixed_decomposableFiber_empty q r
      ((mem_effectiveParamsAt_rational 1 (by decide) q).1 hq)
      ((mem_effectiveParamsAt_degreeTwo r).1 hr)
  · exact rational23_mixed_decomposableFiber_empty q r
      ((mem_effectiveParamsAt_rational 2 (by decide) q).1 hq)
      ((mem_effectiveParamsAt_degreeTwo r).1 hr)

/-- Strong mixed-place exclusion: the sum of effective quotient points from
two distinct closed-place types has no decomposable lift. -/
theorem strongMixedPlace (x y : ClosedPlaceEffectiveParam)
    (hxy : x.1 ≠ y.1) :
    decomposableFiber (closedPlaceEffectivePoint x +
      closedPlaceEffectivePoint y) = ∅ := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact strongMixedPlace_of_lt x y hlt
  · simpa [add_comm] using strongMixedPlace_of_lt y x hgt

end

end N5
end UnrestrictedBooleanMul
