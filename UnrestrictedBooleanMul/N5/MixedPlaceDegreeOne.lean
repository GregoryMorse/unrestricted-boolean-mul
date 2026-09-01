import UnrestrictedBooleanMul.N5.MixedPlaceDegree

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-!
# Mixed-place exclusion at the rational place one

This module supplies compact Boolean-ideal certificates for the pair formed
by the doubled rational place `2P₁` and the degree-two place `P⋆`.
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
private theorem twentyEight_eq_zero_f2 : (28 : F₂) = 0 := by decide
private theorem thirty_eq_zero_f2 : (30 : F₂) = 0 := by decide
private theorem thirtyTwo_eq_zero_f2 : (32 : F₂) = 0 := by decide
private theorem thirtyFour_eq_zero_f2 : (34 : F₂) = 0 := by decide

abbrev DegreeOneAmbientQuad := Fin 4 → Fin 10

def mixed13Quad : Fin 10 → DegreeOneAmbientQuad :=
  ![![0, 1, 5, 6], ![0, 1, 7, 8], ![3, 4, 5, 6],
    ![1, 2, 6, 9], ![0, 3, 7, 9], ![3, 4, 7, 8],
    ![1, 2, 7, 9], ![2, 3, 6, 7], ![1, 2, 6, 8], ![1, 3, 7, 9]]

def mixed13Equation (q r : LocalKleinParam) (c : TargetCoeff)
    (t : Fin 10) : F₂ :=
  mixedPluckerValue 1 q 3 r c (mixed13Quad t 0) (mixed13Quad t 1)
    (mixed13Quad t 2) (mixed13Quad t 3)

def Mixed13PluckerZero (q r : LocalKleinParam) (c : TargetCoeff) : Prop :=
  ∀ t : Fin 10, mixed13Equation q r c t = 0

theorem mixed13PluckerZero_of_decomposable (q r : LocalKleinParam)
    (c : TargetCoeff)
    (hdec : IsDecomposableTwo
      (closedPlaceLift 1 q + closedPlaceLift 3 r + targetTwo c)) :
    Mixed13PluckerZero q r c := by
  intro t
  refine mixedPluckerValue_eq_zero_of_decomposable 1 q 3 r c
    (mixed13Quad t 0) (mixed13Quad t 1) (mixed13Quad t 2) (mixed13Quad t 3)
    ?_ ?_ ?_ ?_ ?_ ?_ hdec
  all_goals fin_cases t <;> decide

theorem mixed13_AL_identity (q0 q1 q3 r1 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed13Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveL r1 r3) c t
      (1 + q0 * q3 + q0 * r3 + c 5 + q1 * c 5 + r1 * c 5 + c 2 * c 5 + c 3 * c 5 + c 6 + r1 * c 6 + c 2 * c 6) * E 1 +
      (1 + r1 * c 3 + r1 * c 5 + c 5 * c 6) * E 2 +
      (1 + q0 * q3 + r1 + q1 * r1 + q0 * r3 + q1 * c 4 + q1 * c 5 + c 2 * c 7) * E 3 +
      (1 + q0 * q3 + q0 * r3 + c 3 + r1 * c 5 + c 3 * c 5 + q1 * c 6 + c 2 * c 6 + c 2 * c 7) * E 4 +
      (q0 * r3 + q1 * c 2 + r1 * c 2 + c 2 * c 4 + c 2 * c 5 + r1 * c 6 + c 3 * c 6 + c 5 * c 6) * E 5 +
      (q0 * q3 + q1 * r1 + c 5 + q1 * c 5 + r1 * c 5 + c 2 * c 5 + c 4 * c 5 + q1 * c 6 + c 2 * c 6 + c 5 * c 6 + c 5 * c 7) * E 6 +
      (q1 + r1 + q1 * c 3 + c 4 + q1 * c 4 + c 5 + q1 * c 5 + r1 * c 5 + q1 * c 6 + r1 * c 6) * E 7 +
      (q1 + q1 * r1 + c 4 + q1 * c 4 + q1 * c 5 + c 2 * c 5 + c 3 * c 5 + q1 * c 6 + c 3 * c 6 + c 5 * c 6) * E 8 +
      c 5 * E 9 := by
  simp [mixed13Equation, mixed13Quad, mixedPluckerValue,
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
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentyEight_eq_zero_f2,
    thirty_eq_zero_f2, thirtyTwo_eq_zero_f2, thirtyFour_eq_zero_f2,
    five_eq_one_f2]

theorem mixed13_AM_identity (q0 q1 q3 r0 r1 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed13Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveM r0 r1) c t
      (1 + q1 * c 3 + c 2 * c 3 + c 4 + c 2 * c 4 + c 3 * c 5) * E 1 +
      (q1 * r1 + c 2 + c 4 + c 2 * c 4 + q1 * c 5 + r1 * c 5) * E 2 +
      (1 + q1 + q1 * r1 + r1 * c 2 + r1 * c 5 + c 2 * c 5) * E 3 +
      (r1 + c 2 * c 3 + c 4 * c 5 + c 2 * c 7) * E 4 +
      (q1 + c 2 + q1 * c 5 + c 2 * c 5) * E 5 +
      (c 3 + r1 * c 3) * E 6 +
      (r1 * c 2 + q1 * c 3 + c 2 * c 3 + c 3 * c 5) * E 7 +
      (q1 * r1 + c 2 + r1 * c 2 + c 2 * c 3 + c 3 * c 4 + c 5 + q1 * c 5 + c 3 * c 5) * E 8 +
      c 2 * c 7 * E 9 := by
  simp [mixed13Equation, mixed13Quad, mixedPluckerValue,
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
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentyEight_eq_zero_f2,
    thirty_eq_zero_f2, thirtyTwo_eq_zero_f2, thirtyFour_eq_zero_f2,
    five_eq_one_f2]

theorem mixed13_AD_identity (q0 q1 q3 r0 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed13Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveD r0 r3) c t
      (1 + q1 + c 2 + q1 * c 2 + q1 * c 4) * E 1 + c 3 * E 2 +
      (1 + q1) * E 3 + (1 + r0 * r3 + c 3) * E 4 +
      (c 2 + c 3) * E 5 + (1 + q1 + c 3 + q1 * c 3) * E 6 +
      (q1 * c 2 + q1 * c 4) * E 7 + (1 + q1 * c 3) * E 8 +
      (r0 * r3 + q1 * c 3 + c 2 * c 7 + c 3 * c 7) * E 9 +
      (q0 * r0 + q1 * c 3 + r0 * c 3 + r3 * c 5 + c 4 * c 5 +
        r3 * c 7) * (r0 * r3) := by
  simp [mixed13Equation, mixed13Quad, mixedPluckerValue,
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
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentyEight_eq_zero_f2,
    thirty_eq_zero_f2, thirtyTwo_eq_zero_f2, thirtyFour_eq_zero_f2,
    five_eq_one_f2]

theorem mixed13_AG_identity (q0 q1 q3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed13Equation (rationalEffectiveA q0 q1 q3)
        degreeEffectiveG c t
      (1 + c 2 + q1 * c 2 + c 4) * E 1 +
      (1 + q1 * c 3 + q1 * c 4 + q1 * c 5 + c 3 * c 6) * E 2 +
      (1 + q1 * c 5) * E 4 + (c 2 + q1 * c 2 + q1 * c 3) * E 5 +
      (1 + c 3 + q1 * c 5) * E 6 +
      (c 4 + q1 * c 4 + q1 * c 5 + c 3 * c 6) * E 7 + c 3 * E 8 +
      (c 2 * c 3 + q1 * c 5 + c 2 * c 7) * E 9 := by
  simp [mixed13Equation, mixed13Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeEffectiveG,
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
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentyEight_eq_zero_f2,
    thirty_eq_zero_f2, thirtyTwo_eq_zero_f2, thirtyFour_eq_zero_f2,
    five_eq_one_f2]

theorem mixed13_DL_identity (q0 q3 r1 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed13Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveL r1 r3) c t
      (r1 + r1 * c 3 + c 3 * c 4 + c 4 * c 6 + r1 * c 7) * E 1 +
      (1 + c 4 * c 5) * E 2 + (r1 * c 4 + c 4 * c 6) * E 3 +
      r1 * c 4 * E 4 + (1 + c 5 + c 6 + c 5 * c 6) * E 5 +
      (r1 + r1 * c 3 + c 3 * c 4 + c 4 * c 5 + c 6 + c 4 * c 6 +
        c 5 * c 6) * E 6 +
      (r1 * c 4 + c 5 + r1 * c 7) * E 7 + c 3 * c 5 * E 9 +
      (r1 + r1 * c 3 + c 3 * c 4 + c 4 * c 5 + q0 * c 6 +
        c 5 * c 6) * (q0 * q3) := by
  simp [mixed13Equation, mixed13Quad, mixedPluckerValue,
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
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentyEight_eq_zero_f2,
    thirty_eq_zero_f2, thirtyTwo_eq_zero_f2, thirtyFour_eq_zero_f2,
    five_eq_one_f2]

theorem mixed13_DM_identity (q0 q3 r0 r1 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed13Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveM r0 r1) c t
      (r1 + r1 * c 3 + c 4) * E 1 + E 2 + c 4 * c 6 * E 3 +
      (c 5 + c 5 * c 7) * E 4 + c 4 * E 5 + c 4 * E 6 +
      (1 + r1 + r1 * c 3 + c 4 * c 6) * E 7 +
      (c 4 + c 2 * c 4) * E 8 := by
  simp [mixed13Equation, mixed13Quad, mixedPluckerValue,
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
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentyEight_eq_zero_f2,
    thirty_eq_zero_f2, thirtyTwo_eq_zero_f2, thirtyFour_eq_zero_f2,
    five_eq_one_f2]

theorem mixed13_DD_identity (q0 q3 r0 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed13Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveD r0 r3) c t
      c 2 * E 1 + (c 2 + c 3) * E 2 + (1 + c 3) * E 3 +
      (1 + c 2) * E 4 + (1 + c 2) * E 6 + E 7 +
      (1 + c 3) * E 8 + (r3 + c 2) * (r0 * r3) := by
  simp [mixed13Equation, mixed13Quad, mixedPluckerValue,
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
    twentyTwo_eq_zero_f2, twentyFour_eq_zero_f2, twentyEight_eq_zero_f2,
    thirty_eq_zero_f2, thirtyTwo_eq_zero_f2, thirtyFour_eq_zero_f2,
    five_eq_one_f2]

theorem mixed13_DG_identity (q0 q3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed13Equation (rationalEffectiveD q0 q3)
        degreeEffectiveG c t
      (c 5 + c 7) * E 2 + c 5 * E 5 + c 7 * E 7 + E 9 := by
  simp [mixed13Equation, mixed13Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeEffectiveG,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]

/-! ## The `2P₁ + P⋆` obstruction -/

theorem mixed13_AL_obstruction (q0 q1 q3 r1 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed13PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveL r1 r3) c := by
  intro h
  unfold Mixed13PluckerZero at h
  have hid := mixed13_AL_identity q0 q1 q3 r1 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed13_AM_obstruction (q0 q1 q3 r0 r1 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed13PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveM r0 r1) c := by
  intro h
  unfold Mixed13PluckerZero at h
  have hid := mixed13_AM_identity q0 q1 q3 r0 r1 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed13_AD_obstruction (q0 q1 q3 r0 r3 : F₂)
    (c : TargetCoeff) (hr03 : r0 * r3 = 0) :
    ¬ Mixed13PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveD r0 r3) c := by
  intro h
  unfold Mixed13PluckerZero at h
  have hid := mixed13_AD_identity q0 q1 q3 r0 r3 c
  dsimp only at hid
  simp only [h, hr03] at hid
  simp at hid

theorem mixed13_AG_obstruction (q0 q1 q3 : F₂) (c : TargetCoeff) :
    ¬ Mixed13PluckerZero (rationalEffectiveA q0 q1 q3)
      degreeEffectiveG c := by
  intro h
  unfold Mixed13PluckerZero at h
  have hid := mixed13_AG_identity q0 q1 q3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed13_DL_obstruction (q0 q3 r1 r3 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) :
    ¬ Mixed13PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveL r1 r3) c := by
  intro h
  unfold Mixed13PluckerZero at h
  have hid := mixed13_DL_identity q0 q3 r1 r3 c
  dsimp only at hid
  simp only [h, hq03] at hid
  simp at hid

theorem mixed13_DM_obstruction (q0 q3 r0 r1 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed13PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveM r0 r1) c := by
  intro h
  unfold Mixed13PluckerZero at h
  have hid := mixed13_DM_identity q0 q3 r0 r1 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed13_DD_obstruction (q0 q3 r0 r3 : F₂)
    (c : TargetCoeff) (hr03 : r0 * r3 = 0) :
    ¬ Mixed13PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveD r0 r3) c := by
  intro h
  unfold Mixed13PluckerZero at h
  have hid := mixed13_DD_identity q0 q3 r0 r3 c
  dsimp only at hid
  simp only [h, hr03] at hid
  simp at hid

theorem mixed13_DG_obstruction (q0 q3 : F₂) (c : TargetCoeff) :
    ¬ Mixed13PluckerZero (rationalEffectiveD q0 q3)
      degreeEffectiveG c := by
  intro h
  unfold Mixed13PluckerZero at h
  have hid := mixed13_DG_identity q0 q3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed13_plucker_obstruction (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : DegreeTwoLocalEffective r)
    (c : TargetCoeff) : ¬ Mixed13PluckerZero q r c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, hq03, rfl⟩
  · rcases degreeTwoLocalEffective_cases r hr with hL | hrest
    · rcases hL with ⟨r1, r3, rfl⟩
      exact mixed13_AL_obstruction q0 q1 q3 r1 r3 c
    · rcases hrest with hM | hrest
      · rcases hM with ⟨r0, r1, rfl⟩
        exact mixed13_AM_obstruction q0 q1 q3 r0 r1 c
      · rcases hrest with hD | hG
        · rcases hD with ⟨r0, r3, hr03, rfl⟩
          exact mixed13_AD_obstruction q0 q1 q3 r0 r3 c hr03
        · rw [hG]
          exact mixed13_AG_obstruction q0 q1 q3 c
  · rcases degreeTwoLocalEffective_cases r hr with hL | hrest
    · rcases hL with ⟨r1, r3, rfl⟩
      exact mixed13_DL_obstruction q0 q3 r1 r3 c hq03
    · rcases hrest with hM | hrest
      · rcases hM with ⟨r0, r1, rfl⟩
        exact mixed13_DM_obstruction q0 q3 r0 r1 c
      · rcases hrest with hD | hG
        · rcases hD with ⟨r0, r3, hr03, rfl⟩
          exact mixed13_DD_obstruction q0 q3 r0 r3 c hr03
        · rw [hG]
          exact mixed13_DG_obstruction q0 q3 c

/-- No decomposable target correction exists for a doubled rational place at
`P₁` together with the unique degree-two place. -/
theorem rational13_mixed_decomposableFiber_empty (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : DegreeTwoLocalEffective r) :
    decomposableFiber
      (closedPlaceQuotientPoint 1 q + closedPlaceQuotientPoint 3 r) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_mixedCandidate_of_mem_decomposableFiber 1 3 q r p hp with
    ⟨c, hpc⟩
  have hdec : IsDecomposableTwo
      (closedPlaceLift 1 q + closedPlaceLift 3 r + targetTwo c) := by
    rw [← hpc]
    exact hp.1
  exact mixed13_plucker_obstruction q r hq hr c
    (mixed13PluckerZero_of_decomposable q r c hdec)

end

end N5
end UnrestrictedBooleanMul
