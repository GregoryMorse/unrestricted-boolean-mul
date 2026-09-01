import UnrestrictedBooleanMul.N5.MixedPlace

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-!
# Mixed-place exclusion against the degree-two place

This module continues the algebraic Pluecker-certificate proof of strong
mixed-place exclusion.  It treats the three pairs formed by a doubled
rational place and the unique degree-two place.
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

/-- Degree-two effective normal form with first coordinate zero and `q₂=1`. -/
def degreeEffectiveL (q1 q3 : F₂) : LocalKleinParam :=
  ![0, q1, 1, q3]

/-- Degree-two effective normal form with fourth coordinate zero and `q₂=1`. -/
def degreeEffectiveM (q0 q1 : F₂) : LocalKleinParam :=
  ![q0, q1, 1, 0]

/-- Degree-two effective normal form with `q₁=1,q₂=0`. -/
def degreeEffectiveD (q0 q3 : F₂) : LocalKleinParam :=
  ![q0, 1, 0, q3]

/-- The unique degree-two effective parameter with `q₀q₃=1`. -/
def degreeEffectiveG : LocalKleinParam :=
  ![1, 0, 0, 1]

/-- The ten degree-two effective parameters split into four algebraic normal
forms.  The overlap between `L` and `M` is harmless and keeps the interfaces
free of finite enumeration. -/
theorem degreeTwoLocalEffective_cases (q : LocalKleinParam)
    (hq : DegreeTwoLocalEffective q) :
    (∃ q1 q3 : F₂, q = degreeEffectiveL q1 q3) ∨
    (∃ q0 q1 : F₂, q = degreeEffectiveM q0 q1) ∨
    (∃ q0 q3 : F₂, q0 * q3 = 0 ∧ q = degreeEffectiveD q0 q3) ∨
      q = degreeEffectiveG := by
  have hrel := hq
  unfold DegreeTwoLocalEffective at hrel
  rcases f2_eq_zero_or_one (q 2) with h2 | h2
  · rcases f2_eq_zero_or_one (q 1) with h1 | h1
    · have hprod : q 0 * q 3 = 1 := by simpa [h1, h2] using hrel
      have h0 : q 0 = 1 := by
        rcases f2_eq_zero_or_one (q 0) with h0 | h0
        · simp [h0] at hprod
        · exact h0
      have h3 : q 3 = 1 := by
        rcases f2_eq_zero_or_one (q 3) with h3 | h3
        · simp [h3] at hprod
        · exact h3
      right; right; right
      funext i
      fin_cases i <;> simp [degreeEffectiveG, h0, h1, h2, h3]
    · have hprod : q 0 * q 3 = 0 := by
        calc
          q 0 * q 3 = (q 2 + 1) * (q 1 + 1) := hrel
          _ = 0 := by
            rw [h1, h2]
            simp only [zero_add, one_mul]
            exact CharTwo.add_self_eq_zero 1
      right; right; left
      refine ⟨q 0, q 3, hprod, ?_⟩
      funext i
      fin_cases i <;> simp [degreeEffectiveD, h1, h2]
  · have hprod : q 0 * q 3 = 0 := by
      calc
        q 0 * q 3 = (q 2 + 1) * (q 1 + 1) := hrel
        _ = 0 := by
          rw [h2]
          have h11 : (1 : F₂) + 1 = 0 := CharTwo.add_self_eq_zero 1
          rw [h11, zero_mul]
    rcases mul_eq_zero.mp hprod with h0 | h3
    · left
      refine ⟨q 1, q 3, ?_⟩
      funext i
      fin_cases i <;> simp [degreeEffectiveL, h0, h2]
    · right; left
      refine ⟨q 0, q 1, ?_⟩
      funext i
      fin_cases i <;> simp [degreeEffectiveM, h2, h3]

abbrev DegreeAmbientQuad := Fin 4 → Fin 10

def mixed03Quad : Fin 15 → DegreeAmbientQuad :=
  ![![0, 3, 5, 8], ![0, 3, 6, 9], ![1, 4, 6, 9],
    ![1, 2, 5, 8], ![0, 1, 6, 7], ![0, 2, 6, 7],
    ![0, 1, 5, 6], ![1, 4, 5, 8], ![2, 3, 6, 7],
    ![1, 2, 5, 6], ![0, 4, 5, 9], ![0, 5, 6, 7],
    ![0, 2, 7, 8], ![0, 4, 5, 6], ![0, 1, 3, 5]]

def mixed03Equation (q r : LocalKleinParam) (c : TargetCoeff)
    (t : Fin 15) : F₂ :=
  mixedPluckerValue 0 q 3 r c (mixed03Quad t 0) (mixed03Quad t 1)
    (mixed03Quad t 2) (mixed03Quad t 3)

def Mixed03PluckerZero (q r : LocalKleinParam) (c : TargetCoeff) : Prop :=
  ∀ t : Fin 15, mixed03Equation q r c t = 0

theorem mixed03PluckerZero_of_decomposable (q r : LocalKleinParam)
    (c : TargetCoeff)
    (hdec : IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 3 r + targetTwo c)) :
    Mixed03PluckerZero q r c := by
  intro t
  refine mixedPluckerValue_eq_zero_of_decomposable 0 q 3 r c
    (mixed03Quad t 0) (mixed03Quad t 1) (mixed03Quad t 2) (mixed03Quad t 3)
    ?_ ?_ ?_ ?_ ?_ ?_ hdec
  all_goals fin_cases t <;> decide

/-! ## Certificates for `2P₀` against `P⋆` -/

theorem mixed03_AL_identity (q0 q1 q3 r1 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed03Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveL r1 r3) c t
      (c 1 + c 4 + q1*r1) * E 1 + (1 + c 2 + c 0*c 5) * E 2 +
      (q1*c 2 + c 1*c 4 + c 1*c 5 + c 3*c 5 + c 4*c 5 +
        r1*c 7 + c 1*c 7) * E 3 +
      (1 + q1 + c 1 + q0*r3 + r1*c 0 + c 0*c 3 + q1*c 5 +
        c 1*c 5) * E 4 +
      (q0*r3 + c 1*c 4 + c 3*c 4) * E 5 +
      (c 2 + r1*c 2 + c 2*c 3 + c 2*c 5) * E 6 +
      (r1 + c 1 + c 4 + r1*c 2 + c 2*c 4 + c 3*c 5 + q1*c 7 +
        r1*c 7) * E 7 +
      (1 + q1*r1 + q1*c 1 + r1*c 2 + c 2*c 3 + q1*c 5 +
        c 3*c 5 + r1*c 7 + c 1*c 7) * E 8 +
      (q1*c 2 + c 1*c 2 + c 2*c 4 + q1*c 5) * E 9 +
      c 2*c 5 * E 10 +
      (q0 + q0*r1 + q0*c 3 + q0*c 5) * E 11 +
      (r1*c 1 + q1*c 4 + c 2*c 5 + c 3*c 5) * E 12 +
      (c 2 + c 5 + q0*r3 + c 2*c 5 + c 4*c 5) * E 13 +
      r3*c 2 * E 14 := by
  simp [mixed03Equation, mixed03Quad, mixedPluckerValue,
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
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2, five_eq_one_f2]

theorem mixed03_AM_identity (q0 q1 q3 r0 r1 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed03Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveM r0 r1) c t
      (1 + r1 + c 4 + c 2*c 7) * E 1 +
      (1 + c 2 + c 0*c 5) * E 2 +
      (1 + q1 + c 7 + q1*r1 + q1*c 2 + q1*c 4 + c 1*c 4 +
        c 2*c 5) * E 3 +
      (c 7 + q1*c 1 + r1*c 2 + c 1*c 2 + q1*c 7 + r1*c 7 +
        c 1*c 7 + c 3*c 7) * E 4 +
      (c 7 + q1*r1 + q1*c 1 + c 2*c 4 + r1*c 5 + c 1*c 5) * E 5 +
      (c 2 + c 2*c 5) * E 6 +
      (c 1 + c 5 + r1*c 4 + c 1*c 4 + c 1*c 7) * E 7 +
      (r1 + c 5 + c 4*c 5) * E 8 +
      (c 2 + r1*c 2 + c 2*c 3 + c 2*c 5) * E 9 +
      c 2*c 5 * E 10 +
      (q0 + r0*r1 + r0*c 2 + r0*c 3 + q0*c 5) * E 11 +
      (1 + c 3 + c 5 + c 2*c 3) * E 12 + c 2 * E 13 := by
  simp [mixed03Equation, mixed03Quad, mixedPluckerValue,
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
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2, five_eq_one_f2]

theorem mixed03_AD_identity (q0 q1 q3 r0 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed03Equation (rationalEffectiveA q0 q1 q3)
        (degreeEffectiveD r0 r3) c t
      (c 0 + c 2) * E 2 + c 3 * E 3 + E 5 +
      (c 1 + c 2 + c 3) * E 8 + E 9 + (1 + c 2) * E 10 +
      (c 2 + c 3) * E 12 + E 13 + (c 1 + c 2) * (r0*r3) := by
  simp [mixed03Equation, mixed03Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]

theorem mixed03_AG_identity (q0 q1 q3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed03Equation (rationalEffectiveA q0 q1 q3)
        degreeEffectiveG c t
      (c 0*c 4 + q1*c 7 + c 1*c 7) * E 0 +
      (1 + c 0*c 6 + q0*c 7) * E 1 + c 3*c 5 * E 2 +
      q3*c 3 * E 3 + (c 3*c 4 + q1*c 7) * E 4 +
      (q3*c 4 + c 0*c 4) * E 5 + c 3*c 4 * E 6 +
      (1 + c 1 + q3*c 1 + q1*c 3 + q0*c 7) * E 7 +
      (1 + c 3*c 8) * E 8 +
      (q1*c 4 + q3*c 5 + c 1*c 7) * E 9 + c 3*c 8 * E 12 +
      (c 4 + c 0*c 4) * E 13 + q3*c 4 * E 14 := by
  simp [mixed03Equation, mixed03Quad, mixedPluckerValue,
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
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2, five_eq_one_f2]

theorem mixed03_DL_identity (q0 q3 r1 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed03Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveL r1 r3) c t
      c 0 * E 2 + c 2 * E 3 + c 2 * E 4 + E 5 + c 2 * E 6 +
      (1 + r1 + c 1) * E 7 + c 2 * E 8 +
      (1 + r1 + c 2 + c 4) * E 9 + (1 + c 2) * E 10 +
      (1 + r1 + c 1 + c 3) * E 12 + E 13 + c 2 * (q0*q3) := by
  simp [mixed03Equation, mixed03Quad, mixedPluckerValue,
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
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2, five_eq_one_f2]

theorem mixed03_DM_identity (q0 q3 r0 r1 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed03Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveM r0 r1) c t
      (1 + r1 + c 3) * E 1 + c 0 * E 2 + (r1 + c 2) * E 3 +
      (1 + c 5 + c 7) * E 4 + (r1 + c 3) * E 5 +
      (1 + r1 + c 1) * E 7 + (1 + c 1 + c 2 + c 3) * E 8 +
      E 9 + (1 + c 2) * E 10 +
      (1 + r1 + c 1 + c 3) * E 12 + E 13 := by
  simp [mixed03Equation, mixed03Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeEffectiveM,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2, five_eq_one_f2]

theorem mixed03_DD_identity (q0 q3 r0 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed03Equation (rationalEffectiveD q0 q3)
        (degreeEffectiveD r0 r3) c t
      (1 + c 5) * E 1 + (1 + c 2) * E 2 + c 4 * E 3 + c 5 * E 4 +
      (1 + c 2 + c 5) * E 5 + c 5 * E 6 + (1 + c 5) * E 7 +
      c 2 * E 8 + c 5 * E 9 + (1 + c 0) * E 10 + r0 * E 11 +
      c 2 * E 13 + c 5 * (q0*q3) + (1 + c 1) * (r0*r3) := by
  simp [mixed03Equation, mixed03Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [degree_pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2, five_eq_one_f2]

theorem mixed03_DG_identity (q0 q3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed03Equation (rationalEffectiveD q0 q3)
        degreeEffectiveG c t
      (1 + c 0) * E 0 + (1 + c 1) * E 3 + (1 + c 0) * E 4 +
      (1 + c 1 + c 2) * E 5 + (1 + c 0) * E 6 +
      (1 + c 1) * E 7 + (1 + c 0 + c 2) * E 9 + E 11 +
      (1 + c 0) * (q0*q3) := by
  simp [mixed03Equation, mixed03Quad, mixedPluckerValue,
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
    ten_eq_zero_f2, twelve_eq_zero_f2, fourteen_eq_zero_f2, five_eq_one_f2]

/-! ## The `2P₀ + P⋆` obstruction -/

theorem mixed03_AL_obstruction (q0 q1 q3 r1 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed03PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveL r1 r3) c := by
  intro h
  unfold Mixed03PluckerZero at h
  have hid := mixed03_AL_identity q0 q1 q3 r1 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed03_AM_obstruction (q0 q1 q3 r0 r1 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed03PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveM r0 r1) c := by
  intro h
  unfold Mixed03PluckerZero at h
  have hid := mixed03_AM_identity q0 q1 q3 r0 r1 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed03_AD_obstruction (q0 q1 q3 r0 r3 : F₂)
    (c : TargetCoeff) (hr03 : r0 * r3 = 0) :
    ¬ Mixed03PluckerZero (rationalEffectiveA q0 q1 q3)
      (degreeEffectiveD r0 r3) c := by
  intro h
  unfold Mixed03PluckerZero at h
  have hid := mixed03_AD_identity q0 q1 q3 r0 r3 c
  dsimp only at hid
  simp only [h, hr03] at hid
  simp at hid

theorem mixed03_AG_obstruction (q0 q1 q3 : F₂) (c : TargetCoeff) :
    ¬ Mixed03PluckerZero (rationalEffectiveA q0 q1 q3)
      degreeEffectiveG c := by
  intro h
  unfold Mixed03PluckerZero at h
  have hid := mixed03_AG_identity q0 q1 q3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed03_DL_obstruction (q0 q3 r1 r3 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) :
    ¬ Mixed03PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveL r1 r3) c := by
  intro h
  unfold Mixed03PluckerZero at h
  have hid := mixed03_DL_identity q0 q3 r1 r3 c
  dsimp only at hid
  simp only [h, hq03] at hid
  simp at hid

theorem mixed03_DM_obstruction (q0 q3 r0 r1 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed03PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveM r0 r1) c := by
  intro h
  unfold Mixed03PluckerZero at h
  have hid := mixed03_DM_identity q0 q3 r0 r1 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed03_DD_obstruction (q0 q3 r0 r3 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) (hr03 : r0 * r3 = 0) :
    ¬ Mixed03PluckerZero (rationalEffectiveD q0 q3)
      (degreeEffectiveD r0 r3) c := by
  intro h
  unfold Mixed03PluckerZero at h
  have hid := mixed03_DD_identity q0 q3 r0 r3 c
  dsimp only at hid
  simp only [h, hq03, hr03] at hid
  simp at hid

theorem mixed03_DG_obstruction (q0 q3 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) :
    ¬ Mixed03PluckerZero (rationalEffectiveD q0 q3)
      degreeEffectiveG c := by
  intro h
  unfold Mixed03PluckerZero at h
  have hid := mixed03_DG_identity q0 q3 c
  dsimp only at hid
  simp only [h, hq03] at hid
  simp at hid

theorem mixed03_plucker_obstruction (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : DegreeTwoLocalEffective r)
    (c : TargetCoeff) : ¬ Mixed03PluckerZero q r c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, hq03, rfl⟩
  · rcases degreeTwoLocalEffective_cases r hr with hL | hrest
    · rcases hL with ⟨r1, r3, rfl⟩
      exact mixed03_AL_obstruction q0 q1 q3 r1 r3 c
    · rcases hrest with hM | hrest
      · rcases hM with ⟨r0, r1, rfl⟩
        exact mixed03_AM_obstruction q0 q1 q3 r0 r1 c
      · rcases hrest with hD | hG
        · rcases hD with ⟨r0, r3, hr03, rfl⟩
          exact mixed03_AD_obstruction q0 q1 q3 r0 r3 c hr03
        · rw [hG]
          exact mixed03_AG_obstruction q0 q1 q3 c
  · rcases degreeTwoLocalEffective_cases r hr with hL | hrest
    · rcases hL with ⟨r1, r3, rfl⟩
      exact mixed03_DL_obstruction q0 q3 r1 r3 c hq03
    · rcases hrest with hM | hrest
      · rcases hM with ⟨r0, r1, rfl⟩
        exact mixed03_DM_obstruction q0 q3 r0 r1 c
      · rcases hrest with hD | hG
        · rcases hD with ⟨r0, r3, hr03, rfl⟩
          exact mixed03_DD_obstruction q0 q3 r0 r3 c hq03 hr03
        · rw [hG]
          exact mixed03_DG_obstruction q0 q3 c hq03

/-- No decomposable target correction exists for a doubled rational place at
`P₀` together with the unique degree-two place. -/
theorem rational03_mixed_decomposableFiber_empty (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : DegreeTwoLocalEffective r) :
    decomposableFiber
      (closedPlaceQuotientPoint 0 q + closedPlaceQuotientPoint 3 r) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_mixedCandidate_of_mem_decomposableFiber 0 3 q r p hp with
    ⟨c, hpc⟩
  have hdec : IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 3 r + targetTwo c) := by
    rw [← hpc]
    exact hp.1
  exact mixed03_plucker_obstruction q r hq hr c
    (mixed03PluckerZero_of_decomposable q r c hdec)

end

end N5
end UnrestrictedBooleanMul
