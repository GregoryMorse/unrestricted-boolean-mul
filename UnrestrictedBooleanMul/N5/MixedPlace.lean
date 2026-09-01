import UnrestrictedBooleanMul.N5.EffectiveClassification

/-!
# Strong mixed-place exclusion

The proof is organized around Pluecker relations for a decomposable ambient
two-form.  Candidate lifts are evaluated directly in the four displayed
closed-place bases and in the Hankel cross block, keeping the finite
certificate at the level of algebraic coordinates rather than circuits.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem pow_three_f2 (x : F₂) : x ^ 3 = x := by
  rw [show 3 = 2 + 1 by omega, pow_succ, N3Certificate.pow_two_f2,
    N3Certificate.mul_self_f2]

/-- Direct coefficient of the Hankel target on an ambient coordinate pair. -/
def explicitTargetCoeff (c : TargetCoeff) (i j : Fin 10) : F₂ :=
  if hi : i.val < 5 then
    if hj : 5 ≤ j.val then
      c ⟨i.val + (j.val - 5), by omega⟩
    else 0
  else if hj : j.val < 5 then
    c ⟨j.val + (i.val - 5), by omega⟩
  else 0

/-- Coefficient of the canonical local quotient lift, evaluated without
forming an ambient 45-coordinate object. -/
def explicitClosedPlaceBasisCoeff : Fin 4 → Fin 4 → Fin 10 → F₂ :=
  ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]],
    ![![1, 1, 1, 1, 1, 0, 0, 0, 0, 0],
      ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]],
    ![![1, 0, 1, 1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 1, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1]]]

def explicitClosedPlaceCanonicalCoord (place : Fin 4)
    (q : LocalKleinParam) : LocalKleinCoord :=
  ![![q 0, 0, q 1, 0, q 2, q 3],
    ![q 0, 0, q 1, 0, q 2, q 3],
    ![q 0, 0, q 1, 0, q 2, q 3],
    ![q 0, 0, 0, q 1, q 2, q 3]] place

def explicitLocalLiftCoeff (place : Fin 4) (q : LocalKleinParam)
    (i j : Fin 10) : F₂ :=
  ∑ s : Fin 6, explicitClosedPlaceCanonicalCoord place q s *
    (explicitClosedPlaceBasisCoeff place (localKleinPair s).1 i *
        explicitClosedPlaceBasisCoeff place (localKleinPair s).2 j +
      explicitClosedPlaceBasisCoeff place (localKleinPair s).1 j *
        explicitClosedPlaceBasisCoeff place (localKleinPair s).2 i)

/-- Coordinate model for a putative decomposable lift of the sum of two local
quotient points. -/
def mixedCandidateCoeff (place : Fin 4) (q : LocalKleinParam)
    (place' : Fin 4) (q' : LocalKleinParam) (c : TargetCoeff)
    (i j : Fin 10) : F₂ :=
  explicitLocalLiftCoeff place q i j +
    explicitLocalLiftCoeff place' q' i j + explicitTargetCoeff c i j

theorem closedPlaceCanonicalCoord_eq_explicit (place : Fin 4)
    (q : LocalKleinParam) (s : Fin 6) :
    closedPlaceCanonicalCoord place q s =
      explicitClosedPlaceCanonicalCoord place q s := by
  fin_cases place <;> fin_cases s <;>
    simp [closedPlaceCanonicalCoord, rationalCanonicalCoord,
      degreeTwoCanonicalCoord, explicitClosedPlaceCanonicalCoord]

set_option maxHeartbeats 800000 in
theorem closedPlaceLocalBasis_eq_explicit (place r : Fin 4) (i : Fin 10) :
    closedPlaceLocalBasis place r i =
      explicitClosedPlaceBasisCoeff place r i := by
  fin_cases place <;> fin_cases r <;> fin_cases i <;>
    simp [closedPlaceLocalBasis, explicitClosedPlaceBasisCoeff,
      aOneEval, aOneJet, bOneEval, bOneJet, aStarZero, aStarOne,
      bStarZero, bStarOne, aLinear, bLinear, aCoord, bCoord,
      Pi.basisFun, Fin.sum_univ_succ]

private theorem ambientCoord_cases (i : Fin 10) :
    (∃ a : Fin 5, i = aCoord a) ∨ ∃ b : Fin 5, i = bCoord b := by
  by_cases hi : i.val < 5
  · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨i.val - 5, by omega⟩, ?_⟩
    apply Fin.ext
    simp [bCoord]
    omega

private theorem mixedQuadraticPair_swap {m : Nat} (i j : Fin m) (hij : i ≠ j) :
    quadraticPair i j hij = quadraticPair j i hij.symm := by
  apply Subtype.ext
  simp [quadraticPair, Finset.pair_comm]

theorem targetTwo_pair_eq_explicitTargetCoeff (c : TargetCoeff)
    (i j : Fin 10) (hij : i ≠ j) :
    targetTwo c (quadraticPair i j hij) = explicitTargetCoeff c i j := by
  rcases ambientCoord_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;>
    rcases ambientCoord_cases j with ⟨a', rfl⟩ | ⟨b', rfl⟩
  · have haa : a ≠ a' := by
      intro h
      subst a'
      exact hij rfl
    rw [targetTwo_sameA c a a' haa]
    simp [explicitTargetCoeff, aCoord]
  · rw [targetTwo_cross]
    simp [explicitTargetCoeff, aCoord, bCoord, hankelIndex]
  · rw [mixedQuadraticPair_swap, targetTwo_cross]
    simp [explicitTargetCoeff, aCoord, bCoord, hankelIndex]
  · have hbb : b ≠ b' := by
      intro h
      subst b'
      exact hij rfl
    rw [targetTwo_sameB c b b' hbb]
    simp [explicitTargetCoeff, bCoord]

theorem closedPlaceLift_pair_eq_explicitLocalLiftCoeff (place : Fin 4)
    (q : LocalKleinParam) (i j : Fin 10) (hij : i ≠ j) :
    closedPlaceLift place q (quadraticPair i j hij) =
      explicitLocalLiftCoeff place q i j := by
  simp [closedPlaceLift, localTwoForm, explicitLocalLiftCoeff,
    squarefreeWedge_pair, smul_eq_mul,
    closedPlaceCanonicalCoord_eq_explicit,
    closedPlaceLocalBasis_eq_explicit]

theorem mixedCandidate_pair (place : Fin 4) (q : LocalKleinParam)
    (place' : Fin 4) (q' : LocalKleinParam) (c : TargetCoeff)
    (i j : Fin 10) (hij : i ≠ j) :
    (closedPlaceLift place q + closedPlaceLift place' q' + targetTwo c)
        (quadraticPair i j hij) =
      mixedCandidateCoeff place q place' q' c i j := by
  simp only [Pi.add_apply, mixedCandidateCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff]

/-- One Pluecker relation on four ordered ambient coordinates. -/
def mixedPluckerValue (place : Fin 4) (q : LocalKleinParam)
    (place' : Fin 4) (q' : LocalKleinParam) (c : TargetCoeff)
    (i j k l : Fin 10) : F₂ :=
  mixedCandidateCoeff place q place' q' c i j *
      mixedCandidateCoeff place q place' q' c k l +
    mixedCandidateCoeff place q place' q' c i k *
      mixedCandidateCoeff place q place' q' c j l +
    mixedCandidateCoeff place q place' q' c i l *
      mixedCandidateCoeff place q place' q' c j k

/-- Every decomposable ambient two-form satisfies the characteristic-two
Pluecker relation. -/
theorem squarefreeWedge_plucker (u v : LinearForm) (i j k l : Fin 10)
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjl : j ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k) :
    squarefreeWedge u v (quadraticPair i j hij) *
        squarefreeWedge u v (quadraticPair k l hkl) +
      squarefreeWedge u v (quadraticPair i k hik) *
        squarefreeWedge u v (quadraticPair j l hjl) +
      squarefreeWedge u v (quadraticPair i l hil) *
        squarefreeWedge u v (quadraticPair j k hjk) = 0 := by
  simp only [squarefreeWedge_pair]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- A decomposable mixed candidate satisfies every Pluecker relation on four
distinct ambient coordinates. -/
theorem mixedPluckerValue_eq_zero_of_decomposable
    (place : Fin 4) (q : LocalKleinParam)
    (place' : Fin 4) (q' : LocalKleinParam) (c : TargetCoeff)
    (i j k l : Fin 10)
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjl : j ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k)
    (hdec : IsDecomposableTwo
      (closedPlaceLift place q + closedPlaceLift place' q' + targetTwo c)) :
    mixedPluckerValue place q place' q' c i j k l = 0 := by
  rcases hdec with ⟨u, v, huv⟩
  unfold mixedPluckerValue
  rw [← mixedCandidate_pair place q place' q' c i j hij,
    ← mixedCandidate_pair place q place' q' c k l hkl,
    ← mixedCandidate_pair place q place' q' c i k hik,
    ← mixedCandidate_pair place q place' q' c j l hjl,
    ← mixedCandidate_pair place q place' q' c i l hil,
    ← mixedCandidate_pair place q place' q' c j k hjk,
    huv]
  exact squarefreeWedge_plucker u v i j k l hij hkl hik hjl hil hjk

abbrev AmbientQuad := Fin 4 → Fin 10

def mixed01Quad : Fin 13 → AmbientQuad :=
  ![![0, 2, 5, 7], ![1, 3, 6, 8], ![0, 4, 5, 9],
    ![0, 2, 6, 8], ![1, 3, 5, 9], ![0, 1, 5, 6],
    ![1, 4, 6, 7], ![0, 3, 6, 9], ![1, 2, 5, 8],
    ![1, 3, 5, 6], ![0, 1, 6, 8], ![0, 1, 5, 7],
    ![0, 2, 5, 6]]

def mixed02Quad : Fin 14 → AmbientQuad :=
  ![![0, 1, 7, 8], ![0, 2, 5, 7], ![1, 3, 6, 8],
    ![2, 4, 7, 9], ![1, 2, 8, 9], ![0, 4, 5, 9],
    ![0, 3, 6, 9], ![1, 4, 5, 8], ![0, 4, 6, 8],
    ![1, 3, 5, 9], ![0, 3, 6, 8], ![1, 3, 5, 8],
    ![1, 3, 6, 9], ![1, 4, 6, 8]]

def mixed12Quad : Fin 16 → AmbientQuad :=
  ![![0, 2, 5, 7], ![0, 2, 6, 8], ![0, 4, 5, 9],
    ![2, 4, 7, 9], ![1, 3, 7, 8], ![3, 4, 8, 9],
    ![1, 3, 6, 8], ![0, 3, 5, 8], ![1, 3, 5, 9],
    ![2, 4, 6, 8], ![3, 4, 6, 8], ![0, 4, 8, 9],
    ![0, 3, 5, 9], ![1, 3, 6, 9], ![1, 4, 5, 8],
    ![0, 3, 6, 9]]

def mixed01Equation (q q' : LocalKleinParam) (c : TargetCoeff)
    (t : Fin 13) : F₂ :=
  mixedPluckerValue 0 q 1 q' c (mixed01Quad t 0) (mixed01Quad t 1)
    (mixed01Quad t 2) (mixed01Quad t 3)

def mixed02Equation (q q' : LocalKleinParam) (c : TargetCoeff)
    (t : Fin 14) : F₂ :=
  mixedPluckerValue 0 q 2 q' c (mixed02Quad t 0) (mixed02Quad t 1)
    (mixed02Quad t 2) (mixed02Quad t 3)

def mixed12Equation (q q' : LocalKleinParam) (c : TargetCoeff)
    (t : Fin 16) : F₂ :=
  mixedPluckerValue 1 q 2 q' c (mixed12Quad t 0) (mixed12Quad t 1)
    (mixed12Quad t 2) (mixed12Quad t 3)

def rationalEffectiveA (q0 q1 q3 : F₂) : LocalKleinParam :=
  ![q0, q1, 1, q3]

def rationalEffectiveB (q3 : F₂) : LocalKleinParam :=
  ![0, 1, 0, q3]

def rationalEffectiveC (q0 : F₂) : LocalKleinParam :=
  ![q0, 1, 0, 0]

def rationalEffectiveD (q0 q3 : F₂) : LocalKleinParam :=
  ![q0, 1, 0, q3]

/-- A compact Boolean-ideal identity for the `A/B` rational effectiveness
branches.  The right side is a combination of six Pluecker equations. -/
theorem mixed01_AB_identity (q0 q1 q3 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      c 4 * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveB r3) c 0 +
      mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveB r3) c 1 +
      (1 + c 0) * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveB r3) c 2 +
      c 2 * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveB r3) c 6 +
      (1 + c 4) * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveB r3) c 8 +
      (1 + c 5) * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveB r3) c 9 := by
  simp [mixed01Equation, mixed01Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveB,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]

def Mixed01PluckerZero (q q' : LocalKleinParam) (c : TargetCoeff) : Prop :=
  ∀ t : Fin 13, mixed01Equation q q' c t = 0

def Mixed02PluckerZero (q q' : LocalKleinParam) (c : TargetCoeff) : Prop :=
  ∀ t : Fin 14, mixed02Equation q q' c t = 0

def Mixed12PluckerZero (q q' : LocalKleinParam) (c : TargetCoeff) : Prop :=
  ∀ t : Fin 16, mixed12Equation q q' c t = 0

/-- Decomposability forces all thirteen selected equations for the first two
rational places. -/
theorem mixed01PluckerZero_of_decomposable (q r : LocalKleinParam)
    (c : TargetCoeff)
    (hdec : IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 1 r + targetTwo c)) :
    Mixed01PluckerZero q r c := by
  intro t
  refine mixedPluckerValue_eq_zero_of_decomposable 0 q 1 r c
    (mixed01Quad t 0) (mixed01Quad t 1) (mixed01Quad t 2) (mixed01Quad t 3)
    ?_ ?_ ?_ ?_ ?_ ?_ hdec
  all_goals fin_cases t <;> decide

theorem mixed01_AB_obstruction (q0 q1 q3 r3 : F₂) (c : TargetCoeff) :
    ¬ Mixed01PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveB r3) c := by
  intro h
  have hid := mixed01_AB_identity q0 q1 q3 r3 c
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h6 := h 6
  have h8 := h 8
  have h9 := h 9
  rw [h0, h1, h2, h6, h8, h9] at hid
  simp at hid

/-- The companion identity for the other `q₂=0` rational effectiveness
branch. -/
theorem mixed01_AC_identity (q0 q1 q3 r0 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      c 4 * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveC r0) c 0 +
      mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveC r0) c 1 +
      (1 + c 0) * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveC r0) c 2 +
      c 2 * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveC r0) c 6 +
      (1 + c 4) * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveC r0) c 8 +
      (1 + c 5) * mixed01Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveC r0) c 9 := by
  simp [mixed01Equation, mixed01Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveC,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]

theorem mixed01_AC_obstruction (q0 q1 q3 r0 : F₂) (c : TargetCoeff) :
    ¬ Mixed01PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveC r0) c := by
  intro h
  have hid := mixed01_AC_identity q0 q1 q3 r0 c
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h6 := h 6
  have h8 := h 8
  have h9 := h 9
  rw [h0, h1, h2, h6, h8, h9] at hid
  simp at hid

set_option maxRecDepth 10000 in
/-- Boolean-ideal certificate for the branch where both rational local
parameters have `q₂=1`. -/
theorem mixed01_AA_identity (q0 q1 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed01Equation (rationalEffectiveA q0 q1 q3)
        (rationalEffectiveA r0 r1 r3) c t
      (r1 + c 4) * E 0 +
      (1 + q1 + c 2 + c 3 + c 4 + q1*r1 + q1*c 2 + q1*c 5 +
        q1*c 7 + r0*r3 + r1*c 1 + r1*c 2 + r1*c 5 + r1*c 7) * E 1 +
      (1 + r1 + c 0 + r1*c 0) * E 2 +
      (1 + c 2 + c 4 + c 5 + q1*r1 + q1*c 5 + q1*c 7 +
        r1*c 2 + r1*c 3 + r1*c 4 + r1*c 7) * E 3 +
      (c 2 + c 3 + c 4 + q1*c 7 + r0*r3 + r1*c 2 +
        r1*c 3 + r1*c 7) * E 4 +
      (1 + c 2 + c 3 + c 4 + q1*c 5 + q1*c 7 + r0*r3 +
        r1*c 1 + r1*c 2 + r1*c 5 + r1*c 7) * E 6 +
      (q1 + c 2 + c 3 + c 4 + q1*c 5 + r0*r3 + r1*c 1 +
        r1*c 2 + r1*c 3 + r1*c 5) * E 7 +
      (q1 + r1 + c 2 + c 4 + r1*c 2 + r1*c 4) * E 8 +
      E 9 + E 10 := by
  simp [mixed01Equation, mixed01Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, localKleinPair,
    Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  have h10 : (10 : F₂) = 0 := by decide
  have h12 : (12 : F₂) = 0 := by decide
  have h14 : (14 : F₂) = 0 := by decide
  have h15 : (15 : F₂) = 1 := by decide
  have h16 : (16 : F₂) = 0 := by decide
  have h18 : (18 : F₂) = 0 := by decide
  have h28 : (28 : F₂) = 0 := by decide
  simp [pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, h10, h12, h14, h15, h16, h18, h28]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem mixed01_AA_obstruction (q0 q1 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed01PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveA r0 r1 r3) c := by
  intro h
  have hid := mixed01_AA_identity q0 q1 q3 r0 r1 r3 c
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  have h9 := h 9
  have h10 := h 10
  dsimp only at hid
  rw [h0, h1, h2, h3, h4, h6, h7, h8, h9, h10] at hid
  simp at hid

set_option maxRecDepth 10000 in
/-- Unified certificate for the `D/A` branch, where `D` denotes
`q₁=1,q₂=0,q₀q₃=0`. -/
theorem mixed01_DA_identity (q0 q3 r0 r1 r3 : F₂) (c : TargetCoeff)
    (hq : q0 * q3 = 0) :
    (1 : F₂) =
      let E := fun t => mixed01Equation (rationalEffectiveD q0 q3)
        (rationalEffectiveA r0 r1 r3) c t
      (r1 + c 1 + c 2 + c 3 + r1*c 1 + r1*c 4 + r1*c 7 +
        c 2*c 7 + c 3*c 4) * E 0 +
      (r1 + c 1 + q3*r0 + q0*r3 + r0*r3 + r1*c 0 + r1*c 4 +
        c 2*c 3) * E 1 +
      (1 + c 0 + c 1 + c 0*c 1) * E 2 +
      (1 + c 3 + c 5 + r1*c 0 + r1*c 2 + r1*c 5) * E 3 +
      (r1 + c 0 + q3*r0 + q0*r3 + r0*r3 + r1*c 0 + r1*c 1 +
        c 0*c 5 + c 2*c 4 + c 2*c 5) * E 4 +
      (c 2 + c 4 + c 7 + r1*c 2 + r1*c 3 + r1*c 4 + r1*c 7) * E 5 +
      (c 1 + c 2 + q3*r0 + q0*r3 + r0*r3 + r1*c 0 + r1*c 3 +
        c 2*c 4) * E 6 +
      (r1 + c 1 + c 2 + q3*r0 + q0*r3 + r0*r3 + r1*c 2 +
        c 0*c 7 + c 2*c 4 + c 2*c 7) * E 7 +
      (r1 + r1*c 0 + r1*c 2 + r1*c 3 + c 0*c 7 + c 2*c 7) * E 8 +
      (1 + r1 + r1*c 0) * E 9 + E 10 + E 11 + E 12 := by
  simp [mixed01Equation, mixed01Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  have h10 : (10 : F₂) = 0 := by decide
  have h12 : (12 : F₂) = 0 := by decide
  have h14 : (14 : F₂) = 0 := by decide
  have h15 : (15 : F₂) = 1 := by decide
  have h16 : (16 : F₂) = 0 := by decide
  have h18 : (18 : F₂) = 0 := by decide
  have h19 : (19 : F₂) = 1 := by decide
  have h20 : (20 : F₂) = 0 := by decide
  have h28 : (28 : F₂) = 0 := by decide
  rcases mul_eq_zero.mp hq with hq0 | hq3
  · simp [pow_three_f2, hq0, N3Certificate.two_eq_zero_f2,
      N3Certificate.three_eq_one_f2,
      N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, h10, h12, h14, h15, h16, h18, h19, h20, h28]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  · simp [pow_three_f2, hq3, N3Certificate.two_eq_zero_f2,
      N3Certificate.three_eq_one_f2,
      N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, h10, h12, h14, h15, h16, h18, h19, h20, h28]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]

theorem mixed01_DA_obstruction (q0 q3 r0 r1 r3 : F₂) (c : TargetCoeff)
    (hq : q0 * q3 = 0) :
    ¬ Mixed01PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveA r0 r1 r3) c := by
  intro h
  have hid := mixed01_DA_identity q0 q3 r0 r1 r3 c hq
  dsimp only at hid
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  have h9 := h 9
  have h10 := h 10
  have h11 := h 11
  have h12 := h 12
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] at hid
  simp at hid

/-- Compact certificate when both parameters are in the `D` branch. -/
theorem mixed01_DD_identity (q0 q3 r0 r3 : F₂) (c : TargetCoeff)
    (hq : q0 * q3 = 0) (hr : r0 * r3 = 0) :
    (1 : F₂) =
      let E := fun t => mixed01Equation (rationalEffectiveD q0 q3)
        (rationalEffectiveD r0 r3) c t
      c 4 * E 0 + E 1 + (1 + c 0) * E 2 + E 3 + E 4 +
        E 6 + E 7 + E 8 := by
  simp [mixed01Equation, mixed01Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, localKleinPair,
    Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  have h5 : (5 : F₂) = 1 := by decide
  simp [hq, hr, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2, h5]

theorem mixed01_DD_obstruction (q0 q3 r0 r3 : F₂) (c : TargetCoeff)
    (hq : q0 * q3 = 0) (hr : r0 * r3 = 0) :
    ¬ Mixed01PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveD r0 r3) c := by
  intro h
  have hid := mixed01_DD_identity q0 q3 r0 r3 c hq hr
  dsimp only at hid
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  rw [h0, h1, h2, h3, h4, h6, h7, h8] at hid
  simp at hid

/-- Every effective doubled-rational parameter has one of the two normal
forms used by the symbolic mixed-place certificates. -/
theorem rationalLocalEffective_cases (q : LocalKleinParam)
    (hq : RationalLocalEffective q) :
    (∃ q0 q1 q3 : F₂, q = rationalEffectiveA q0 q1 q3) ∨
      ∃ q0 q3 : F₂, q0 * q3 = 0 ∧ q = rationalEffectiveD q0 q3 := by
  rcases hq with hq2 | ⟨hq2, hq1, hq03⟩
  · left
    refine ⟨q 0, q 1, q 3, ?_⟩
    funext i
    fin_cases i <;> simp [rationalEffectiveA, hq2]
  · right
    refine ⟨q 0, q 3, hq03, ?_⟩
    funext i
    fin_cases i <;> simp [rationalEffectiveD, hq2, hq1]

/-- The selected Pluecker equations cannot vanish for two effective
doubled-rational parameters at the first two rational places. -/
theorem mixed01_plucker_obstruction (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (c : TargetCoeff) : ¬ Mixed01PluckerZero q r c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, hq03, rfl⟩
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, hr03, rfl⟩
    · exact mixed01_AA_obstruction q0 q1 q3 r0 r1 r3 c
    · rcases mul_eq_zero.mp hr03 with hr0 | hr3
      · subst r0
        simpa [rationalEffectiveD, rationalEffectiveB] using
          mixed01_AB_obstruction q0 q1 q3 r3 c
      · subst r3
        simpa [rationalEffectiveD, rationalEffectiveC] using
          mixed01_AC_obstruction q0 q1 q3 r0 c
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, hr03, rfl⟩
    · exact mixed01_DA_obstruction q0 q3 r0 r1 r3 c hq03
    · exact mixed01_DD_obstruction q0 q3 r0 r3 c hq03 hr03

/-- Every representative of the sum of two displayed quotient points is the
sum of their canonical lifts and one Hankel target form. -/
theorem exists_mixedCandidate_of_mem_decomposableFiber
    (place place' : Fin 4) (q r : LocalKleinParam) (p : TwoForm)
    (hp : p ∈ decomposableFiber
      (closedPlaceQuotientPoint place q +
        closedPlaceQuotientPoint place' r)) :
    ∃ c : TargetCoeff,
      p = closedPlaceLift place q + closedPlaceLift place' r + targetTwo c := by
  let base := closedPlaceLift place q + closedPlaceLift place' r
  have hbase : quadraticQuotientProjection base =
      closedPlaceQuotientPoint place q +
        closedPlaceQuotientPoint place' r := by
    simp [base, closedPlaceQuotientPoint]
  have hzero : quadraticQuotientProjection (p + base) = 0 := by
    rw [map_add, hp.2, hbase]
    let x : QuadraticQuotient :=
      closedPlaceQuotientPoint place q + closedPlaceQuotientPoint place' r
    change x + x = 0
    calc
      x + x = (1 : F₂) • x + (1 : F₂) • x := by simp
      _ = ((1 : F₂) + 1) • x := (add_smul 1 1 x).symm
      _ = 0 := by
        have h11 : (1 : F₂) + 1 = 0 := by decide
        rw [h11, zero_smul]
  have htarget : p + base ∈ targetTwoSpace :=
    (quadraticQuotientProjection_eq_zero_iff _).1 hzero
  rcases htarget with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  change targetTwo c = p + base at hc
  change p = base + targetTwo c
  rw [hc]
  funext s
  simp only [Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- The decomposable fiber over the sum of effective quotient points at the
first two rational places is empty. -/
theorem rational01_mixed_decomposableFiber_empty (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r) :
    decomposableFiber
      (closedPlaceQuotientPoint 0 q + closedPlaceQuotientPoint 1 r) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_mixedCandidate_of_mem_decomposableFiber 0 1 q r p hp with
    ⟨c, hpc⟩
  have hdec : IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 1 r + targetTwo c) := by
    rw [← hpc]
    exact hp.1
  exact mixed01_plucker_obstruction q r hq hr c
    (mixed01PluckerZero_of_decomposable q r c hdec)

/-! ## The other rational-place pairs -/

/-- Boolean-ideal certificate for the `A/A` branches at `2P₀,2P∞`. -/
theorem mixed02_AA_identity (q0 q1 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed02Equation (rationalEffectiveA q0 q1 q3)
        (rationalEffectiveA r0 r1 r3) c t
      (1 + c 3 + c 4) * E 0 + (1 + c 6) * E 1 +
      (1 + q1 + c 1 + c 6) * E 2 + (1 + c 4 + c 0*c 4) * E 3 +
      (1 + c 0 + c 4) * E 5 + (1 + q1 + c 1) * E 6 +
      (1 + c 2) * E 10 := by
  simp [mixed02Equation, mixed02Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, localKleinPair,
    Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Boolean-ideal certificate for the `A/D` branches at `2P₀,2P∞`. -/
theorem mixed02_AD_identity (q0 q1 q3 r0 r3 : F₂)
    (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed02Equation (rationalEffectiveA q0 q1 q3)
        (rationalEffectiveD r0 r3) c t
      (1 + c 3 + c 4) * E 0 + E 1 + (q1 + c 1) * E 2 +
      (1 + c 0) * E 5 + (1 + q1 + c 1) * E 6 +
      (1 + c 2) * E 10 + E 12 + E 13 := by
  simp [mixed02Equation, mixed02Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Boolean-ideal certificate for the `D/A` branches at `2P₀,2P∞`. -/
theorem mixed02_DA_identity (q0 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed02Equation (rationalEffectiveD q0 q3)
        (rationalEffectiveA r0 r1 r3) c t
      (1 + c 4) * E 3 + c 4 * E 4 + c 2 * E 6 + c 2 * E 7 +
      E 10 + E 11 + (1 + c 1) * E 12 + c 1 * E 13 := by
  simp [mixed02Equation, mixed02Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]

/-- Boolean-ideal certificate for the `D/D` branches at `2P₀,2P∞`. -/
theorem mixed02_DD_identity (q0 q3 r0 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed02Equation (rationalEffectiveD q0 q3)
        (rationalEffectiveD r0 r3) c t
      E 6 + E 7 + E 8 + E 9 := by
  simp [mixed02Equation, mixed02Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, localKleinPair,
    Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  simp [pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]

theorem mixed02_AA_obstruction (q0 q1 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed02PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveA r0 r1 r3) c := by
  intro h
  unfold Mixed02PluckerZero at h
  have hid := mixed02_AA_identity q0 q1 q3 r0 r1 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed02_AD_obstruction (q0 q1 q3 r0 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed02PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveD r0 r3) c := by
  intro h
  unfold Mixed02PluckerZero at h
  have hid := mixed02_AD_identity q0 q1 q3 r0 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed02_DA_obstruction (q0 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed02PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveA r0 r1 r3) c := by
  intro h
  unfold Mixed02PluckerZero at h
  have hid := mixed02_DA_identity q0 q3 r0 r1 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed02_DD_obstruction (q0 q3 r0 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed02PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveD r0 r3) c := by
  intro h
  unfold Mixed02PluckerZero at h
  have hid := mixed02_DD_identity q0 q3 r0 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed02_plucker_obstruction (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (c : TargetCoeff) : ¬ Mixed02PluckerZero q r c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, _, rfl⟩
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, _, rfl⟩
    · exact mixed02_AA_obstruction q0 q1 q3 r0 r1 r3 c
    · exact mixed02_AD_obstruction q0 q1 q3 r0 r3 c
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, _, rfl⟩
    · exact mixed02_DA_obstruction q0 q3 r0 r1 r3 c
    · exact mixed02_DD_obstruction q0 q3 r0 r3 c

theorem mixed02PluckerZero_of_decomposable (q r : LocalKleinParam)
    (c : TargetCoeff)
    (hdec : IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 2 r + targetTwo c)) :
    Mixed02PluckerZero q r c := by
  intro t
  refine mixedPluckerValue_eq_zero_of_decomposable 0 q 2 r c
    (mixed02Quad t 0) (mixed02Quad t 1) (mixed02Quad t 2) (mixed02Quad t 3)
    ?_ ?_ ?_ ?_ ?_ ?_ hdec
  all_goals fin_cases t <;> decide

theorem rational02_mixed_decomposableFiber_empty (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r) :
    decomposableFiber
      (closedPlaceQuotientPoint 0 q + closedPlaceQuotientPoint 2 r) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_mixedCandidate_of_mem_decomposableFiber 0 2 q r p hp with
    ⟨c, hpc⟩
  have hdec : IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 2 r + targetTwo c) := by
    rw [← hpc]
    exact hp.1
  exact mixed02_plucker_obstruction q r hq hr c
    (mixed02PluckerZero_of_decomposable q r c hdec)

/-- Boolean-ideal certificate for the `A/A` branches at `2P₁,2P∞`. -/
theorem mixed12_AA_identity (q0 q1 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed12Equation (rationalEffectiveA q0 q1 q3)
        (rationalEffectiveA r0 r1 r3) c t
      (q1 + c 6) * E 0 + (q1 + c 3 + c 6 + q1*c 3) * E 1 +
      (1 + c 8) * E 2 + E 3 + (c 2 + c 5 + q1*c 2) * E 4 +
      (1 + c 3 + q1*c 3) * E 6 + c 4 * E 7 +
      (c 1 + q1*c 1) * E 8 + (1 + q1 + c 4) * E 9 +
      (q1 + c 1 + c 3) * E 10 + (c 2 + q1*c 2) * E 13 +
      (1 + q1 + c 4) * E 14 + (1 + q1) * E 15 := by
  simp [mixed12Equation, mixed12Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, localKleinPair,
    Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  have h10 : (10 : F₂) = 0 := by decide
  have h12 : (12 : F₂) = 0 := by decide
  have h18 : (18 : F₂) = 0 := by decide
  have h30 : (30 : F₂) = 0 := by decide
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, h10, h12, h18, h30]

/-- Boolean-ideal certificate for the `A/D` branches at `2P₁,2P∞`. -/
theorem mixed12_AD_identity (q0 q1 q3 r0 r3 : F₂)
    (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed12Equation (rationalEffectiveA q0 q1 q3)
        (rationalEffectiveD r0 r3) c t
      (c 4 + c 6 + c 7) * E 0 + q1 * E 1 +
      (c 0 + c 4 + c 8) * E 2 + (1 + q1 + c 0 + c 3) * E 3 +
      (c 3 + c 4 + c 6 + c 7) * E 4 + (1 + q1 + c 2) * E 6 +
      (1 + c 4 + c 5 + c 6 + c 7) * E 7 +
      (q1 + c 3 + c 4 + c 5 + c 6) * E 8 +
      (q1 + c 1 + c 3 + c 4 + c 6) * E 9 +
      (1 + c 0 + c 3 + c 4 + c 5) * E 10 + c 4 * E 11 +
      c 6 * E 12 + E 13 + (q1 + c 3 + c 5) * E 14 +
      (1 + q1 + c 3 + c 4 + c 6 + c 7) * E 15 := by
  simp [mixed12Equation, mixed12Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  have h10 : (10 : F₂) = 0 := by decide
  have h12 : (12 : F₂) = 0 := by decide
  have h14 : (14 : F₂) = 0 := by decide
  have h24 : (24 : F₂) = 0 := by decide
  have h26 : (26 : F₂) = 0 := by decide
  simp [N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2,
    h10, h12, h14, h24, h26]

/-- Boolean-ideal certificate for the `D/A` branches at `2P₁,2P∞`.
The final summand is precisely the `D`-branch effectiveness equation. -/
theorem mixed12_DA_identity (q0 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed12Equation (rationalEffectiveD q0 q3)
        (rationalEffectiveA r0 r1 r3) c t
      c 4 * E 2 + (1 + c 0 + c 4) * E 3 + (c 5 + c 6) * E 4 +
      E 7 + (1 + c 4) * E 9 + (1 + c 3 + c 4) * E 10 + q0*q3 := by
  simp [mixed12Equation, mixed12Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  have h5 : (5 : F₂) = 1 := by decide
  simp [N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2, h5]

/-- Boolean-ideal certificate for the `D/D` branches at `2P₁,2P∞`. -/
theorem mixed12_DD_identity (q0 q3 r0 r3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun t => mixed12Equation (rationalEffectiveD q0 q3)
        (rationalEffectiveD r0 r3) c t
      E 1 + (1 + c 2) * E 4 + c 3 * E 6 + (1 + c 3) * E 8 +
      (1 + c 1) * E 9 + E 12 + (1 + c 2) * E 13 +
      (c 0 + c 2 + c 3) * E 14 + (c 0 + c 2 + c 3) * E 15 := by
  simp [mixed12Equation, mixed12Quad, mixedPluckerValue,
    mixedCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, localKleinPair,
    Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, N3Certificate.three_eq_one_f2]
  ring_nf
  simp [pow_three_f2, N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]
  ring_nf
  have h5 : (5 : F₂) = 1 := by decide
  simp [N3Certificate.six_eq_zero_f2, N3Certificate.eight_eq_zero_f2, h5]

theorem mixed12_AA_obstruction (q0 q1 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed12PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveA r0 r1 r3) c := by
  intro h
  unfold Mixed12PluckerZero at h
  have hid := mixed12_AA_identity q0 q1 q3 r0 r1 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed12_AD_obstruction (q0 q1 q3 r0 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed12PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveD r0 r3) c := by
  intro h
  unfold Mixed12PluckerZero at h
  have hid := mixed12_AD_identity q0 q1 q3 r0 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed12_DA_obstruction (q0 q3 r0 r1 r3 : F₂)
    (c : TargetCoeff) (hq03 : q0 * q3 = 0) :
    ¬ Mixed12PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveA r0 r1 r3) c := by
  intro h
  unfold Mixed12PluckerZero at h
  have hid := mixed12_DA_identity q0 q3 r0 r1 r3 c
  dsimp only at hid
  simp only [h, hq03] at hid
  simp at hid

theorem mixed12_DD_obstruction (q0 q3 r0 r3 : F₂)
    (c : TargetCoeff) :
    ¬ Mixed12PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveD r0 r3) c := by
  intro h
  unfold Mixed12PluckerZero at h
  have hid := mixed12_DD_identity q0 q3 r0 r3 c
  dsimp only at hid
  simp only [h] at hid
  simp at hid

theorem mixed12_plucker_obstruction (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (c : TargetCoeff) : ¬ Mixed12PluckerZero q r c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, hq03, rfl⟩
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, _, rfl⟩
    · exact mixed12_AA_obstruction q0 q1 q3 r0 r1 r3 c
    · exact mixed12_AD_obstruction q0 q1 q3 r0 r3 c
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, _, rfl⟩
    · exact mixed12_DA_obstruction q0 q3 r0 r1 r3 c hq03
    · exact mixed12_DD_obstruction q0 q3 r0 r3 c

theorem mixed12PluckerZero_of_decomposable (q r : LocalKleinParam)
    (c : TargetCoeff)
    (hdec : IsDecomposableTwo
      (closedPlaceLift 1 q + closedPlaceLift 2 r + targetTwo c)) :
    Mixed12PluckerZero q r c := by
  intro t
  refine mixedPluckerValue_eq_zero_of_decomposable 1 q 2 r c
    (mixed12Quad t 0) (mixed12Quad t 1) (mixed12Quad t 2) (mixed12Quad t 3)
    ?_ ?_ ?_ ?_ ?_ ?_ hdec
  all_goals fin_cases t <;> decide

theorem rational12_mixed_decomposableFiber_empty (q r : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r) :
    decomposableFiber
      (closedPlaceQuotientPoint 1 q + closedPlaceQuotientPoint 2 r) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_mixedCandidate_of_mem_decomposableFiber 1 2 q r p hp with
    ⟨c, hpc⟩
  have hdec : IsDecomposableTwo
      (closedPlaceLift 1 q + closedPlaceLift 2 r + targetTwo c) := by
    rw [← hpc]
    exact hp.1
  exact mixed12_plucker_obstruction q r hq hr c
    (mixed12PluckerZero_of_decomposable q r c hdec)

end

end N5
end UnrestrictedBooleanMul
