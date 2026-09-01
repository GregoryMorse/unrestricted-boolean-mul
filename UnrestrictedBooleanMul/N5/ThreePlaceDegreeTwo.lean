import UnrestrictedBooleanMul.N5.ThreeRationalProfile

set_option linter.unusedSimpArgs false

/-!
# Three-place candidates with the degree-two place

This module extends the algebraic coordinate interface from `MixedPlace` to
sums of three closed-place quotient points.  It is deliberately independent
of any circuit enumeration: a candidate is the sum of three displayed local
Klein lifts and one arbitrary Hankel target form, and decomposability is tested
only through Pluecker identities.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Coordinate model for a putative decomposable lift of the sum of three
closed-place quotient points. -/
def threePlaceCandidateCoeff
    (place₀ : Fin 4) (q₀ : LocalKleinParam)
    (place₁ : Fin 4) (q₁ : LocalKleinParam)
    (place₂ : Fin 4) (q₂ : LocalKleinParam)
    (c : TargetCoeff) (i j : Fin 10) : F₂ :=
  explicitLocalLiftCoeff place₀ q₀ i j +
    explicitLocalLiftCoeff place₁ q₁ i j +
    explicitLocalLiftCoeff place₂ q₂ i j + explicitTargetCoeff c i j

theorem threePlaceCandidate_pair
    (place₀ : Fin 4) (q₀ : LocalKleinParam)
    (place₁ : Fin 4) (q₁ : LocalKleinParam)
    (place₂ : Fin 4) (q₂ : LocalKleinParam)
    (c : TargetCoeff) (i j : Fin 10) (hij : i ≠ j) :
    (closedPlaceLift place₀ q₀ + closedPlaceLift place₁ q₁ +
        closedPlaceLift place₂ q₂ + targetTwo c) (quadraticPair i j hij) =
      threePlaceCandidateCoeff place₀ q₀ place₁ q₁ place₂ q₂ c i j := by
  simp only [Pi.add_apply, threePlaceCandidateCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff]

/-- One Pluecker relation for a three-place candidate. -/
def threePlacePluckerValue
    (place₀ : Fin 4) (q₀ : LocalKleinParam)
    (place₁ : Fin 4) (q₁ : LocalKleinParam)
    (place₂ : Fin 4) (q₂ : LocalKleinParam)
    (c : TargetCoeff) (i j k l : Fin 10) : F₂ :=
  threePlaceCandidateCoeff place₀ q₀ place₁ q₁ place₂ q₂ c i j *
      threePlaceCandidateCoeff place₀ q₀ place₁ q₁ place₂ q₂ c k l +
    threePlaceCandidateCoeff place₀ q₀ place₁ q₁ place₂ q₂ c i k *
      threePlaceCandidateCoeff place₀ q₀ place₁ q₁ place₂ q₂ c j l +
    threePlaceCandidateCoeff place₀ q₀ place₁ q₁ place₂ q₂ c i l *
      threePlaceCandidateCoeff place₀ q₀ place₁ q₁ place₂ q₂ c j k

/-- Every decomposable three-place candidate satisfies every Pluecker
relation on four distinct ambient coordinates. -/
theorem threePlacePluckerValue_eq_zero_of_decomposable
    (place₀ : Fin 4) (q₀ : LocalKleinParam)
    (place₁ : Fin 4) (q₁ : LocalKleinParam)
    (place₂ : Fin 4) (q₂ : LocalKleinParam)
    (c : TargetCoeff) (i j k l : Fin 10)
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjl : j ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k)
    (hdec : IsDecomposableTwo
      (closedPlaceLift place₀ q₀ + closedPlaceLift place₁ q₁ +
        closedPlaceLift place₂ q₂ + targetTwo c)) :
    threePlacePluckerValue
      place₀ q₀ place₁ q₁ place₂ q₂ c i j k l = 0 := by
  rcases hdec with ⟨u, v, huv⟩
  unfold threePlacePluckerValue
  rw [← threePlaceCandidate_pair place₀ q₀ place₁ q₁ place₂ q₂ c i j hij,
    ← threePlaceCandidate_pair place₀ q₀ place₁ q₁ place₂ q₂ c k l hkl,
    ← threePlaceCandidate_pair place₀ q₀ place₁ q₁ place₂ q₂ c i k hik,
    ← threePlaceCandidate_pair place₀ q₀ place₁ q₁ place₂ q₂ c j l hjl,
    ← threePlaceCandidate_pair place₀ q₀ place₁ q₁ place₂ q₂ c i l hil,
    ← threePlaceCandidate_pair place₀ q₀ place₁ q₁ place₂ q₂ c j k hjk,
    huv]
  exact squarefreeWedge_plucker u v i j k l hij hkl hik hjl hil hjk

/-- Every representative of the sum of three displayed quotient points is
the sum of their canonical lifts and one Hankel target form. -/
theorem exists_threePlaceCandidate_of_mem_decomposableFiber
    (place₀ : Fin 4) (q₀ : LocalKleinParam)
    (place₁ : Fin 4) (q₁ : LocalKleinParam)
    (place₂ : Fin 4) (q₂ : LocalKleinParam)
    (p : TwoForm)
    (hp : p ∈ decomposableFiber
      (closedPlaceQuotientPoint place₀ q₀ +
        closedPlaceQuotientPoint place₁ q₁ +
        closedPlaceQuotientPoint place₂ q₂)) :
    ∃ c : TargetCoeff,
      p = closedPlaceLift place₀ q₀ + closedPlaceLift place₁ q₁ +
        closedPlaceLift place₂ q₂ + targetTwo c := by
  let base := closedPlaceLift place₀ q₀ + closedPlaceLift place₁ q₁ +
    closedPlaceLift place₂ q₂
  have hbase : quadraticQuotientProjection base =
      closedPlaceQuotientPoint place₀ q₀ +
        closedPlaceQuotientPoint place₁ q₁ +
        closedPlaceQuotientPoint place₂ q₂ := by
    simp [base, closedPlaceQuotientPoint]
  have hzero : quadraticQuotientProjection (p + base) = 0 := by
    rw [map_add, hp.2, hbase]
    let x : QuadraticQuotient :=
      closedPlaceQuotientPoint place₀ q₀ +
        closedPlaceQuotientPoint place₁ q₁ +
        closedPlaceQuotientPoint place₂ q₂
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

/-! ## The representative `0,1,*` profile -/

/-- A Pluecker equation for the two first rational places and the degree-two
place.  Keeping the ambient quadruple explicit lets each Boolean-ideal
certificate use only the minors it needs. -/
def three013Equation (q r s : LocalKleinParam) (c : TargetCoeff)
    (i j k l : Fin 10) : F₂ :=
  threePlacePluckerValue 0 q 1 r 3 s c i j k l

theorem three013Equation_eq_zero_of_decomposable
    (q r s : LocalKleinParam) (c : TargetCoeff)
    (i j k l : Fin 10)
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjl : j ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k)
    (hdec : IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 1 r +
        closedPlaceLift 3 s + targetTwo c)) :
    three013Equation q r s c i j k l = 0 :=
  threePlacePluckerValue_eq_zero_of_decomposable
    0 q 1 r 3 s c i j k l hij hkl hik hjl hil hjk hdec

/-- Nonlinear normal chart for the degree-two effective parameters with
`s₀=1`.  Its fourth coordinate is solved from the local Klein equation. -/
def degreeTwoEffectiveS (s1 s2 : F₂) : LocalKleinParam :=
  ![1, s1, s2, (s2 + 1) * (s1 + 1)]

/-- Linear normal chart with `s₀=0,s₂=1`. -/
def degreeTwoEffectiveT (s1 s3 : F₂) : LocalKleinParam :=
  ![0, s1, 1, s3]

/-- Terminal normal chart with `s₀=0,s₂=0,s₁=1`. -/
def degreeTwoEffectiveU (s3 : F₂) : LocalKleinParam :=
  ![0, 1, 0, s3]

/-- The ten effective degree-two parameters are covered by three algebraic
normal charts; this is a case split on the Klein equation, not an atlas
enumeration. -/
theorem degreeTwoLocalEffective_threeChart_cases (s : LocalKleinParam)
    (hs : DegreeTwoLocalEffective s) :
    (∃ s1 s2 : F₂, s = degreeTwoEffectiveS s1 s2) ∨
      (∃ s1 s3 : F₂, s = degreeTwoEffectiveT s1 s3) ∨
      ∃ s3 : F₂, s = degreeTwoEffectiveU s3 := by
  by_cases hs0 : s 0 = 1
  · left
    refine ⟨s 1, s 2, ?_⟩
    funext i
    fin_cases i <;> simp [degreeTwoEffectiveS, hs0]
    have h := hs
    simp only [DegreeTwoLocalEffective, hs0, one_mul] at h
    exact h
  · have hs0zero : s 0 = 0 :=
      (f2_eq_zero_or_one (s 0)).resolve_right hs0
    by_cases hs2 : s 2 = 1
    · right; left
      refine ⟨s 1, s 3, ?_⟩
      funext i
      fin_cases i <;> simp [degreeTwoEffectiveT, hs0zero, hs2]
    · have hs2zero : s 2 = 0 :=
        (f2_eq_zero_or_one (s 2)).resolve_right hs2
      have hs1 : s 1 = 1 := by
        have h := hs
        simp only [DegreeTwoLocalEffective, hs0zero, zero_mul,
          hs2zero, zero_add, one_mul] at h
        by_contra hs1
        have hs1zero : s 1 = 0 :=
          (f2_eq_zero_or_one (s 1)).resolve_right hs1
        simp [hs1zero] at h
      right; right
      refine ⟨s 3, ?_⟩
      funext i
      fin_cases i <;> simp [degreeTwoEffectiveU, hs0zero, hs2zero, hs1]

private theorem pow_three_f2_threePlace (x : F₂) : x ^ 3 = x := by
  rw [show 3 = 2 + 1 by omega, pow_succ, N3Certificate.pow_two_f2,
    N3Certificate.mul_self_f2]

private theorem five_eq_one_f2_threePlace : (5 : F₂) = 1 := by decide
private theorem ten_eq_zero_f2_threePlace : (10 : F₂) = 0 := by decide
private theorem twelve_eq_zero_f2_threePlace : (12 : F₂) = 0 := by decide
private theorem fourteen_eq_zero_f2_threePlace : (14 : F₂) = 0 := by decide
private theorem seven_eq_one_f2_threePlace : (7 : F₂) = 1 := by decide
private theorem eighteen_eq_zero_f2_threePlace : (18 : F₂) = 0 := by decide

set_option maxRecDepth 10000 in
/-- Boolean-ideal certificate for two `A` rational charts and the nonlinear
degree-two `S` chart. -/
theorem three013_AAS_identity
    (q0 q1 q3 r0 r1 r3 s1 s2 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      (r0 + q0*s2 + q0*c 3 + q0*c 5 + q1*r0 + r0*s1 +
          r0*c 1 + r0*c 5) *
        three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 3 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 6 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 7 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 8 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 9 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 3 6 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 3 8 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeTwoEffectiveS,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, seven_eq_one_f2_threePlace,
    eighteen_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `A/D/S` Boolean-ideal certificate. -/
theorem three013_ADS_identity
    (q0 q1 q3 r0 r3 s1 s2 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      (q0 + q0*s2 + q0*c 4 + r0*s1 + r0*c 2 + r0*c 4) *
        three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 3 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 7 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 8 +
      three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 3 7 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    degreeTwoEffectiveS, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `D/A/S` Boolean-ideal certificate. -/
theorem three013_DAS_identity
    (q0 q3 r0 r1 r3 s1 s2 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      (r0 + q0*s1 + q0*c 2 + q0*c 4 + r0*s1 + r0*s2 +
          r0*c 0 + r0*c 4) *
        three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 3 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 5 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 6 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 7 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 8 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 3 5 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 3 7 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    degreeTwoEffectiveS, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `D/D/S` Boolean-ideal certificate. -/
theorem three013_DDS_identity
    (q0 q3 r0 r3 s1 s2 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      (r0 + q0*s1 + q0*c 3 + r0*s1 + r0*s2 + r0*c 1 + r0*c 3) *
        three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 3 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 6 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 2 7 +
      three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c
          0 1 3 6 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeTwoEffectiveS,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, seven_eq_one_f2_threePlace,
    eighteen_eq_zero_f2_threePlace]

/-- Vanishing of all legitimate Pluecker equations for the representative
three-place candidate. -/
def Three013PluckerZero (q r s : LocalKleinParam)
    (c : TargetCoeff) : Prop :=
  ∀ i j k l : Fin 10,
    i ≠ j → k ≠ l → i ≠ k → j ≠ l → i ≠ l → j ≠ k →
      three013Equation q r s c i j k l = 0

theorem three013PluckerZero_of_decomposable
    (q r s : LocalKleinParam) (c : TargetCoeff)
    (hdec : IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 1 r +
        closedPlaceLift 3 s + targetTwo c)) :
    Three013PluckerZero q r s c := by
  intro i j k l hij hkl hik hjl hil hjk
  exact three013Equation_eq_zero_of_decomposable q r s c i j k l
    hij hkl hik hjl hil hjk hdec

theorem three013_AAS_obstruction
    (q0 q1 q3 r0 r1 r3 s1 s2 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c := by
  intro h
  have hid := three013_AAS_identity q0 q1 q3 r0 r1 r3 s1 s2 c
  have h0123 := h 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0126 := h 0 1 2 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0127 := h 0 1 2 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0128 := h 0 1 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0129 := h 0 1 2 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0136 := h 0 1 3 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0138 := h 0 1 3 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h0123, h0126, h0127, h0128, h0129, h0136, h0138] at hid
  simp at hid

theorem three013_ADS_obstruction
    (q0 q1 q3 r0 r3 s1 s2 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c := by
  intro h
  have hid := three013_ADS_identity q0 q1 q3 r0 r3 s1 s2 c
  have h0123 := h 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0127 := h 0 1 2 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0128 := h 0 1 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0137 := h 0 1 3 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h0123, h0127, h0128, h0137] at hid
  simp at hid

theorem three013_DAS_obstruction
    (q0 q3 r0 r1 r3 s1 s2 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveS s1 s2) c := by
  intro h
  have hid := three013_DAS_identity q0 q3 r0 r1 r3 s1 s2 c
  have h0123 := h 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0125 := h 0 1 2 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0126 := h 0 1 2 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0127 := h 0 1 2 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0128 := h 0 1 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0135 := h 0 1 3 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0137 := h 0 1 3 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h0123, h0125, h0126, h0127, h0128, h0135, h0137] at hid
  simp at hid

theorem three013_DDS_obstruction
    (q0 q3 r0 r3 s1 s2 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveD r0 r3) (degreeTwoEffectiveS s1 s2) c := by
  intro h
  have hid := three013_DDS_identity q0 q3 r0 r3 s1 s2 c
  have h0123 := h 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0126 := h 0 1 2 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0127 := h 0 1 2 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0136 := h 0 1 3 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h0123, h0126, h0127, h0136] at hid
  simp at hid

/-- No candidate in the nonlinear degree-two chart can satisfy all
Pluecker equations when both rational parameters are effective. -/
theorem three013_S_plucker_obstruction
    (q r : LocalKleinParam) (s1 s2 : F₂)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (c : TargetCoeff) :
    ¬ Three013PluckerZero q r (degreeTwoEffectiveS s1 s2) c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, hq03, rfl⟩
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, hr03, rfl⟩
    · exact three013_AAS_obstruction q0 q1 q3 r0 r1 r3 s1 s2 c
    · exact three013_ADS_obstruction q0 q1 q3 r0 r3 s1 s2 c
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, hr03, rfl⟩
    · exact three013_DAS_obstruction q0 q3 r0 r1 r3 s1 s2 c
    · exact three013_DDS_obstruction q0 q3 r0 r3 s1 s2 c

end

end N5
end UnrestrictedBooleanMul
