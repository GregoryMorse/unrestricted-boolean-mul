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
private theorem sixteen_eq_zero_f2_threePlace : (16 : F₂) = 0 := by decide
private theorem twenty_eq_zero_f2_threePlace : (20 : F₂) = 0 := by decide
private theorem twenty_two_eq_zero_f2_threePlace : (22 : F₂) = 0 := by decide
private theorem twenty_four_eq_zero_f2_threePlace : (24 : F₂) = 0 := by decide
private theorem twenty_six_eq_zero_f2_threePlace : (26 : F₂) = 0 := by decide
private theorem thirty_eq_zero_f2_threePlace : (30 : F₂) = 0 := by decide
private theorem thirty_two_eq_zero_f2_threePlace : (32 : F₂) = 0 := by decide
private theorem thirty_four_eq_zero_f2_threePlace : (34 : F₂) = 0 := by decide
private theorem nine_eq_one_f2_threePlace : (9 : F₂) = 1 := by decide
private theorem twenty_eight_eq_zero_f2_threePlace : (28 : F₂) = 0 := by decide
private theorem thirty_eight_eq_zero_f2_threePlace : (38 : F₂) = 0 := by decide

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

/-! ## The linear degree-two `T` chart -/

set_option maxRecDepth 10000 in
/-- `A/A/T` Boolean-ideal certificate. -/
theorem three013_AAT_identity
    (q0 q1 q3 r0 r1 r3 s1 s3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun i j k l =>
        three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveT s1 s3) c
          i j k l
      (c 4 + c 8 + r1*s1 + r1*c 4 + s1*c 5 + s1*c 7 +
          s1*c 8 + c 3*c 5 + c 3*c 7 + c 4*c 5 + c 5*c 6 +
          c 5*c 7 + c 6*c 8) * E 2 3 7 8 +
      (1 + r1 + c 4 + c 5 + c 6 + c 7 + r0*s3 + r1*s1 +
          r1*c 3 + r1*c 4 + r1*c 7 + s1*c 3 + s1*c 5 +
          s1*c 6 + s1*c 7 + c 3*c 5 + c 3*c 7 + c 4*c 5 +
          c 6*c 7) * E 1 2 8 9 +
      (c 4 + c 5 + c 6 + r0*r3 + r0*s3 + r1*s1 + r1*c 4 +
          s1*c 3 + s1*c 4 + c 0*c 7 + c 3*c 4 + c 3*c 5) *
        E 3 4 7 9 +
      (s1 + c 3 + c 4 + c 6 + c 7 + c 8 + r0*s3 + r1*c 7 +
          s1*c 3 + s1*c 5 + s1*c 7 + s1*c 8 + c 5*c 8 +
          c 6*c 8) * E 2 3 6 7 +
      (1 + s1 + c 3 + c 4 + c 5 + c 6 + c 7 + r0*s3 +
          r1*s1 + r1*c 7 + s1*c 7 + c 3*c 7 + c 4*c 7 +
          c 5*c 8) * E 0 3 5 9 +
      (1 + r1 + c 3 + c 4 + c 5 + c 6 + r1*s1 + r1*c 3 +
          r1*c 7 + s1*c 4 + s1*c 5 + c 4*c 7 + c 5*c 8) *
        E 1 2 7 9 +
      (r1 + s1 + c 3 + c 4 + c 7 + r0*s3 + r1*c 3 +
          s1*c 5 + s1*c 6 + c 5*c 6 + c 5*c 7) * E 1 4 7 8 +
      (1 + r1 + s1 + r1*s1) * E 0 4 5 8 +
      (s1 + c 6) * E 1 4 5 7 + E 0 3 8 9 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeTwoEffectiveT,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, sixteen_eq_zero_f2_threePlace,
    eighteen_eq_zero_f2_threePlace, twenty_eq_zero_f2_threePlace,
    twenty_two_eq_zero_f2_threePlace, twenty_four_eq_zero_f2_threePlace,
    twenty_six_eq_zero_f2_threePlace, thirty_eq_zero_f2_threePlace,
    thirty_two_eq_zero_f2_threePlace, thirty_four_eq_zero_f2_threePlace,
    seven_eq_one_f2_threePlace, nine_eq_one_f2_threePlace,
    twenty_eight_eq_zero_f2_threePlace, thirty_eight_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `A/D/T` Boolean-ideal certificate.  The final factor is precisely the
`D`-chart Klein constraint. -/
theorem three013_ADT_identity
    (q0 q1 q3 r0 r3 s1 s3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun i j k l =>
        three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveT s1 s3) c
          i j k l
      (s1 + c 4 + s1*c 5 + s1*c 6 + c 5*c 6) * E 1 2 7 8 +
      (1 + s1 + c 4 + s1*c 5 + s1*c 6 + c 5*c 6) * E 3 4 6 7 +
      E 2 3 6 8 + (1 + c 3 + c 6) * E 0 2 8 9 + r0*r3 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    degreeTwoEffectiveT, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, sixteen_eq_zero_f2_threePlace,
    eighteen_eq_zero_f2_threePlace, twenty_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `D/A/T` Boolean-ideal certificate. -/
theorem three013_DAT_identity
    (q0 q3 r0 r1 r3 s1 s3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun i j k l =>
        three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveT s1 s3) c
          i j k l
      (s1 + c 2 + c 3 + c 4 + c 7 + r1*c 4 + r1*c 6 +
          s1*c 2 + s1*c 4 + s1*c 5 + s1*c 6 + s1*c 7 +
          c 2*c 4 + c 3*c 7 + c 4*c 6 + c 5*c 6) * E 1 4 5 7 +
      (r1 + c 1 + c 2 + c 4 + c 5 + c 6 + r0*s3 + r1*c 3 +
          r1*c 5 + r1*c 6 + s1*c 1 + s1*c 5 + s1*c 6 +
          c 1*c 6 + c 2*c 5 + c 2*c 7 + c 3*c 6 + c 4*c 7 +
          c 5*c 7 + c 6*c 7) * E 1 4 7 8 +
      (1 + s1 + c 2 + c 3 + c 4 + c 7 + r1*s1 + r1*c 6 +
          r1*c 7 + s1*c 3 + s1*c 5 + s1*c 6 + c 2*c 3 +
          c 2*c 5 + c 2*c 6 + c 3*c 5 + c 3*c 6 + c 4*c 5 +
          c 4*c 7 + c 5*c 7) * E 3 4 6 7 +
      (1 + r1 + s1 + r0*r3 + r0*s3 + r1*c 6 + r1*c 7 +
          s1*c 5 + s1*c 7 + c 5*c 6 + c 5*c 7) * E 3 4 7 9 +
      (1 + r1 + c 1 + c 3 + r0*s3 + r1*c 2 + r1*c 5 +
          r1*c 6 + r1*c 7 + s1*c 1 + c 1*c 6 + c 2*c 3 +
          c 2*c 5 + c 4*c 7 + c 5*c 6) * E 1 2 6 7 +
      (s1 + c 3 + r0*s3 + r1*c 2 + r1*c 3 + r1*c 6 +
          s1*c 3 + s1*c 4 + s1*c 7 + c 2*c 3 + c 2*c 5 +
          c 3*c 5 + c 4*c 5 + c 4*c 7 + c 5*c 6 + c 5*c 8) *
        E 2 3 8 9 +
      (r1 + s1 + c 2 + c 3 + r0*r3 + r0*s3 + r1*c 2 +
          r1*c 7 + s1*c 7 + c 2*c 3 + c 3*c 6 + c 4*c 5 +
          c 5*c 6) * E 0 2 7 9 +
      (r1 + c 2 + c 3 + c 4 + c 6 + r1*s1 + r1*c 2) * E 2 3 6 7 +
      (r1 + c 4 + r1*c 2 + c 2*c 3 + c 2*c 7) * E 0 3 8 9 +
      E 1 3 6 8 + (1 + r1 + c 6) * E 2 4 5 8 +
      (1 + r1 + s1 + c 7) * E 0 4 5 8 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    degreeTwoEffectiveT, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, sixteen_eq_zero_f2_threePlace,
    eighteen_eq_zero_f2_threePlace, twenty_eq_zero_f2_threePlace,
    twenty_two_eq_zero_f2_threePlace, twenty_four_eq_zero_f2_threePlace,
    twenty_six_eq_zero_f2_threePlace, thirty_eq_zero_f2_threePlace,
    thirty_two_eq_zero_f2_threePlace, thirty_four_eq_zero_f2_threePlace,
    seven_eq_one_f2_threePlace, nine_eq_one_f2_threePlace,
    twenty_eight_eq_zero_f2_threePlace, thirty_eight_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `D/D/T` Boolean-ideal certificate. -/
theorem three013_DDT_identity
    (q0 q3 r0 r3 s1 s3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun i j k l =>
        three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveT s1 s3) c
          i j k l
      c 4*c 6 * E 2 3 5 6 +
      (s1 + c 0 + c 3 + c 4 + s1*c 0 + s1*c 2 + c 0*c 7 +
          c 3*c 4 + c 4*c 5) * E 2 3 6 7 +
      (1 + s1*c 3) * E 1 4 7 8 + q3*c 6 * E 0 1 2 9 +
      (1 + c 5 + r0*r3 + r0*s3 + s1*c 3 + c 3*c 4 +
          c 4*c 5) * E 0 3 8 9 +
      (1 + c 0 + c 3 + c 5 + c 7 + s1*c 0 + s1*c 2 +
          c 0*c 7 + c 3*c 7) * E 1 2 7 8 +
      E 2 3 6 8 +
      (1 + c 3 + c 5 + c 7 + s1*c 3 + s1*c 4 + c 5*c 7) *
        E 0 4 5 8 + s1 * E 1 2 6 7 + E 1 2 7 9 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeTwoEffectiveT,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, sixteen_eq_zero_f2_threePlace,
    eighteen_eq_zero_f2_threePlace, twenty_eq_zero_f2_threePlace,
    twenty_two_eq_zero_f2_threePlace, twenty_four_eq_zero_f2_threePlace,
    twenty_six_eq_zero_f2_threePlace, thirty_eq_zero_f2_threePlace,
    thirty_two_eq_zero_f2_threePlace, thirty_four_eq_zero_f2_threePlace,
    nine_eq_one_f2_threePlace]

theorem three013_AAT_obstruction
    (q0 q1 q3 r0 r1 r3 s1 s3 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveT s1 s3) c := by
  intro h
  have hid := three013_AAT_identity q0 q1 q3 r0 r1 r3 s1 s3 c
  dsimp only at hid
  have h2378 := h 2 3 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1289 := h 1 2 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h3479 := h 3 4 7 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2367 := h 2 3 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0359 := h 0 3 5 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1279 := h 1 2 7 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1478 := h 1 4 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0458 := h 0 4 5 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1457 := h 1 4 5 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0389 := h 0 3 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h2378, h1289, h3479, h2367, h0359, h1279, h1478,
    h0458, h1457, h0389] at hid
  simp at hid

theorem three013_ADT_obstruction
    (q0 q1 q3 r0 r3 s1 s3 : F₂) (c : TargetCoeff)
    (hr03 : r0*r3 = 0) :
    ¬ Three013PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveD r0 r3) (degreeTwoEffectiveT s1 s3) c := by
  intro h
  have hid := three013_ADT_identity q0 q1 q3 r0 r3 s1 s3 c
  dsimp only at hid
  have h1278 := h 1 2 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h3467 := h 3 4 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2368 := h 2 3 6 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0289 := h 0 2 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h1278, h3467, h2368, h0289, hr03] at hid
  simp at hid

theorem three013_DAT_obstruction
    (q0 q3 r0 r1 r3 s1 s3 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveT s1 s3) c := by
  intro h
  have hid := three013_DAT_identity q0 q3 r0 r1 r3 s1 s3 c
  dsimp only at hid
  have h1457 := h 1 4 5 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1478 := h 1 4 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h3467 := h 3 4 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h3479 := h 3 4 7 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1267 := h 1 2 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2389 := h 2 3 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0279 := h 0 2 7 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2367 := h 2 3 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0389 := h 0 3 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1368 := h 1 3 6 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2458 := h 2 4 5 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0458 := h 0 4 5 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h1457, h1478, h3467, h3479, h1267, h2389, h0279, h2367,
    h0389, h1368, h2458, h0458] at hid
  simp at hid

theorem three013_DDT_obstruction
    (q0 q3 r0 r3 s1 s3 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveD r0 r3) (degreeTwoEffectiveT s1 s3) c := by
  intro h
  have hid := three013_DDT_identity q0 q3 r0 r3 s1 s3 c
  dsimp only at hid
  have h2356 := h 2 3 5 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2367 := h 2 3 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1478 := h 1 4 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0129 := h 0 1 2 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0389 := h 0 3 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1278 := h 1 2 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2368 := h 2 3 6 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0458 := h 0 4 5 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1267 := h 1 2 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1279 := h 1 2 7 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h2356, h2367, h1478, h0129, h0389, h1278, h2368, h0458,
    h1267, h1279] at hid
  simp at hid

/-- No candidate in the linear `T` chart can satisfy all Pluecker equations
when both rational parameters are effective. -/
theorem three013_T_plucker_obstruction
    (q r : LocalKleinParam) (s1 s3 : F₂)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (c : TargetCoeff) :
    ¬ Three013PluckerZero q r (degreeTwoEffectiveT s1 s3) c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, hq03, rfl⟩
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, hr03, rfl⟩
    · exact three013_AAT_obstruction q0 q1 q3 r0 r1 r3 s1 s3 c
    · exact three013_ADT_obstruction q0 q1 q3 r0 r3 s1 s3 c hr03
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, hr03, rfl⟩
    · exact three013_DAT_obstruction q0 q3 r0 r1 r3 s1 s3 c
    · exact three013_DDT_obstruction q0 q3 r0 r3 s1 s3 c

/-! ## The terminal degree-two `U` chart -/

set_option maxRecDepth 10000 in
/-- `A/A/U` Boolean-ideal certificate. -/
theorem three013_AAU_identity
    (q0 q1 q3 r0 r1 r3 s3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun i j k l =>
        three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveU s3) c i j k l
      (r1 + r0*r1 + r1*c 5 + q0*r0*r1 + q0*r0*c 5 +
          q0*r1*r3 + q0*r1*s3 + q0*r1*c 4 + q0*r1*c 6 +
          q0*r3*c 5 + q0*s3*c 5 + q0*c 4*c 5 + q0*c 5*c 6 +
          r0*r1*c 5) * E 0 2 6 8 +
      (r0 + c 6 + q0*c 6 + r0*c 2 + r0*c 6 + q3*r0*c 6 +
          r0*r1*c 6) * E 2 4 5 7 +
      (1 + r0 + c 6 + q0*r0 + q0*c 4 + q0*c 6 + q3*r0 +
          r0*r1 + r0*r3 + r0*s3 + r1*c 5 + r1*c 6 + q0*r0*r1 +
          q0*r1*c 4 + q0*r1*c 6) * E 0 1 8 9 +
      (1 + r0 + r1 + c 6 + q0*r3 + q0*s3 + q3*r0 + r0*r3 +
          r0*s3 + r1*c 3 + r1*c 6 + q0*r0*r1 + q0*r1*c 4 +
          q0*r1*c 6) * E 3 4 5 6 +
      (1 + q0*r0 + q0*c 4 + q0*c 6 + q3*r0 + r0*r1) * E 1 2 8 9 +
      (q0 + c 2 + c 4 + q0*r1 + q0*c 4 + q0*q3*r1) * E 1 2 3 8 +
      (1 + r0) * E 0 1 4 7 + E 0 1 2 7 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, degreeTwoEffectiveU,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    seven_eq_one_f2_threePlace, nine_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, sixteen_eq_zero_f2_threePlace,
    eighteen_eq_zero_f2_threePlace, twenty_eq_zero_f2_threePlace,
    twenty_two_eq_zero_f2_threePlace, twenty_four_eq_zero_f2_threePlace,
    twenty_six_eq_zero_f2_threePlace, twenty_eight_eq_zero_f2_threePlace,
    thirty_eq_zero_f2_threePlace, thirty_two_eq_zero_f2_threePlace,
    thirty_four_eq_zero_f2_threePlace, thirty_eight_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `A/D/U` Boolean-ideal certificate. -/
theorem three013_ADU_identity
    (q0 q1 q3 r0 r3 s3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun i j k l =>
        three013Equation (rationalEffectiveA q0 q1 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveU s3) c i j k l
      (c 3 + r0*c 3) * E 0 1 6 7 +
      (r0 + c 3 + q0*r0 + r0*c 3) * E 0 1 8 9 +
      (r0 + c 2 + c 3 + q0*r0 + r0*c 2 + r0*c 3) * E 2 3 6 7 +
      (1 + r0) * E 1 2 6 8 +
      (1 + r0 + c 2 + c 3 + r0*c 2 + r0*c 3) * E 3 4 5 6 +
      E 0 1 2 3 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    degreeTwoEffectiveU, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    seven_eq_one_f2_threePlace, nine_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, sixteen_eq_zero_f2_threePlace,
    eighteen_eq_zero_f2_threePlace, twenty_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `D/A/U` Boolean-ideal certificate. -/
theorem three013_DAU_identity
    (q0 q3 r0 r1 r3 s3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun i j k l =>
        three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveU s3) c i j k l
      (1 + c 0 + c 5 + c 6 + q0*r3 + q0*s3 + r1*c 0 +
          r1*c 2 + r1*c 3 + r1*c 4 + c 2*c 4 + c 3*c 5 +
          c 3*c 6 + c 3*c 7) * E 0 3 5 9 +
      (c 5 + c 6 + c 5*c 8 + c 6*c 8) * E 1 4 5 9 +
      (r1 + c 2 + r1*c 4 + r1*c 6 + r1*c 7 + c 2*c 6 +
          c 3*c 6 + c 3*c 7 + c 4*c 6 + c 6*c 8) * E 3 4 7 9 +
      (r1*r3 + r1*s3 + r3*c 6 + s3*c 6) * E 0 1 2 7 +
      (r1 + c 4 + c 6 + c 7 + r0*r3 + r1*c 2 + c 3*c 6 +
          c 5*c 8) * E 2 4 5 7 +
      (r1 + c 2 + c 4 + c 6 + q0*r3 + q0*s3 + r0*r3 +
          r1*c 0 + r1*c 3 + r1*c 4 + r1*c 7 + c 0*c 5 +
          c 0*c 6 + c 0*c 7 + c 2*c 4 + c 3*c 6 + c 4*c 7 +
          c 5*c 8) * E 1 2 8 9 +
      (1 + r1 + c 0 + c 3 + c 6 + c 7 + r1*c 3 + r1*c 7 +
          c 0*c 4 + c 0*c 5 + c 3*c 6 + c 4*c 7 + c 5*c 8) *
        E 0 3 8 9 +
      (1 + c 0 + c 4 + c 6 + r1*c 0 + r1*c 5 + r1*c 7 +
          c 3*c 5 + c 5*c 8) * E 1 2 7 9 +
      (c 6 + c 7 + r1*c 3 + c 0*c 4 + c 0*c 6 + c 0*c 7) *
        E 1 4 7 8 +
      (c 5 + q0*r3 + q0*s3 + r1*c 2 + c 2*c 4) * E 0 4 5 8 +
      (1 + c 0 + c 3 + c 6 + r0*r3 + r1*c 0 + r1*c 5 +
          r1*c 6) * E 0 1 7 8 + E 2 3 6 7 + E 0 1 8 9 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveA, rationalEffectiveD,
    degreeTwoEffectiveU, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    seven_eq_one_f2_threePlace, nine_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, sixteen_eq_zero_f2_threePlace,
    eighteen_eq_zero_f2_threePlace, twenty_eq_zero_f2_threePlace,
    twenty_two_eq_zero_f2_threePlace, twenty_four_eq_zero_f2_threePlace,
    twenty_six_eq_zero_f2_threePlace, twenty_eight_eq_zero_f2_threePlace,
    thirty_eq_zero_f2_threePlace, thirty_two_eq_zero_f2_threePlace,
    thirty_four_eq_zero_f2_threePlace, thirty_eight_eq_zero_f2_threePlace]

set_option maxRecDepth 10000 in
/-- `D/D/U` Boolean-ideal certificate. -/
theorem three013_DDU_identity
    (q0 q3 r0 r3 s3 : F₂) (c : TargetCoeff) :
    (1 : F₂) =
      let E := fun i j k l =>
        three013Equation (rationalEffectiveD q0 q3)
          (rationalEffectiveD r0 r3) (degreeTwoEffectiveU s3) c i j k l
      q0*r0 * E 0 1 7 8 +
      (1 + q0 + q0*c 3 + c 3*c 4) * E 2 3 6 7 +
      (1 + q0 + c 3 + q0*c 3 + c 3*c 6) * E 0 1 8 9 +
      c 3 * E 0 3 8 9 +
      (c 2 + q0*c 2 + r0*c 2 + r3*c 3 + s3*c 3) * E 0 1 2 9 +
      (1 + r0) * E 0 1 2 6 := by
  simp [three013Equation, threePlacePluckerValue,
    threePlaceCandidateCoeff, explicitLocalLiftCoeff,
    explicitClosedPlaceCanonicalCoord, explicitClosedPlaceBasisCoeff,
    explicitTargetCoeff, rationalEffectiveD, degreeTwoEffectiveU,
    localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, pow_three_f2_threePlace,
    N3Certificate.three_eq_one_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2, N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2, five_eq_one_f2_threePlace,
    seven_eq_one_f2_threePlace, nine_eq_one_f2_threePlace,
    ten_eq_zero_f2_threePlace, twelve_eq_zero_f2_threePlace,
    fourteen_eq_zero_f2_threePlace, sixteen_eq_zero_f2_threePlace,
    eighteen_eq_zero_f2_threePlace, twenty_eq_zero_f2_threePlace]

theorem three013_AAU_obstruction
    (q0 q1 q3 r0 r1 r3 s3 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveU s3) c := by
  intro h
  have hid := three013_AAU_identity q0 q1 q3 r0 r1 r3 s3 c
  dsimp only at hid
  have h0268 := h 0 2 6 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2457 := h 2 4 5 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0189 := h 0 1 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h3456 := h 3 4 5 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1289 := h 1 2 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1238 := h 1 2 3 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0147 := h 0 1 4 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0127 := h 0 1 2 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h0268, h2457, h0189, h3456, h1289, h1238, h0147, h0127] at hid
  simp at hid

theorem three013_ADU_obstruction
    (q0 q1 q3 r0 r3 s3 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveA q0 q1 q3)
      (rationalEffectiveD r0 r3) (degreeTwoEffectiveU s3) c := by
  intro h
  have hid := three013_ADU_identity q0 q1 q3 r0 r3 s3 c
  dsimp only at hid
  have h0167 := h 0 1 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0189 := h 0 1 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2367 := h 2 3 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1268 := h 1 2 6 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h3456 := h 3 4 5 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0123 := h 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h0167, h0189, h2367, h1268, h3456, h0123] at hid
  simp at hid

theorem three013_DAU_obstruction
    (q0 q3 r0 r1 r3 s3 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveA r0 r1 r3) (degreeTwoEffectiveU s3) c := by
  intro h
  have hid := three013_DAU_identity q0 q3 r0 r1 r3 s3 c
  dsimp only at hid
  have h0359 := h 0 3 5 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1459 := h 1 4 5 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h3479 := h 3 4 7 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0127 := h 0 1 2 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2457 := h 2 4 5 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1289 := h 1 2 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0389 := h 0 3 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1279 := h 1 2 7 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1478 := h 1 4 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0458 := h 0 4 5 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0178 := h 0 1 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2367 := h 2 3 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0189 := h 0 1 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h0359, h1459, h3479, h0127, h2457, h1289, h0389, h1279,
    h1478, h0458, h0178, h2367, h0189] at hid
  simp at hid

theorem three013_DDU_obstruction
    (q0 q3 r0 r3 s3 : F₂) (c : TargetCoeff) :
    ¬ Three013PluckerZero (rationalEffectiveD q0 q3)
      (rationalEffectiveD r0 r3) (degreeTwoEffectiveU s3) c := by
  intro h
  have hid := three013_DDU_identity q0 q3 r0 r3 s3 c
  dsimp only at hid
  have h0178 := h 0 1 7 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2367 := h 2 3 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0189 := h 0 1 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0389 := h 0 3 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0129 := h 0 1 2 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h0126 := h 0 1 2 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [h0178, h2367, h0189, h0389, h0129, h0126] at hid
  simp at hid

/-- No candidate in the terminal `U` chart can satisfy all Pluecker
equations when both rational parameters are effective. -/
theorem three013_U_plucker_obstruction
    (q r : LocalKleinParam) (s3 : F₂)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (c : TargetCoeff) :
    ¬ Three013PluckerZero q r (degreeTwoEffectiveU s3) c := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, hq03, rfl⟩
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, hr03, rfl⟩
    · exact three013_AAU_obstruction q0 q1 q3 r0 r1 r3 s3 c
    · exact three013_ADU_obstruction q0 q1 q3 r0 r3 s3 c
  · rcases rationalLocalEffective_cases r hr with
      ⟨r0, r1, r3, rfl⟩ | ⟨r0, r3, hr03, rfl⟩
    · exact three013_DAU_obstruction q0 q3 r0 r1 r3 s3 c
    · exact three013_DDU_obstruction q0 q3 r0 r3 s3 c

/-- Algebraic three-place obstruction for the representative profile
`2P₀,2P₁,P_*`. -/
theorem three013_plucker_obstruction
    (q r s : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (hs : DegreeTwoLocalEffective s) (c : TargetCoeff) :
    ¬ Three013PluckerZero q r s c := by
  rcases degreeTwoLocalEffective_threeChart_cases s hs with
    ⟨s1, s2, rfl⟩ | ⟨s1, s3, rfl⟩ | ⟨s3, rfl⟩
  · exact three013_S_plucker_obstruction q r s1 s2 hq hr c
  · exact three013_T_plucker_obstruction q r s1 s3 hq hr c
  · exact three013_U_plucker_obstruction q r s3 hq hr c

/-- The sum of effective local lifts at `2P₀,2P₁,P_*`, plus any Hankel
target form, is never decomposable. -/
theorem three013_not_decomposable
    (q r s : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (hs : DegreeTwoLocalEffective s) (c : TargetCoeff) :
    ¬ IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 1 r +
        closedPlaceLift 3 s + targetTwo c) := by
  intro hdec
  exact three013_plucker_obstruction q r s hq hr hs c
    (three013PluckerZero_of_decomposable q r s c hdec)

/-- The decomposable fiber over the sum of effective quotient points at
`2P₀,2P₁,P_*` is empty. -/
theorem rational01_degreeTwo_mixed_decomposableFiber_empty
    (q r s : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (hs : DegreeTwoLocalEffective s) :
    decomposableFiber
      (closedPlaceQuotientPoint 0 q + closedPlaceQuotientPoint 1 r +
        closedPlaceQuotientPoint 3 s) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_threePlaceCandidate_of_mem_decomposableFiber
      0 q 1 r 3 s p hp with ⟨c, hc⟩
  apply three013_not_decomposable q r s hq hr hs c
  rw [← hc]
  exact hp.1

/-! ## Return to the abstract defect profile -/

/-- In a defect space of dimension at most three representing
`2P₀,2P₁,P_*`, every populated point is one of the three represented
witnesses.  The only fourth projective point would lie in the triple-sum
fiber excluded above. -/
theorem populatedPoint_cases_of_rational01_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h1 : IsRepresentedPlace Q 1)
    (h3 : IsRepresentedPlace Q 3)
    (y : PopulatedPoint Q) :
    y = representedPopulatedPoint Q 0 h0 ∨
      y = representedPopulatedPoint Q 1 h1 ∨
      y = representedPopulatedPoint Q 3 h3 := by
  let p0 := representedClosedPlaceParam Q 0 h0
  let p1 := representedClosedPlaceParam Q 1 h1
  let p3 := representedClosedPlaceParam Q 3 h3
  let q0 : LocalKleinParam := p0.2.1
  let q1 : LocalKleinParam := p1.2.1
  let q3 : LocalKleinParam := p3.2.1
  have hq0 : RationalLocalEffective q0 := by
    have hm := p0.2.2
    change q0 ∈ rationalEffectiveParams at hm
    simpa [rationalEffectiveParams] using hm
  have hq1 : RationalLocalEffective q1 := by
    have hm := p1.2.2
    change q1 ∈ rationalEffectiveParams at hm
    simpa [rationalEffectiveParams] using hm
  have hq3 : DegreeTwoLocalEffective q3 := by
    have hm := p3.2.2
    change q3 ∈ degreeTwoEffectiveParams at hm
    simpa [degreeTwoEffectiveParams] using hm
  have hcases := populatedPoint_cases_of_three_distinct_places
    Q hQ 0 1 3 h0 h1 h3 (by decide) (by decide) (by decide) y
  change y = representedPopulatedPoint Q 0 h0 ∨
      y = representedPopulatedPoint Q 1 h1 ∨
      y = representedPopulatedPoint Q 3 h3 ∨
      populatedQuotientPoint y =
        populatedQuotientPoint (representedPopulatedPoint Q 0 h0) +
          populatedQuotientPoint (representedPopulatedPoint Q 1 h1) +
          populatedQuotientPoint (representedPopulatedPoint Q 3 h3) at hcases
  rcases hcases with h | h | h | hy
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    have hfiber : populatedLift y ∈ decomposableFiber
        (closedPlaceQuotientPoint 0 q0 +
          closedPlaceQuotientPoint 1 q1 +
          closedPlaceQuotientPoint 3 q3) := by
      have hm := populatedLift_mem_fiber y
      rw [hy] at hm
      simpa [p0, p1, p3, q0, q1, q3, closedPlaceEffectivePoint] using hm
    have hempty := rational01_degreeTwo_mixed_decomposableFiber_empty
      q0 q1 q3 hq0 hq1 hq3
    rw [hempty] at hfiber
    exact hfiber.elim

/-- There are at most the three represented populated points in the
`2P₀,2P₁,P_*` profile. -/
theorem populatedPoint_card_le_three_of_rational01_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h1 : IsRepresentedPlace Q 1)
    (h3 : IsRepresentedPlace Q 3) :
    Fintype.card (PopulatedPoint Q) ≤ 3 := by
  classical
  let x0 := representedPopulatedPoint Q 0 h0
  let x1 := representedPopulatedPoint Q 1 h1
  let x3 := representedPopulatedPoint Q 3 h3
  have hsubset : (Finset.univ : Finset (PopulatedPoint Q)) ⊆
      {x0, x1, x3} := by
    intro y hy
    have hcases := populatedPoint_cases_of_rational01_degreeTwo_places
      Q hQ h0 h1 h3 y
    simpa [x0, x1, x3] using hcases
  calc
    Fintype.card (PopulatedPoint Q) =
        (Finset.univ : Finset (PopulatedPoint Q)).card :=
      Finset.card_univ.symm
    _ ≤ ({x0, x1, x3} : Finset (PopulatedPoint Q)).card :=
      Finset.card_le_card hsubset
    _ ≤ 3 := Finset.card_le_three

/-- The additive relation kernel vanishes in the representative
degree-two-plus-two-rational profile. -/
theorem populatedRelationKernel_finrank_eq_zero_of_rational01_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h1 : IsRepresentedPlace Q 1)
    (h3 : IsRepresentedPlace Q 3) :
    Module.finrank F₂
      ↥(relationKernel (populatedQuotientPoint (Q := Q))) = 0 := by
  let x : Fin 3 → PopulatedPoint Q :=
    ![representedPopulatedPoint Q 0 h0,
      representedPopulatedPoint Q 1 h1,
      representedPopulatedPoint Q 3 h3]
  have hlinQ : LinearIndependent F₂ (fun i : Fin 3 ↦ (x i).1) := by
    rw [show (fun i : Fin 3 ↦ (x i).1) =
        (![ (representedPopulatedPoint Q 0 h0).1,
            (representedPopulatedPoint Q 1 h1).1,
            (representedPopulatedPoint Q 3 h3).1 ] : Fin 3 → Q) by
      funext i
      fin_cases i <;> rfl]
    exact representedTriple_linearIndependent Q 0 1 3 h0 h1 h3
      (by decide) (by decide) (by decide)
  have hlin : LinearIndependent F₂
      (fun i : Fin 3 ↦ populatedQuotientPoint (x i)) :=
    hlinQ.map' Q.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hsmallSpan : Submodule.span F₂
      (Set.range (fun i : Fin 3 ↦ populatedQuotientPoint (x i))) ≤
      Submodule.span F₂
        (Set.range (populatedQuotientPoint (Q := Q))) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, rfl⟩
  have hspanRank : 3 ≤ Module.finrank F₂
      (Submodule.span F₂
        (Set.range (populatedQuotientPoint (Q := Q)))) := by
    have hrank := Submodule.finrank_mono hsmallSpan
    rw [finrank_span_eq_card hlin] at hrank
    simpa using hrank
  have hkernel := relationKernel_finrank_add_span
    (populatedQuotientPoint (Q := Q))
  have hcard :=
    populatedPoint_card_le_three_of_rational01_degreeTwo_places
      Q hQ h0 h1 h3
  omega

/-- The relation-gift term is zero for `2P₀,2P₁,P_*`. -/
theorem relationGiftRank_eq_zero_of_rational01_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h1 : IsRepresentedPlace Q 1)
    (h3 : IsRepresentedPlace Q 3) :
    relationGiftRank Q = 0 := by
  have hgift := relationGiftRank_le_relationKernel Q
  rw [populatedRelationKernel_finrank_eq_zero_of_rational01_degreeTwo_places
    Q hQ h0 h1 h3] at hgift
  omega

/-- The represented displacement weight is exactly four in this profile. -/
theorem representedPlaceWeight_eq_four_of_rational01_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h1 : IsRepresentedPlace Q 1)
    (h3 : IsRepresentedPlace Q 3) :
    representedPlaceWeight Q = 4 := by
  classical
  have h2 : ¬ IsRepresentedPlace Q 2 := by
    intro h2
    apply not_all_closedPlaces_represented Q hQ
    intro i
    fin_cases i <;> assumption
  simp [representedPlaceWeight, representedRationalPlaceCount,
    representedDegreeTwoIndicator, h0, h1, h2, h3]

/-- Sharp capacity row of manuscript Theorem 6.2 for the representative
degree-two place together with two rational places. -/
theorem targetCapacity_eq_seven_of_rational01_degreeTwo_places
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (h0 : IsRepresentedPlace Q 0)
    (h1 : IsRepresentedPlace Q 1)
    (h3 : IsRepresentedPlace Q 3) :
    targetCapacity Q = 7 := by
  rw [targetCapacity_eq_three_add_representedPlaceWeight_add_gifts,
    representedPlaceWeight_eq_four_of_rational01_degreeTwo_places
      Q hQ h0 h1 h3,
    relationGiftRank_eq_zero_of_rational01_degreeTwo_places
      Q hQ h0 h1 h3]

end

end N5
end UnrestrictedBooleanMul
