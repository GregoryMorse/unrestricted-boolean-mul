import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedBase
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedCorrectionOneNormalization

/-!
# Semantic closure of `OneOneAlignedCorrectionOne`

The affine normalizer is replayed here with explicit polynomial
certificates before the compact unit certificate is applied.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The original equations actually used to derive the affine ledger. -/
private def oneOneAlignedCorrectionOneSubstitutionSource
    (v : Fin 71 → F₂) : Fin 29 → F₂ :=
  ![
    -- return-high-0x023
    v 21 + v 31,
    -- return-high-0x025
    v 22 + v 32,
    -- return-high-0x029
    v 23 + v 33,
    -- return-high-0x031
    v 24 + v 34,
    -- return-high-0x061
    v 26 + v 36,
    -- return-high-0x0a1
    v 27 + v 37,
    -- return-high-0x121
    v 28 + v 38,
    -- return-high-0x221
    v 29 + v 39,
    -- product-high-0x063
    v 6 * v 11 + v 1 * v 16 + v 16 * v 42 + v 11 * v 47 + v 63 + v 68 + v 6 * v 21 * v 70 + v 16 * v 21 * v 70 + v 1 * v 26 * v 70 + v 11 * v 26 * v 70 + v 6 * v 31 * v 70 + v 26 * v 31 * v 70 + v 1 * v 36 * v 70 + v 21 * v 36 * v 70 + v 26 * v 42 * v 70 + v 36 * v 42 * v 70 + v 21 * v 47 * v 70 + v 31 * v 47 * v 70,
    -- product-high-0x065
    v 6 * v 12 + v 2 * v 16 + v 16 * v 43 + v 12 * v 47 + v 63 + v 66 + v 69 + v 6 * v 22 * v 70 + v 16 * v 22 * v 70 + v 2 * v 26 * v 70 + v 12 * v 26 * v 70 + v 6 * v 32 * v 70 + v 26 * v 32 * v 70 + v 2 * v 36 * v 70 + v 22 * v 36 * v 70 + v 26 * v 43 * v 70 + v 36 * v 43 * v 70 + v 22 * v 47 * v 70 + v 32 * v 47 * v 70,
    -- product-high-0x071
    v 6 * v 14 + v 4 * v 16 + v 16 * v 45 + v 14 * v 47 + v 63 + v 66 + v 68 + v 6 * v 24 * v 70 + v 16 * v 24 * v 70 + v 4 * v 26 * v 70 + v 14 * v 26 * v 70 + v 6 * v 34 * v 70 + v 26 * v 34 * v 70 + v 4 * v 36 * v 70 + v 24 * v 36 * v 70 + v 26 * v 45 * v 70 + v 36 * v 45 * v 70 + v 24 * v 47 * v 70 + v 34 * v 47 * v 70,
    -- product-high-0x0a3
    v 7 * v 11 + v 1 * v 17 + v 17 * v 42 + v 11 * v 48 + v 63 + v 66 + v 69 + v 7 * v 21 * v 70 + v 17 * v 21 * v 70 + v 1 * v 27 * v 70 + v 11 * v 27 * v 70 + v 7 * v 31 * v 70 + v 27 * v 31 * v 70 + v 1 * v 37 * v 70 + v 21 * v 37 * v 70 + v 27 * v 42 * v 70 + v 37 * v 42 * v 70 + v 21 * v 48 * v 70 + v 31 * v 48 * v 70,
    -- product-high-0x0a5
    v 7 * v 12 + v 2 * v 17 + v 17 * v 43 + v 12 * v 48 + v 63 + v 7 * v 22 * v 70 + v 17 * v 22 * v 70 + v 2 * v 27 * v 70 + v 12 * v 27 * v 70 + v 7 * v 32 * v 70 + v 27 * v 32 * v 70 + v 2 * v 37 * v 70 + v 22 * v 37 * v 70 + v 27 * v 43 * v 70 + v 37 * v 43 * v 70 + v 22 * v 48 * v 70 + v 32 * v 48 * v 70,
    -- product-high-0x0a9
    v 7 * v 13 + v 3 * v 17 + v 17 * v 44 + v 13 * v 48 + v 63 + v 66 + v 68 + v 7 * v 23 * v 70 + v 17 * v 23 * v 70 + v 3 * v 27 * v 70 + v 13 * v 27 * v 70 + v 7 * v 33 * v 70 + v 27 * v 33 * v 70 + v 3 * v 37 * v 70 + v 23 * v 37 * v 70 + v 27 * v 44 * v 70 + v 37 * v 44 * v 70 + v 23 * v 48 * v 70 + v 33 * v 48 * v 70,
    -- product-high-0x0b1
    v 7 * v 14 + v 4 * v 17 + v 17 * v 45 + v 14 * v 48 + v 63 + v 69 + v 7 * v 24 * v 70 + v 17 * v 24 * v 70 + v 4 * v 27 * v 70 + v 14 * v 27 * v 70 + v 7 * v 34 * v 70 + v 27 * v 34 * v 70 + v 4 * v 37 * v 70 + v 24 * v 37 * v 70 + v 27 * v 45 * v 70 + v 37 * v 45 * v 70 + v 24 * v 48 * v 70 + v 34 * v 48 * v 70,
    -- product-high-0x0e1
    v 7 * v 16 + v 6 * v 17 + v 17 * v 47 + v 16 * v 48 + v 7 * v 26 * v 70 + v 17 * v 26 * v 70 + v 6 * v 27 * v 70 + v 16 * v 27 * v 70 + v 7 * v 36 * v 70 + v 27 * v 36 * v 70 + v 6 * v 37 * v 70 + v 26 * v 37 * v 70 + v 27 * v 47 * v 70 + v 37 * v 47 * v 70 + v 26 * v 48 * v 70 + v 36 * v 48 * v 70,
    -- product-high-0x131
    v 8 * v 14 + v 4 * v 18 + v 18 * v 45 + v 14 * v 49 + v 63 + v 66 + v 67 + v 8 * v 24 * v 70 + v 18 * v 24 * v 70 + v 4 * v 28 * v 70 + v 14 * v 28 * v 70 + v 8 * v 34 * v 70 + v 28 * v 34 * v 70 + v 4 * v 38 * v 70 + v 24 * v 38 * v 70 + v 28 * v 45 * v 70 + v 38 * v 45 * v 70 + v 24 * v 49 * v 70 + v 34 * v 49 * v 70,
    -- product-high-0x231
    v 9 * v 14 + v 4 * v 19 + v 19 * v 45 + v 14 * v 50 + v 63 + v 64 + v 9 * v 24 * v 70 + v 19 * v 24 * v 70 + v 4 * v 29 * v 70 + v 14 * v 29 * v 70 + v 9 * v 34 * v 70 + v 29 * v 34 * v 70 + v 4 * v 39 * v 70 + v 24 * v 39 * v 70 + v 29 * v 45 * v 70 + v 39 * v 45 * v 70 + v 24 * v 50 * v 70 + v 34 * v 50 * v 70,
    -- fix-m1-0
    v 11,
    -- fix-m2-0
    v 12,
    -- fix-m4-0
    v 14,
    -- fix-m6-1
    1 + v 16,
    -- fix-m7-0
    v 17,
    -- fix-x1-1
    1 + v 21,
    -- fix-x2-0
    v 22,
    -- fix-x4-0
    v 24,
    -- fix-x6-0
    v 26,
    -- fix-x7-0
    v 27,
    -- fix-correctionReturn0-1
    1 + v 70
  ]


private def oneOneAlignedCorrectionOneSubstitutionCombination_y1 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 0 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 23

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_y1_certificate
    (v : Fin 71 → F₂) :
    v 31 + (1) =
      oneOneAlignedCorrectionOneSubstitutionCombination_y1 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y1, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_y1_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 31 = 1 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_y1_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y1, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_y2 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 1 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 24

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_y2_certificate
    (v : Fin 71 → F₂) :
    v 32 + (0) =
      oneOneAlignedCorrectionOneSubstitutionCombination_y2 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y2, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_y2_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 32 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_y2_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y2, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_y3 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 2

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_y3_certificate
    (v : Fin 71 → F₂) :
    v 33 + (v 23) =
      oneOneAlignedCorrectionOneSubstitutionCombination_y3 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y3, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_y3_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 33 = v 23 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_y3_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y3, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_y4 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 3 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 25

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_y4_certificate
    (v : Fin 71 → F₂) :
    v 34 + (0) =
      oneOneAlignedCorrectionOneSubstitutionCombination_y4 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y4, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_y4_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 34 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_y4_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y4, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_y6 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 26

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_y6_certificate
    (v : Fin 71 → F₂) :
    v 36 + (0) =
      oneOneAlignedCorrectionOneSubstitutionCombination_y6 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y6, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_y6_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 36 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_y6_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y6, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_y7 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 27

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_y7_certificate
    (v : Fin 71 → F₂) :
    v 37 + (0) =
      oneOneAlignedCorrectionOneSubstitutionCombination_y7 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y7, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_y7_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 37 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_y7_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y7, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_y8 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 6

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_y8_certificate
    (v : Fin 71 → F₂) :
    v 38 + (v 28) =
      oneOneAlignedCorrectionOneSubstitutionCombination_y8 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y8, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_y8_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 38 = v 28 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_y8_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y8, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_y9 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 7

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_y9_certificate
    (v : Fin 71 → F₂) :
    v 39 + (v 29) =
      oneOneAlignedCorrectionOneSubstitutionCombination_y9 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y9, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_y9_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 39 = v 29 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_y9_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_y9, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget6 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 8 +
  (v 6 * v 21 + v 16 * v 21 + v 7 * v 22 + v 17 * v 22 + v 1 * v 26 + v 11 * v 26 + v 2 * v 27 + v 12 * v 27 + v 6 * v 31 + v 26 * v 31 + v 7 * v 32 + v 27 * v 32 + v 1 * v 36 + v 21 * v 36 + v 2 * v 37 + v 22 * v 37 + v 26 * v 42 + v 36 * v 42 + v 27 * v 43 + v 37 * v 43 + v 21 * v 47 + v 31 * v 47 + v 22 * v 48 + v 32 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 1 + v 21 + v 42) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (1 + v 11 + v 21) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 26 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 0 +
  (v 16 + v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 23 +
  (1 + v 1 + v 42) * oneOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 6 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 2 + v 22 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 12 + v 22) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 2 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 19

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget6_certificate
    (v : Fin 71 → F₂) :
    v 68 + (1 + v 1 + v 42) =
      oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget6 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget6, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget6_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 68 = 1 + v 1 + v 42 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_correctionTarget6_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget6, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget7 (v : Fin 71 → F₂) : F₂ :=
  (v 6 * v 21 + v 7 * v 21 + v 16 * v 21 + v 17 * v 21 + v 7 * v 22 + v 17 * v 22 + v 6 * v 24 + v 16 * v 24 + v 1 * v 26 + v 4 * v 26 + v 11 * v 26 + v 14 * v 26 + v 1 * v 27 + v 2 * v 27 + v 11 * v 27 + v 12 * v 27 + v 6 * v 31 + v 7 * v 31 + v 26 * v 31 + v 27 * v 31 + v 7 * v 32 + v 27 * v 32 + v 6 * v 34 + v 26 * v 34 + v 1 * v 36 + v 4 * v 36 + v 21 * v 36 + v 24 * v 36 + v 1 * v 37 + v 2 * v 37 + v 21 * v 37 + v 22 * v 37 + v 26 * v 42 + v 27 * v 42 + v 36 * v 42 + v 37 * v 42 + v 27 * v 43 + v 37 * v 43 + v 26 * v 45 + v 36 * v 45 + v 21 * v 47 + v 24 * v 47 + v 31 * v 47 + v 34 * v 47 + v 21 * v 48 + v 22 * v 48 + v 31 * v 48 + v 32 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 11 +
  (v 1 + v 2 + v 21 + v 22 + v 42 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (1 + v 11 + v 12 + v 21 + v 22) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 6 + v 7 + v 26 + v 27 + v 47 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 0 +
  (v 16 + v 17 + v 26 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 23 +
  (1 + v 1 + v 2 + v 42 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 6 + v 7 + v 47 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 19 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 10 +
  (v 1 + v 4 + v 21 + v 24 + v 42 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (1 + v 11 + v 14 + v 21 + v 24) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 26 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 16 + v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 25 +
  (1 + v 1 + v 4 + v 42 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 6 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 20 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 8

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget7_certificate
    (v : Fin 71 → F₂) :
    v 69 + (1 + v 1 + v 4 + v 42 + v 45) =
      oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget7 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget7, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget7_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 69 = 1 + v 1 + v 4 + v 42 + v 45 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_correctionTarget7_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget7, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget4 (v : Fin 71 → F₂) : F₂ :=
  (v 6 * v 22 + v 16 * v 22 + v 7 * v 24 + v 17 * v 24 + v 2 * v 26 + v 12 * v 26 + v 4 * v 27 + v 14 * v 27 + v 6 * v 32 + v 26 * v 32 + v 7 * v 34 + v 27 * v 34 + v 2 * v 36 + v 22 * v 36 + v 4 * v 37 + v 24 * v 37 + v 26 * v 43 + v 36 * v 43 + v 27 * v 45 + v 37 * v 45 + v 22 * v 47 + v 32 * v 47 + v 24 * v 48 + v 34 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 2 + v 22 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 12 + v 22) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 25 +
  (v 2 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 20 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 14 +
  (v 4 + v 24 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 14 + v 24) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 4 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 9 +
  (v 6 + v 26 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 16 + v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 6 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 19

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget4_certificate
    (v : Fin 71 → F₂) :
    v 66 + (v 2 + v 43) =
      oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget4 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget4, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget4_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 66 = v 2 + v 43 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_correctionTarget4_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget4, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear2 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 11 +
  (v 7 * v 21 + v 17 * v 21 + v 6 * v 22 + v 16 * v 22 + v 2 * v 26 + v 12 * v 26 + v 1 * v 27 + v 11 * v 27 + v 7 * v 31 + v 27 * v 31 + v 6 * v 32 + v 26 * v 32 + v 2 * v 36 + v 22 * v 36 + v 1 * v 37 + v 21 * v 37 + v 27 * v 42 + v 37 * v 42 + v 26 * v 43 + v 36 * v 43 + v 22 * v 47 + v 32 * v 47 + v 21 * v 48 + v 31 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 1 + v 21 + v 42) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (1 + v 11 + v 21) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 0 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 23 +
  (1 + v 1 + v 42) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 9 +
  (v 2 + v 22 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 12 + v 22) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 26 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 16 + v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 2 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 6 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 19

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_factorLinear2_certificate
    (v : Fin 71 → F₂) :
    v 43 + (v 2) =
      oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear2 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear2, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_factorLinear2_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 43 = v 2 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_factorLinear2_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear2, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget1 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 7 * v 22 + v 17 * v 22 + v 2 * v 27 + v 12 * v 27 + v 7 * v 32 + v 27 * v 32 + v 2 * v 37 + v 22 * v 37 + v 27 * v 43 + v 37 * v 43 + v 22 * v 48 + v 32 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 2 + v 22 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 12 + v 22) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 2 + v 43) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 19

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget1_certificate
    (v : Fin 71 → F₂) :
    v 63 + (0) =
      oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget1 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget1, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget1_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 63 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_correctionTarget1_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget1, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear4 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 14 +
  (v 6 * v 21 + v 7 * v 21 + v 16 * v 21 + v 17 * v 21 + v 6 * v 24 + v 7 * v 24 + v 16 * v 24 + v 17 * v 24 + v 1 * v 26 + v 4 * v 26 + v 11 * v 26 + v 14 * v 26 + v 1 * v 27 + v 4 * v 27 + v 11 * v 27 + v 14 * v 27 + v 6 * v 31 + v 7 * v 31 + v 26 * v 31 + v 27 * v 31 + v 6 * v 34 + v 7 * v 34 + v 26 * v 34 + v 27 * v 34 + v 1 * v 36 + v 4 * v 36 + v 21 * v 36 + v 24 * v 36 + v 1 * v 37 + v 4 * v 37 + v 21 * v 37 + v 24 * v 37 + v 26 * v 42 + v 27 * v 42 + v 36 * v 42 + v 37 * v 42 + v 26 * v 45 + v 27 * v 45 + v 36 * v 45 + v 37 * v 45 + v 21 * v 47 + v 24 * v 47 + v 31 * v 47 + v 34 * v 47 + v 21 * v 48 + v 24 * v 48 + v 31 * v 48 + v 34 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 1 + v 4 + v 21 + v 24 + v 42 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (1 + v 11 + v 14 + v 21 + v 24) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 6 + v 7 + v 26 + v 27 + v 47 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 16 + v 17 + v 26 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 25 +
  (1 + v 1 + v 4 + v 42 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 6 + v 7 + v 47 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 20 +
  (v 1 + v 4 + v 21 + v 24 + v 42 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (1 + v 11 + v 14 + v 21 + v 24) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (1 + v 1 + v 4 + v 42 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 21 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 10 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 8 +
  (v 6 + v 7 + v 26 + v 27 + v 47 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 0 +
  (v 16 + v 17 + v 26 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 23 +
  (v 6 + v 7 + v 47 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 11

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_factorLinear4_certificate
    (v : Fin 71 → F₂) :
    v 45 + (1 + v 1 + v 4 + v 42) =
      oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear4 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear4, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_factorLinear4_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 45 = 1 + v 1 + v 4 + v 42 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_factorLinear4_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear4, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear7 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 15 +
  (v 7 * v 26 + v 17 * v 26 + v 6 * v 27 + v 16 * v 27 + v 7 * v 36 + v 27 * v 36 + v 6 * v 37 + v 26 * v 37 + v 27 * v 47 + v 37 * v 47 + v 26 * v 48 + v 36 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 6 + v 26 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 16 + v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 21

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_factorLinear7_certificate
    (v : Fin 71 → F₂) :
    v 48 + (v 7) =
      oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear7 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear7, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_factorLinear7_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 48 = v 7 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_factorLinear7_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear7, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear1 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 13 +
  (v 6 * v 21 + v 7 * v 21 + v 16 * v 21 + v 17 * v 21 + v 7 * v 23 + v 17 * v 23 + v 7 * v 24 + v 17 * v 24 + v 1 * v 26 + v 11 * v 26 + v 7 * v 13 * v 26 + v 13 * v 17 * v 26 + v 1 * v 27 + v 3 * v 27 + v 4 * v 27 + v 11 * v 27 + v 13 * v 27 + v 6 * v 13 * v 27 + v 14 * v 27 + v 13 * v 16 * v 27 + v 6 * v 31 + v 7 * v 31 + v 26 * v 31 + v 27 * v 31 + v 7 * v 33 + v 27 * v 33 + v 7 * v 34 + v 27 * v 34 + v 1 * v 36 + v 7 * v 13 * v 36 + v 21 * v 36 + v 13 * v 27 * v 36 + v 1 * v 37 + v 3 * v 37 + v 4 * v 37 + v 6 * v 13 * v 37 + v 21 * v 37 + v 23 * v 37 + v 24 * v 37 + v 13 * v 26 * v 37 + v 26 * v 42 + v 27 * v 42 + v 36 * v 42 + v 37 * v 42 + v 27 * v 44 + v 37 * v 44 + v 27 * v 45 + v 37 * v 45 + v 21 * v 47 + v 13 * v 27 * v 47 + v 31 * v 47 + v 13 * v 37 * v 47 + v 21 * v 48 + v 23 * v 48 + v 24 * v 48 + v 13 * v 26 * v 48 + v 31 * v 48 + v 33 * v 48 + v 34 * v 48 + v 13 * v 36 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 1 + v 3 + v 4 + v 6 * v 13 + v 21 + v 23 + v 24 + v 13 * v 26 + v 42 + v 44 + v 45 + v 13 * v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (1 + v 11 + v 13 + v 14 + v 13 * v 16 + v 21 + v 24 + v 13 * v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 2 +
  (1 + v 1 + v 3 + v 4 + v 6 * v 13 + v 23 + v 42 + v 44 + v 45 + v 13 * v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 8 +
  (v 1 + v 7 * v 13 + v 21 + v 13 * v 27 + v 42 + v 13 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (1 + v 11 + v 13 * v 17 + v 21 + v 13 * v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 7 + v 26 + v 27 + v 47 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 0 +
  (v 16 + v 17 + v 26 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 23 +
  (1 + v 1 + v 7 * v 13 + v 42 + v 13 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 6 + v 7 + v 47 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 18 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 25 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 20 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 14 +
  (v 13) * oneOneAlignedCorrectionOneSubstitutionSource v 15 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 11

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_factorLinear1_certificate
    (v : Fin 71 → F₂) :
    v 42 + (1 + v 1) =
      oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear1 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear1, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_factorLinear1_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 42 = 1 + v 1 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_factorLinear1_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_factorLinear1, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget5 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 16 +
  (v 7 * v 21 + v 17 * v 21 + v 7 * v 22 + v 17 * v 22 + v 7 * v 18 * v 23 + v 17 * v 18 * v 23 + v 7 * v 24 + v 8 * v 24 + v 17 * v 24 + v 18 * v 24 + v 6 * v 18 * v 24 + v 16 * v 18 * v 24 + v 4 * v 18 * v 26 + v 7 * v 13 * v 18 * v 26 + v 14 * v 18 * v 26 + v 13 * v 17 * v 18 * v 26 + v 1 * v 27 + v 2 * v 27 + v 4 * v 27 + v 11 * v 27 + v 12 * v 27 + v 14 * v 27 + v 3 * v 18 * v 27 + v 13 * v 18 * v 27 + v 6 * v 13 * v 18 * v 27 + v 13 * v 16 * v 18 * v 27 + v 4 * v 28 + v 14 * v 28 + v 7 * v 31 + v 27 * v 31 + v 7 * v 32 + v 27 * v 32 + v 7 * v 18 * v 33 + v 18 * v 27 * v 33 + v 7 * v 34 + v 8 * v 34 + v 6 * v 18 * v 34 + v 18 * v 26 * v 34 + v 27 * v 34 + v 28 * v 34 + v 4 * v 18 * v 36 + v 7 * v 13 * v 18 * v 36 + v 18 * v 24 * v 36 + v 13 * v 18 * v 27 * v 36 + v 1 * v 37 + v 2 * v 37 + v 4 * v 37 + v 3 * v 18 * v 37 + v 6 * v 13 * v 18 * v 37 + v 21 * v 37 + v 22 * v 37 + v 18 * v 23 * v 37 + v 24 * v 37 + v 13 * v 18 * v 26 * v 37 + v 4 * v 38 + v 24 * v 38 + v 27 * v 42 + v 37 * v 42 + v 27 * v 43 + v 37 * v 43 + v 18 * v 27 * v 44 + v 18 * v 37 * v 44 + v 18 * v 26 * v 45 + v 27 * v 45 + v 28 * v 45 + v 18 * v 36 * v 45 + v 37 * v 45 + v 38 * v 45 + v 18 * v 24 * v 47 + v 13 * v 18 * v 27 * v 47 + v 18 * v 34 * v 47 + v 13 * v 18 * v 37 * v 47 + v 21 * v 48 + v 22 * v 48 + v 18 * v 23 * v 48 + v 24 * v 48 + v 13 * v 18 * v 26 * v 48 + v 31 * v 48 + v 32 * v 48 + v 18 * v 33 * v 48 + v 34 * v 48 + v 13 * v 18 * v 36 * v 48 + v 24 * v 49 + v 34 * v 49) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 4 + v 24 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 6 +
  (v 7 + v 8 + v 6 * v 18 + v 18 * v 26 + v 27 + v 28 + v 18 * v 47 + v 48 + v 49) * oneOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 17 + v 18 + v 16 * v 18 + v 18 * v 26 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 25 +
  (v 7 + v 8 + v 6 * v 18 + v 28 + v 18 * v 47 + v 48 + v 49) * oneOneAlignedCorrectionOneSubstitutionSource v 20 +
  (v 4 * v 18 + v 7 * v 13 * v 18 + v 18 * v 24 + v 13 * v 18 * v 27 + v 18 * v 45 + v 13 * v 18 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 14 * v 18 + v 13 * v 17 * v 18 + v 18 * v 24 + v 13 * v 18 * v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 4 * v 18 + v 7 * v 13 * v 18 + v 18 * v 45 + v 13 * v 18 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 21 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 14 +
  (v 1 + v 2 + v 4 + v 3 * v 18 + v 6 * v 13 * v 18 + v 21 + v 22 + v 18 * v 23 + v 24 + v 13 * v 18 * v 26 + v 42 + v 43 + v 18 * v 44 + v 45 + v 13 * v 18 * v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (1 + v 11 + v 12 + v 14 + v 13 * v 18 + v 13 * v 16 * v 18 + v 21 + v 22 + v 24 + v 13 * v 18 * v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (1 + v 1 + v 2 + v 4 + v 3 * v 18 + v 6 * v 13 * v 18 + v 18 * v 23 + v 42 + v 43 + v 18 * v 44 + v 45 + v 13 * v 18 * v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 19 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 18) * oneOneAlignedCorrectionOneSubstitutionSource v 10 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 0 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 23 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 11 +
  (v 18) * oneOneAlignedCorrectionOneSubstitutionSource v 13 +
  (v 7 * v 18 + v 18 * v 27 + v 18 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 2 +
  (v 13 * v 18) * oneOneAlignedCorrectionOneSubstitutionSource v 15

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget5_certificate
    (v : Fin 71 → F₂) :
    v 67 + (0) =
      oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget5 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget5, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget5_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 67 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_correctionTarget5_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget5, hzero]


private def oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget2 (v : Fin 71 → F₂) : F₂ :=
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 17 +
  (v 7 * v 22 + v 17 * v 22 + v 7 * v 19 * v 23 + v 17 * v 19 * v 23 + v 9 * v 24 + v 19 * v 24 + v 6 * v 19 * v 24 + v 16 * v 19 * v 24 + v 4 * v 19 * v 26 + v 7 * v 13 * v 19 * v 26 + v 14 * v 19 * v 26 + v 13 * v 17 * v 19 * v 26 + v 2 * v 27 + v 12 * v 27 + v 3 * v 19 * v 27 + v 13 * v 19 * v 27 + v 6 * v 13 * v 19 * v 27 + v 13 * v 16 * v 19 * v 27 + v 4 * v 29 + v 14 * v 29 + v 7 * v 32 + v 27 * v 32 + v 7 * v 19 * v 33 + v 19 * v 27 * v 33 + v 9 * v 34 + v 6 * v 19 * v 34 + v 19 * v 26 * v 34 + v 29 * v 34 + v 4 * v 19 * v 36 + v 7 * v 13 * v 19 * v 36 + v 19 * v 24 * v 36 + v 13 * v 19 * v 27 * v 36 + v 2 * v 37 + v 3 * v 19 * v 37 + v 6 * v 13 * v 19 * v 37 + v 22 * v 37 + v 19 * v 23 * v 37 + v 13 * v 19 * v 26 * v 37 + v 4 * v 39 + v 24 * v 39 + v 27 * v 43 + v 37 * v 43 + v 19 * v 27 * v 44 + v 19 * v 37 * v 44 + v 19 * v 26 * v 45 + v 29 * v 45 + v 19 * v 36 * v 45 + v 39 * v 45 + v 19 * v 24 * v 47 + v 13 * v 19 * v 27 * v 47 + v 19 * v 34 * v 47 + v 13 * v 19 * v 37 * v 47 + v 22 * v 48 + v 19 * v 23 * v 48 + v 13 * v 19 * v 26 * v 48 + v 32 * v 48 + v 19 * v 33 * v 48 + v 13 * v 19 * v 36 * v 48 + v 24 * v 50 + v 34 * v 50) * oneOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 4 + v 24 + v 45) * oneOneAlignedCorrectionOneSubstitutionSource v 7 +
  (v 9 + v 6 * v 19 + v 19 * v 26 + v 29 + v 19 * v 47 + v 50) * oneOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 19 + v 16 * v 19 + v 19 * v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 25 +
  (v 9 + v 6 * v 19 + v 29 + v 19 * v 47 + v 50) * oneOneAlignedCorrectionOneSubstitutionSource v 20 +
  (1) * oneOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 2 + v 3 * v 19 + v 6 * v 13 * v 19 + v 22 + v 19 * v 23 + v 13 * v 19 * v 26 + v 43 + v 19 * v 44 + v 13 * v 19 * v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 12 + v 13 * v 19 + v 13 * v 16 * v 19 + v 22 + v 13 * v 19 * v 26) * oneOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 17 + v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 2 + v 3 * v 19 + v 6 * v 13 * v 19 + v 19 * v 23 + v 43 + v 19 * v 44 + v 13 * v 19 * v 47) * oneOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 7 + v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 19 +
  (v 4 * v 19 + v 7 * v 13 * v 19 + v 19 * v 24 + v 13 * v 19 * v 27 + v 19 * v 45 + v 13 * v 19 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 14 * v 19 + v 13 * v 17 * v 19 + v 19 * v 24 + v 13 * v 19 * v 27) * oneOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 4 * v 19 + v 7 * v 13 * v 19 + v 19 * v 45 + v 13 * v 19 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 19) * oneOneAlignedCorrectionOneSubstitutionSource v 10 +
  (v 19) * oneOneAlignedCorrectionOneSubstitutionSource v 13 +
  (v 7 * v 19 + v 19 * v 27 + v 19 * v 48) * oneOneAlignedCorrectionOneSubstitutionSource v 2 +
  (v 13 * v 19) * oneOneAlignedCorrectionOneSubstitutionSource v 15

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget2_certificate
    (v : Fin 71 → F₂) :
    v 64 + (0) =
      oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget2 v := by
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget2, oneOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem oneOneAlignedCorrectionOne_substitution_correctionTarget2_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, oneOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 64 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [oneOneAlignedCorrectionOne_substitution_correctionTarget2_certificate]
  simp [oneOneAlignedCorrectionOneSubstitutionCombination_correctionTarget2, hzero]

/-- The semantic high equations and normalized fixed values discharge
every source equation used by affine elimination. -/
private theorem oneOneAlignedCorrectionOne_substitution_source_eq_zero
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : OneOneAlignedNormalForm p)
    (hcorrection : p.correctionReturn = (1 : F₂))
    (hbase : ∀ i : Fin 31, oneOneAlignedBaseConstraint p.vector i = 0) :
    ∀ i : Fin 29, oneOneAlignedCorrectionOneSubstitutionSource p.vector i = 0 := by
  intro i
  fin_cases i
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (0 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (0 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (1 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (1 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (2 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (2 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (3 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (3 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (4 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (4 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (5 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (5 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (6 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (6 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (7 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (7 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (8 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (13 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (9 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (14 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (10 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (15 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (11 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (18 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (12 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (19 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (13 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (20 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (14 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (21 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (15 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (22 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (16 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (23 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (17 : Fin 29) = 0
    simpa [oneOneAlignedCorrectionOneSubstitutionSource, oneOneAlignedBaseConstraint] using
      hbase (24 : Fin 31)
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (18 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.m1]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (19 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.m2]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (20 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.m4]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (21 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.m6]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (22 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.m7]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (23 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.x1]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (24 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.x2]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (25 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.x4]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (26 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.x6]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (27 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.x7]
  · change oneOneAlignedCorrectionOneSubstitutionSource p.vector (28 : Fin 29) = 0
    simp [oneOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hcorrection]

/-- All 29 substitutions used by the compact certificate follow from
the literal history equations and the aligned normal form. -/
private theorem oneOneAlignedCorrectionOne_substitutions_of_source_zero
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : OneOneAlignedNormalForm p)
    (hcorrection : p.correctionReturn = (1 : F₂))
    (hsource : ∀ i : Fin 29,
      oneOneAlignedCorrectionOneSubstitutionSource p.vector i = 0) :
    OneOneAlignedCorrectionOneSubstitutions p.vector := by
  refine {
    y1 := oneOneAlignedCorrectionOne_substitution_y1_of_source_zero p.vector hsource
    y2 := oneOneAlignedCorrectionOne_substitution_y2_of_source_zero p.vector hsource
    y3 := oneOneAlignedCorrectionOne_substitution_y3_of_source_zero p.vector hsource
    y4 := oneOneAlignedCorrectionOne_substitution_y4_of_source_zero p.vector hsource
    y6 := oneOneAlignedCorrectionOne_substitution_y6_of_source_zero p.vector hsource
    y7 := oneOneAlignedCorrectionOne_substitution_y7_of_source_zero p.vector hsource
    y8 := oneOneAlignedCorrectionOne_substitution_y8_of_source_zero p.vector hsource
    y9 := oneOneAlignedCorrectionOne_substitution_y9_of_source_zero p.vector hsource
    m1 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.m1
    m2 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.m2
    m4 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.m4
    m6 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.m6
    m7 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.m7
    x1 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.x1
    x2 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.x2
    x4 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.x4
    x6 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.x6
    x7 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.x7
    correctionReturn0 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hcorrection
    correctionTarget6 := oneOneAlignedCorrectionOne_substitution_correctionTarget6_of_source_zero p.vector hsource
    correctionTarget7 := oneOneAlignedCorrectionOne_substitution_correctionTarget7_of_source_zero p.vector hsource
    correctionTarget4 := oneOneAlignedCorrectionOne_substitution_correctionTarget4_of_source_zero p.vector hsource
    factorLinear2 := oneOneAlignedCorrectionOne_substitution_factorLinear2_of_source_zero p.vector hsource
    correctionTarget1 := oneOneAlignedCorrectionOne_substitution_correctionTarget1_of_source_zero p.vector hsource
    factorLinear4 := oneOneAlignedCorrectionOne_substitution_factorLinear4_of_source_zero p.vector hsource
    factorLinear7 := oneOneAlignedCorrectionOne_substitution_factorLinear7_of_source_zero p.vector hsource
    factorLinear1 := oneOneAlignedCorrectionOne_substitution_factorLinear1_of_source_zero p.vector hsource
    correctionTarget5 := oneOneAlignedCorrectionOne_substitution_correctionTarget5_of_source_zero p.vector hsource
    correctionTarget2 := oneOneAlignedCorrectionOne_substitution_correctionTarget2_of_source_zero p.vector hsource
  }

/-- The exceptional aligned leaf is inconsistent with the literal
quadratic return-history hypotheses. -/
theorem oneOneAlignedCorrectionOne_inconsistent_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : OneOneAlignedNormalForm p)
    (hcorrection : p.correctionReturn = (1 : F₂))
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference .zero p ∈
      N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .zero p))) :
    False := by
  have hbase := oneOneAligned_base_equations_of_quadratic_history p
    hreturned hfeedback hprojection
  have hsource := oneOneAlignedCorrectionOne_substitution_source_eq_zero p hnormal
    hcorrection hbase
  have hsub := oneOneAlignedCorrectionOne_substitutions_of_source_zero p hnormal
    hcorrection hsource
  apply oneOneAlignedCorrectionOne_inconsistent_of_original p.vector hsub
  intro i
  simpa [oneOneAlignedCorrectionOneOriginalConstraint] using
    hbase ((![8, 9, 10, 11, 12, 16, 17, 25, 26, 27, 28, 29, 30] : Fin 13 → Fin 31) i)

end
end N5
end UnrestrictedBooleanMul
