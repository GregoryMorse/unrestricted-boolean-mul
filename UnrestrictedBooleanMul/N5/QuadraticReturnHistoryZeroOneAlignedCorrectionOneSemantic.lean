import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedBase
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedCorrectionOneNormalization

/-!
# Semantic closure of `ZeroOneAlignedCorrectionOne`

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
private def zeroOneAlignedCorrectionOneSubstitutionSource
    (v : Fin 71 → F₂) : Fin 29 → F₂ :=
  ![
    -- return-high-0x023
    v 21,
    -- return-high-0x025
    v 22,
    -- return-high-0x029
    v 23,
    -- return-high-0x031
    v 24,
    -- return-high-0x061
    v 26,
    -- return-high-0x0a1
    v 27,
    -- return-high-0x121
    v 28,
    -- return-high-0x221
    v 29,
    -- product-high-0x063
    v 6 * v 11 + v 1 * v 16 + v 6 * v 42 + v 1 * v 47 + v 63 + v 68 + v 16 * v 21 * v 70 + v 11 * v 26 * v 70 + v 6 * v 31 * v 70 + v 26 * v 31 * v 70 + v 1 * v 36 * v 70 + v 21 * v 36 * v 70 + v 26 * v 42 * v 70 + v 21 * v 47 * v 70,
    -- product-high-0x065
    v 6 * v 12 + v 2 * v 16 + v 6 * v 43 + v 2 * v 47 + v 63 + v 66 + v 69 + v 16 * v 22 * v 70 + v 12 * v 26 * v 70 + v 6 * v 32 * v 70 + v 26 * v 32 * v 70 + v 2 * v 36 * v 70 + v 22 * v 36 * v 70 + v 26 * v 43 * v 70 + v 22 * v 47 * v 70,
    -- product-high-0x071
    v 6 * v 14 + v 4 * v 16 + v 6 * v 45 + v 4 * v 47 + v 63 + v 66 + v 68 + v 16 * v 24 * v 70 + v 14 * v 26 * v 70 + v 6 * v 34 * v 70 + v 26 * v 34 * v 70 + v 4 * v 36 * v 70 + v 24 * v 36 * v 70 + v 26 * v 45 * v 70 + v 24 * v 47 * v 70,
    -- product-high-0x0a3
    v 7 * v 11 + v 1 * v 17 + v 7 * v 42 + v 1 * v 48 + v 63 + v 66 + v 69 + v 17 * v 21 * v 70 + v 11 * v 27 * v 70 + v 7 * v 31 * v 70 + v 27 * v 31 * v 70 + v 1 * v 37 * v 70 + v 21 * v 37 * v 70 + v 27 * v 42 * v 70 + v 21 * v 48 * v 70,
    -- product-high-0x0a5
    v 7 * v 12 + v 2 * v 17 + v 7 * v 43 + v 2 * v 48 + v 63 + v 17 * v 22 * v 70 + v 12 * v 27 * v 70 + v 7 * v 32 * v 70 + v 27 * v 32 * v 70 + v 2 * v 37 * v 70 + v 22 * v 37 * v 70 + v 27 * v 43 * v 70 + v 22 * v 48 * v 70,
    -- product-high-0x0a9
    v 7 * v 13 + v 3 * v 17 + v 7 * v 44 + v 3 * v 48 + v 63 + v 66 + v 68 + v 17 * v 23 * v 70 + v 13 * v 27 * v 70 + v 7 * v 33 * v 70 + v 27 * v 33 * v 70 + v 3 * v 37 * v 70 + v 23 * v 37 * v 70 + v 27 * v 44 * v 70 + v 23 * v 48 * v 70,
    -- product-high-0x0b1
    v 7 * v 14 + v 4 * v 17 + v 7 * v 45 + v 4 * v 48 + v 63 + v 69 + v 17 * v 24 * v 70 + v 14 * v 27 * v 70 + v 7 * v 34 * v 70 + v 27 * v 34 * v 70 + v 4 * v 37 * v 70 + v 24 * v 37 * v 70 + v 27 * v 45 * v 70 + v 24 * v 48 * v 70,
    -- product-high-0x0e1
    v 7 * v 16 + v 6 * v 17 + v 7 * v 47 + v 6 * v 48 + v 17 * v 26 * v 70 + v 16 * v 27 * v 70 + v 7 * v 36 * v 70 + v 27 * v 36 * v 70 + v 6 * v 37 * v 70 + v 26 * v 37 * v 70 + v 27 * v 47 * v 70 + v 26 * v 48 * v 70,
    -- product-high-0x131
    v 8 * v 14 + v 4 * v 18 + v 8 * v 45 + v 4 * v 49 + v 63 + v 66 + v 67 + v 18 * v 24 * v 70 + v 14 * v 28 * v 70 + v 8 * v 34 * v 70 + v 28 * v 34 * v 70 + v 4 * v 38 * v 70 + v 24 * v 38 * v 70 + v 28 * v 45 * v 70 + v 24 * v 49 * v 70,
    -- product-high-0x231
    v 9 * v 14 + v 4 * v 19 + v 9 * v 45 + v 4 * v 50 + v 63 + v 64 + v 19 * v 24 * v 70 + v 14 * v 29 * v 70 + v 9 * v 34 * v 70 + v 29 * v 34 * v 70 + v 4 * v 39 * v 70 + v 24 * v 39 * v 70 + v 29 * v 45 * v 70 + v 24 * v 50 * v 70,
    -- fix-ell1-0
    v 1,
    -- fix-ell2-0
    v 2,
    -- fix-ell4-0
    v 4,
    -- fix-ell6-1
    1 + v 6,
    -- fix-ell7-0
    v 7,
    -- fix-y1-1
    1 + v 31,
    -- fix-y2-0
    v 32,
    -- fix-y4-0
    v 34,
    -- fix-y6-0
    v 36,
    -- fix-y7-0
    v 37,
    -- fix-correctionReturn0-1
    1 + v 70
  ]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_x1 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 0

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_x1_certificate
    (v : Fin 71 → F₂) :
    v 21 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_x1 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x1, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_x1_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 21 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_x1_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x1, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_x2 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 1

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_x2_certificate
    (v : Fin 71 → F₂) :
    v 22 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_x2 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x2, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_x2_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 22 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_x2_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x2, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_x3 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 2

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_x3_certificate
    (v : Fin 71 → F₂) :
    v 23 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_x3 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x3, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_x3_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 23 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_x3_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x3, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_x4 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 3

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_x4_certificate
    (v : Fin 71 → F₂) :
    v 24 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_x4 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x4, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_x4_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 24 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_x4_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x4, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_x6 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 4

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_x6_certificate
    (v : Fin 71 → F₂) :
    v 26 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_x6 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x6, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_x6_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 26 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_x6_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x6, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_x7 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 5

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_x7_certificate
    (v : Fin 71 → F₂) :
    v 27 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_x7 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x7, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_x7_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 27 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_x7_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x7, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_x8 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 6

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_x8_certificate
    (v : Fin 71 → F₂) :
    v 28 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_x8 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x8, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_x8_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 28 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_x8_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x8, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_x9 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 7

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_x9_certificate
    (v : Fin 71 → F₂) :
    v 29 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_x9 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x9, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_x9_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 29 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_x9_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_x9, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget6 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 8 +
  (v 16 * v 21 + v 17 * v 22 + v 11 * v 26 + v 12 * v 27 + v 6 * v 31 + v 26 * v 31 + v 7 * v 32 + v 27 * v 32 + v 1 * v 36 + v 21 * v 36 + v 2 * v 37 + v 22 * v 37 + v 26 * v 42 + v 27 * v 43 + v 21 * v 47 + v 22 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 1 + v 21) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 26) * zeroOneAlignedCorrectionOneSubstitutionSource v 23 +
  (1 + v 11 + v 42) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 0 +
  (1 + v 11 + v 42) * zeroOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 2 + v 22) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 12 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 12 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 19

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget6_certificate
    (v : Fin 71 → F₂) :
    v 68 + (1 + v 11 + v 42) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget6 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget6, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget6_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 68 = 1 + v 11 + v 42 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_correctionTarget6_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget6, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget7 (v : Fin 71 → F₂) : F₂ :=
  (v 16 * v 21 + v 17 * v 21 + v 17 * v 22 + v 16 * v 24 + v 11 * v 26 + v 14 * v 26 + v 11 * v 27 + v 12 * v 27 + v 6 * v 31 + v 7 * v 31 + v 26 * v 31 + v 27 * v 31 + v 7 * v 32 + v 27 * v 32 + v 6 * v 34 + v 26 * v 34 + v 1 * v 36 + v 4 * v 36 + v 21 * v 36 + v 24 * v 36 + v 1 * v 37 + v 2 * v 37 + v 21 * v 37 + v 22 * v 37 + v 26 * v 42 + v 27 * v 42 + v 27 * v 43 + v 26 * v 45 + v 21 * v 47 + v 24 * v 47 + v 21 * v 48 + v 22 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 11 +
  (v 1 + v 2 + v 21 + v 22) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 6 + v 7 + v 26 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 23 +
  (1 + v 11 + v 12 + v 42 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 16 + v 17 + v 47 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 0 +
  (1 + v 11 + v 12 + v 42 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 16 + v 17 + v 47 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 19 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 10 +
  (v 1 + v 4 + v 21 + v 24) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 26) * zeroOneAlignedCorrectionOneSubstitutionSource v 25 +
  (1 + v 11 + v 14 + v 42 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 3 +
  (1 + v 11 + v 14 + v 42 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 20 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 8

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget7_certificate
    (v : Fin 71 → F₂) :
    v 69 + (1 + v 11 + v 14 + v 42 + v 45) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget7 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget7, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget7_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 69 = 1 + v 11 + v 14 + v 42 + v 45 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_correctionTarget7_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget7, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget4 (v : Fin 71 → F₂) : F₂ :=
  (v 16 * v 22 + v 17 * v 24 + v 12 * v 26 + v 14 * v 27 + v 6 * v 32 + v 26 * v 32 + v 7 * v 34 + v 27 * v 34 + v 2 * v 36 + v 22 * v 36 + v 4 * v 37 + v 24 * v 37 + v 26 * v 43 + v 27 * v 45 + v 22 * v 47 + v 24 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 2 + v 22) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 25 +
  (v 12 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 12 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 20 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 14 +
  (v 4 + v 24) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 14 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 14 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 9 +
  (v 6 + v 26) * zeroOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 19

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget4_certificate
    (v : Fin 71 → F₂) :
    v 66 + (v 12 + v 43) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget4 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget4, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget4_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 66 = v 12 + v 43 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_correctionTarget4_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget4, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear2 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 11 +
  (v 17 * v 21 + v 16 * v 22 + v 12 * v 26 + v 11 * v 27 + v 7 * v 31 + v 27 * v 31 + v 6 * v 32 + v 26 * v 32 + v 2 * v 36 + v 22 * v 36 + v 1 * v 37 + v 21 * v 37 + v 27 * v 42 + v 26 * v 43 + v 22 * v 47 + v 21 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 1 + v 21) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 23 +
  (1 + v 11 + v 42) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 0 +
  (1 + v 11 + v 42) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 9 +
  (v 2 + v 22) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 26) * zeroOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 12 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 12 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 19

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_factorLinear2_certificate
    (v : Fin 71 → F₂) :
    v 43 + (v 12) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear2 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear2, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_factorLinear2_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 43 = v 12 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_factorLinear2_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear2, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget1 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 17 * v 22 + v 12 * v 27 + v 7 * v 32 + v 27 * v 32 + v 2 * v 37 + v 22 * v 37 + v 27 * v 43 + v 22 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 2 + v 22) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 12 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 12 + v 43) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 19

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget1_certificate
    (v : Fin 71 → F₂) :
    v 63 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget1 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget1, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget1_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 63 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_correctionTarget1_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget1, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear4 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 14 +
  (v 16 * v 21 + v 17 * v 21 + v 16 * v 24 + v 17 * v 24 + v 11 * v 26 + v 14 * v 26 + v 11 * v 27 + v 14 * v 27 + v 6 * v 31 + v 7 * v 31 + v 26 * v 31 + v 27 * v 31 + v 6 * v 34 + v 7 * v 34 + v 26 * v 34 + v 27 * v 34 + v 1 * v 36 + v 4 * v 36 + v 21 * v 36 + v 24 * v 36 + v 1 * v 37 + v 4 * v 37 + v 21 * v 37 + v 24 * v 37 + v 26 * v 42 + v 27 * v 42 + v 26 * v 45 + v 27 * v 45 + v 21 * v 47 + v 24 * v 47 + v 21 * v 48 + v 24 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 1 + v 4 + v 21 + v 24) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 6 + v 7 + v 26 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 25 +
  (1 + v 11 + v 14 + v 42 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 16 + v 17 + v 47 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 3 +
  (1 + v 11 + v 14 + v 42 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 16 + v 17 + v 47 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 20 +
  (v 1 + v 4 + v 21 + v 24) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (1 + v 11 + v 14 + v 42 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (1 + v 11 + v 14 + v 42 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 21 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 10 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 8 +
  (v 6 + v 7 + v 26 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 23 +
  (v 16 + v 17 + v 47 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 0 +
  (v 16 + v 17 + v 47 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 11

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_factorLinear4_certificate
    (v : Fin 71 → F₂) :
    v 45 + (1 + v 11 + v 14 + v 42) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear4 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear4, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_factorLinear4_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 45 = 1 + v 11 + v 14 + v 42 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_factorLinear4_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear4, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear7 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 15 +
  (v 17 * v 26 + v 16 * v 27 + v 7 * v 36 + v 27 * v 36 + v 6 * v 37 + v 26 * v 37 + v 27 * v 47 + v 26 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 6 + v 26) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 16 + v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 21

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_factorLinear7_certificate
    (v : Fin 71 → F₂) :
    v 48 + (v 17) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear7 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear7, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_factorLinear7_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 48 = v 17 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_factorLinear7_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear7, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear1 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 13 +
  (v 16 * v 21 + v 17 * v 21 + v 17 * v 23 + v 17 * v 24 + v 11 * v 26 + v 3 * v 17 * v 26 + v 11 * v 27 + v 13 * v 27 + v 14 * v 27 + v 3 * v 16 * v 27 + v 6 * v 31 + v 7 * v 31 + v 26 * v 31 + v 27 * v 31 + v 7 * v 33 + v 27 * v 33 + v 7 * v 34 + v 27 * v 34 + v 1 * v 36 + v 3 * v 7 * v 36 + v 21 * v 36 + v 3 * v 27 * v 36 + v 1 * v 37 + v 3 * v 37 + v 4 * v 37 + v 3 * v 6 * v 37 + v 21 * v 37 + v 23 * v 37 + v 24 * v 37 + v 3 * v 26 * v 37 + v 26 * v 42 + v 27 * v 42 + v 27 * v 44 + v 27 * v 45 + v 21 * v 47 + v 3 * v 27 * v 47 + v 21 * v 48 + v 23 * v 48 + v 24 * v 48 + v 3 * v 26 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 1 + v 3 + v 4 + v 3 * v 6 + v 21 + v 23 + v 24 + v 3 * v 26) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (1 + v 11 + v 13 + v 14 + v 3 * v 16 + v 33 + v 42 + v 44 + v 45 + v 3 * v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 2 +
  (1 + v 11 + v 13 + v 14 + v 3 * v 16 + v 33 + v 42 + v 44 + v 45 + v 3 * v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 8 +
  (v 1 + v 3 * v 7 + v 21 + v 3 * v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 6 + v 7 + v 26 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 23 +
  (1 + v 11 + v 3 * v 17 + v 42 + v 3 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 16 + v 17 + v 47 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 0 +
  (1 + v 11 + v 3 * v 17 + v 42 + v 3 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 16 + v 17 + v 47 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 18 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 25 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 20 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 14 +
  (v 3) * zeroOneAlignedCorrectionOneSubstitutionSource v 15 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 11

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_factorLinear1_certificate
    (v : Fin 71 → F₂) :
    v 42 + (1 + v 11) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear1 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear1, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_factorLinear1_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 42 = 1 + v 11 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_factorLinear1_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_factorLinear1, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget5 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 16 +
  (v 17 * v 21 + v 17 * v 22 + v 8 * v 17 * v 23 + v 8 * v 16 * v 24 + v 17 * v 24 + v 18 * v 24 + v 8 * v 14 * v 26 + v 3 * v 8 * v 17 * v 26 + v 11 * v 27 + v 12 * v 27 + v 8 * v 13 * v 27 + v 14 * v 27 + v 3 * v 8 * v 16 * v 27 + v 14 * v 28 + v 7 * v 31 + v 27 * v 31 + v 7 * v 32 + v 27 * v 32 + v 7 * v 8 * v 33 + v 8 * v 27 * v 33 + v 7 * v 34 + v 8 * v 34 + v 6 * v 8 * v 34 + v 8 * v 26 * v 34 + v 27 * v 34 + v 28 * v 34 + v 4 * v 8 * v 36 + v 3 * v 7 * v 8 * v 36 + v 8 * v 24 * v 36 + v 3 * v 8 * v 27 * v 36 + v 1 * v 37 + v 2 * v 37 + v 4 * v 37 + v 3 * v 8 * v 37 + v 3 * v 6 * v 8 * v 37 + v 21 * v 37 + v 22 * v 37 + v 8 * v 23 * v 37 + v 24 * v 37 + v 3 * v 8 * v 26 * v 37 + v 4 * v 38 + v 24 * v 38 + v 27 * v 42 + v 27 * v 43 + v 8 * v 27 * v 44 + v 8 * v 26 * v 45 + v 27 * v 45 + v 28 * v 45 + v 8 * v 24 * v 47 + v 3 * v 8 * v 27 * v 47 + v 21 * v 48 + v 22 * v 48 + v 8 * v 23 * v 48 + v 24 * v 48 + v 3 * v 8 * v 26 * v 48 + v 24 * v 49) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 7 + v 8 + v 6 * v 8 + v 8 * v 26 + v 27 + v 28) * zeroOneAlignedCorrectionOneSubstitutionSource v 25 +
  (v 14 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 6 +
  (v 8 * v 16 + v 17 + v 18 + v 38 + v 8 * v 47 + v 48 + v 49) * zeroOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 8 * v 16 + v 17 + v 18 + v 38 + v 8 * v 47 + v 48 + v 49) * zeroOneAlignedCorrectionOneSubstitutionSource v 20 +
  (v 4 * v 8 + v 3 * v 7 * v 8 + v 8 * v 24 + v 3 * v 8 * v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 8 * v 14 + v 3 * v 8 * v 17 + v 8 * v 45 + v 3 * v 8 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 8 * v 14 + v 3 * v 8 * v 17 + v 8 * v 45 + v 3 * v 8 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 21 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 14 +
  (v 1 + v 2 + v 4 + v 3 * v 8 + v 3 * v 6 * v 8 + v 21 + v 22 + v 8 * v 23 + v 24 + v 3 * v 8 * v 26) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (1 + v 11 + v 12 + v 8 * v 13 + v 14 + v 3 * v 8 * v 16 + v 8 * v 33 + v 42 + v 43 + v 8 * v 44 + v 45 + v 3 * v 8 * v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (1 + v 11 + v 12 + v 8 * v 13 + v 14 + v 3 * v 8 * v 16 + v 8 * v 33 + v 42 + v 43 + v 8 * v 44 + v 45 + v 3 * v 8 * v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 19 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 8) * zeroOneAlignedCorrectionOneSubstitutionSource v 10 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 23 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 0 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 18 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 11 +
  (v 8) * zeroOneAlignedCorrectionOneSubstitutionSource v 13 +
  (v 8 * v 17 + v 8 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 2 +
  (v 3 * v 8) * zeroOneAlignedCorrectionOneSubstitutionSource v 15

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget5_certificate
    (v : Fin 71 → F₂) :
    v 67 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget5 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget5, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget5_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 67 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_correctionTarget5_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget5, hzero]


private def zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget2 (v : Fin 71 → F₂) : F₂ :=
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 17 +
  (v 17 * v 22 + v 9 * v 17 * v 23 + v 9 * v 16 * v 24 + v 19 * v 24 + v 9 * v 14 * v 26 + v 3 * v 9 * v 17 * v 26 + v 12 * v 27 + v 9 * v 13 * v 27 + v 3 * v 9 * v 16 * v 27 + v 14 * v 29 + v 7 * v 32 + v 27 * v 32 + v 7 * v 9 * v 33 + v 9 * v 27 * v 33 + v 9 * v 34 + v 6 * v 9 * v 34 + v 9 * v 26 * v 34 + v 29 * v 34 + v 4 * v 9 * v 36 + v 3 * v 7 * v 9 * v 36 + v 9 * v 24 * v 36 + v 3 * v 9 * v 27 * v 36 + v 2 * v 37 + v 3 * v 9 * v 37 + v 3 * v 6 * v 9 * v 37 + v 22 * v 37 + v 9 * v 23 * v 37 + v 3 * v 9 * v 26 * v 37 + v 4 * v 39 + v 24 * v 39 + v 27 * v 43 + v 9 * v 27 * v 44 + v 9 * v 26 * v 45 + v 29 * v 45 + v 9 * v 24 * v 47 + v 3 * v 9 * v 27 * v 47 + v 22 * v 48 + v 9 * v 23 * v 48 + v 3 * v 9 * v 26 * v 48 + v 24 * v 50) * zeroOneAlignedCorrectionOneSubstitutionSource v 28 +
  (v 9 + v 6 * v 9 + v 9 * v 26 + v 29) * zeroOneAlignedCorrectionOneSubstitutionSource v 25 +
  (v 14 + v 45) * zeroOneAlignedCorrectionOneSubstitutionSource v 7 +
  (v 9 * v 16 + v 19 + v 39 + v 9 * v 47 + v 50) * zeroOneAlignedCorrectionOneSubstitutionSource v 3 +
  (v 9 * v 16 + v 19 + v 39 + v 9 * v 47 + v 50) * zeroOneAlignedCorrectionOneSubstitutionSource v 20 +
  (1) * zeroOneAlignedCorrectionOneSubstitutionSource v 12 +
  (v 2 + v 3 * v 9 + v 3 * v 6 * v 9 + v 22 + v 9 * v 23 + v 3 * v 9 * v 26) * zeroOneAlignedCorrectionOneSubstitutionSource v 27 +
  (v 7 + v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 24 +
  (v 12 + v 9 * v 13 + v 3 * v 9 * v 16 + v 9 * v 33 + v 43 + v 9 * v 44 + v 3 * v 9 * v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 5 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 1 +
  (v 12 + v 9 * v 13 + v 3 * v 9 * v 16 + v 9 * v 33 + v 43 + v 9 * v 44 + v 3 * v 9 * v 47) * zeroOneAlignedCorrectionOneSubstitutionSource v 22 +
  (v 17 + v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 19 +
  (v 4 * v 9 + v 3 * v 7 * v 9 + v 9 * v 24 + v 3 * v 9 * v 27) * zeroOneAlignedCorrectionOneSubstitutionSource v 26 +
  (v 9 * v 14 + v 3 * v 9 * v 17 + v 9 * v 45 + v 3 * v 9 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 4 +
  (v 9 * v 14 + v 3 * v 9 * v 17 + v 9 * v 45 + v 3 * v 9 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 21 +
  (v 9) * zeroOneAlignedCorrectionOneSubstitutionSource v 10 +
  (v 9) * zeroOneAlignedCorrectionOneSubstitutionSource v 13 +
  (v 9 * v 17 + v 9 * v 48) * zeroOneAlignedCorrectionOneSubstitutionSource v 2 +
  (v 3 * v 9) * zeroOneAlignedCorrectionOneSubstitutionSource v 15

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget2_certificate
    (v : Fin 71 → F₂) :
    v 64 + (0) =
      zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget2 v := by
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget2, zeroOneAlignedCorrectionOneSubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem zeroOneAlignedCorrectionOne_substitution_correctionTarget2_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, zeroOneAlignedCorrectionOneSubstitutionSource v i = 0) :
    v 64 = 0 := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [zeroOneAlignedCorrectionOne_substitution_correctionTarget2_certificate]
  simp [zeroOneAlignedCorrectionOneSubstitutionCombination_correctionTarget2, hzero]

/-- The semantic high equations and normalized fixed values discharge
every source equation used by affine elimination. -/
private theorem zeroOneAlignedCorrectionOne_substitution_source_eq_zero
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : ZeroOneAlignedNormalForm p)
    (hcorrection : p.correctionReturn = (1 : F₂))
    (hbase : ∀ i : Fin 34, zeroOneAlignedBaseConstraint p.vector i = 0) :
    ∀ i : Fin 29, zeroOneAlignedCorrectionOneSubstitutionSource p.vector i = 0 := by
  intro i
  fin_cases i
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (0 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (0 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (1 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (1 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (2 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (2 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (3 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (3 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (4 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (4 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (5 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (5 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (6 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (6 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (7 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (7 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (8 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (13 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (9 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (15 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (10 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (16 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (11 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (19 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (12 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (20 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (13 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (21 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (14 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (22 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (15 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (25 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (16 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (26 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (17 : Fin 29) = 0
    simpa [zeroOneAlignedCorrectionOneSubstitutionSource, zeroOneAlignedBaseConstraint] using
      hbase (27 : Fin 34)
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (18 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.ell1]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (19 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.ell2]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (20 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.ell4]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (21 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.ell6]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (22 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.ell7]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (23 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.y1]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (24 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.y2]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (25 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.y4]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (26 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.y6]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (27 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hnormal.y7]
  · change zeroOneAlignedCorrectionOneSubstitutionSource p.vector (28 : Fin 29) = 0
    simp [zeroOneAlignedCorrectionOneSubstitutionSource,
      ZeroOneOffAxisHistoryParameters.vector, hcorrection]

/-- All 29 substitutions used by the compact certificate follow from
the literal history equations and the aligned normal form. -/
private theorem zeroOneAlignedCorrectionOne_substitutions_of_source_zero
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : ZeroOneAlignedNormalForm p)
    (hcorrection : p.correctionReturn = (1 : F₂))
    (hsource : ∀ i : Fin 29,
      zeroOneAlignedCorrectionOneSubstitutionSource p.vector i = 0) :
    ZeroOneAlignedCorrectionOneSubstitutions p.vector := by
  refine {
    x1 := zeroOneAlignedCorrectionOne_substitution_x1_of_source_zero p.vector hsource
    x2 := zeroOneAlignedCorrectionOne_substitution_x2_of_source_zero p.vector hsource
    x3 := zeroOneAlignedCorrectionOne_substitution_x3_of_source_zero p.vector hsource
    x4 := zeroOneAlignedCorrectionOne_substitution_x4_of_source_zero p.vector hsource
    x6 := zeroOneAlignedCorrectionOne_substitution_x6_of_source_zero p.vector hsource
    x7 := zeroOneAlignedCorrectionOne_substitution_x7_of_source_zero p.vector hsource
    x8 := zeroOneAlignedCorrectionOne_substitution_x8_of_source_zero p.vector hsource
    x9 := zeroOneAlignedCorrectionOne_substitution_x9_of_source_zero p.vector hsource
    ell1 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.ell1
    ell2 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.ell2
    ell4 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.ell4
    ell6 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.ell6
    ell7 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.ell7
    y1 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.y1
    y2 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.y2
    y4 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.y4
    y6 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.y6
    y7 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hnormal.y7
    correctionReturn0 := by simpa [ZeroOneOffAxisHistoryParameters.vector] using hcorrection
    correctionTarget6 := zeroOneAlignedCorrectionOne_substitution_correctionTarget6_of_source_zero p.vector hsource
    correctionTarget7 := zeroOneAlignedCorrectionOne_substitution_correctionTarget7_of_source_zero p.vector hsource
    correctionTarget4 := zeroOneAlignedCorrectionOne_substitution_correctionTarget4_of_source_zero p.vector hsource
    factorLinear2 := zeroOneAlignedCorrectionOne_substitution_factorLinear2_of_source_zero p.vector hsource
    correctionTarget1 := zeroOneAlignedCorrectionOne_substitution_correctionTarget1_of_source_zero p.vector hsource
    factorLinear4 := zeroOneAlignedCorrectionOne_substitution_factorLinear4_of_source_zero p.vector hsource
    factorLinear7 := zeroOneAlignedCorrectionOne_substitution_factorLinear7_of_source_zero p.vector hsource
    factorLinear1 := zeroOneAlignedCorrectionOne_substitution_factorLinear1_of_source_zero p.vector hsource
    correctionTarget5 := zeroOneAlignedCorrectionOne_substitution_correctionTarget5_of_source_zero p.vector hsource
    correctionTarget2 := zeroOneAlignedCorrectionOne_substitution_correctionTarget2_of_source_zero p.vector hsource
  }

/-- The exceptional aligned leaf is inconsistent with the literal
quadratic return-history hypotheses. -/
theorem zeroOneAlignedCorrectionOne_inconsistent_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : ZeroOneAlignedNormalForm p)
    (hcorrection : p.correctionReturn = (1 : F₂))
    (hreturned : mixedReturnSection .zeroOne p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne .zero p ∈
      N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p))) :
    False := by
  have hbase := zeroOneAligned_base_equations_of_quadratic_history p
    hreturned hfeedback hprojection
  have hsource := zeroOneAlignedCorrectionOne_substitution_source_eq_zero p hnormal
    hcorrection hbase
  have hsub := zeroOneAlignedCorrectionOne_substitutions_of_source_zero p hnormal
    hcorrection hsource
  apply zeroOneAlignedCorrectionOne_inconsistent_of_original p.vector hsub
  intro i
  simpa [zeroOneAlignedCorrectionOneOriginalConstraint] using
    hbase ((![8, 9, 10, 11, 12, 14, 17, 18, 23, 24, 28, 29, 30, 31, 32, 33] : Fin 16 → Fin 34) i)

end
end N5
end UnrestrictedBooleanMul
