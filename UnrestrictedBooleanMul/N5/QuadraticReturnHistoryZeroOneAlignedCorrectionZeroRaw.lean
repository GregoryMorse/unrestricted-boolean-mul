import UnrestrictedBooleanMul.ANF

/-!
# Reduced aligned certificate: `ZeroOneAlignedCorrectionZero`

This generated module checks a sparse Boolean-polynomial unit
identity.  External algebra was used only to discover the stored
multipliers; Lean replays the identity without extra axioms.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192

/-- The 16 reduced semantic generators in this unit certificate. -/
def zeroOneAlignedCorrectionZeroReducedConstraint (v : Fin 71 → F₂) : Fin 16 → F₂ :=
  ![
    -- product-high-0x023
    v 5 * v 10 * v 11 + v 0 * v 11 * v 15 + v 5 * v 11 * v 41 + v 0 * v 11 * v 46 + v 53 + v 11 * v 62 + v 65 + v 41 * v 65,
    -- product-high-0x025
    v 5 * v 10 * v 12 + v 0 * v 12 * v 15 + v 5 * v 12 * v 41 + v 0 * v 12 * v 46 + v 54 + v 12 * v 62,
    -- product-high-0x043
    v 10 * v 11 + v 0 * v 11 * v 16 + v 11 * v 41 + v 0 * v 11 * v 47 + v 11 * v 65,
    -- product-high-0x061
    1 + v 10 + v 15 + v 16 + v 0 * v 16 + v 5 * v 16 + v 40 + v 41 + v 15 * v 41 + v 5 * v 16 * v 41 + v 46 + v 10 * v 46 + v 0 * v 16 * v 46 + v 47 + v 0 * v 47 + v 5 * v 47 + v 5 * v 10 * v 47 + v 0 * v 15 * v 47 + v 58 + v 47 * v 62 + v 65 + v 46 * v 65,
    -- product-high-0x062
    v 11 * v 15 + v 5 * v 11 * v 16 + v 11 * v 46 + v 5 * v 11 * v 47 + v 47 * v 65,
    -- product-high-0x064
    v 12 * v 15 + v 5 * v 12 * v 16 + v 12 * v 46 + v 5 * v 12 * v 47,
    -- product-high-0x0a1
    v 5 * v 10 * v 17 + v 0 * v 15 * v 17 + v 5 * v 17 * v 41 + v 0 * v 17 * v 46 + v 59 + v 17 * v 62,
    -- product-high-0x0a2
    v 17 * v 65,
    -- product-high-0x0c1
    v 10 * v 17 + v 0 * v 16 * v 17 + v 17 * v 41 + v 0 * v 17 * v 47 + v 17 * v 65,
    -- product-high-0x0e0
    v 15 * v 17 + v 5 * v 16 * v 17 + v 17 * v 46 + v 5 * v 17 * v 47,
    -- quotient-6
    v 5 * v 12 + v 5 * v 12 * v 15 + v 0 * v 17 + v 0 * v 10 * v 17 + v 17 * v 20 + v 12 * v 25 + v 5 * v 12 * v 40 + v 0 * v 17 * v 40 + v 0 * v 17 * v 41 + v 5 * v 12 * v 46 + v 17 * v 52 + v 46 * v 54 + v 12 * v 57 + v 41 * v 59,
    -- quotient-13
    1 + v 11 + v 5 * v 12 + v 5 * v 12 * v 15 + v 11 * v 16 + v 12 * v 25 + v 11 * v 40 + v 5 * v 12 * v 40 + v 5 * v 12 * v 46 + v 11 * v 47 + v 47 * v 53 + v 46 * v 54 + v 12 * v 57 + v 11 * v 58,
    -- quotient-14
    v 13 * v 25 + v 5 * v 33 + v 25 * v 33 + v 3 * v 35 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 17 * v 53 + v 46 * v 55 + v 44 * v 57 + v 11 * v 59,
    -- quotient-20
    v 12 + v 12 * v 16 + v 13 * v 25 + v 5 * v 33 + v 25 * v 33 + v 3 * v 35 + v 12 * v 40 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 12 * v 47 + v 47 * v 54 + v 46 * v 55 + v 44 * v 57 + v 12 * v 58,
    -- quotient-36
    v 5 * v 17 + v 5 * v 15 * v 17 + v 17 * v 25 + v 5 * v 17 * v 40 + v 5 * v 17 * v 46 + v 17 * v 57 + v 46 * v 59,
    -- quotient-39
    v 17 + v 16 * v 17 + v 17 * v 40 + v 17 * v 47 + v 17 * v 58 + v 47 * v 59
  ]

private def zeroOneAlignedCorrectionZeroReducedMultiplier (v : Fin 71 → F₂) : Fin 16 → F₂ :=
  ![
    -- product-high-0x023
    v 5 * v 17 + v 47,
    -- product-high-0x025
    v 17 * v 46 + v 5 * v 17 * v 47,
    -- product-high-0x043
    1 + v 46,
    -- product-high-0x061
    v 11,
    -- product-high-0x062
    1 + v 41,
    -- product-high-0x064
    v 17,
    -- product-high-0x0a1
    v 5 * v 11 * v 17 + v 41 + v 17 * v 41 + v 12 * v 46 + v 5 * v 12 * v 47,
    -- product-high-0x0a2
    1 + v 5 + v 17 + v 5 * v 41,
    -- product-high-0x0c1
    1 + v 17,
    -- product-high-0x0e0
    v 12,
    -- quotient-6
    1 + v 17,
    -- quotient-13
    1,
    -- quotient-14
    v 5 * v 17,
    -- quotient-20
    v 5 * v 17,
    -- quotient-36
    v 12,
    -- quotient-39
    v 5 * v 12
  ]

private def zeroOneAlignedCorrectionZeroReducedProduct (v : Fin 71 → F₂) : Fin 16 → F₂ :=
  ![
    -- product-high-0x023
    v 5 * v 10 * v 11 * v 17 + v 0 * v 5 * v 11 * v 15 * v 17 + v 5 * v 11 * v 17 * v 41 + v 0 * v 5 * v 11 * v 17 * v 46 + v 5 * v 10 * v 11 * v 47 + v 0 * v 11 * v 15 * v 47 + v 5 * v 11 * v 41 * v 47 + v 0 * v 11 * v 46 * v 47 + v 5 * v 17 * v 53 + v 47 * v 53 + v 5 * v 11 * v 17 * v 62 + v 11 * v 47 * v 62 + v 5 * v 17 * v 65 + v 5 * v 17 * v 41 * v 65 + v 47 * v 65 + v 41 * v 47 * v 65,
    -- product-high-0x025
    v 0 * v 12 * v 17 * v 46 + v 5 * v 10 * v 12 * v 17 * v 46 + v 0 * v 12 * v 15 * v 17 * v 46 + v 5 * v 12 * v 17 * v 41 * v 46 + v 5 * v 10 * v 12 * v 17 * v 47 + v 0 * v 5 * v 12 * v 15 * v 17 * v 47 + v 5 * v 12 * v 17 * v 41 * v 47 + v 0 * v 5 * v 12 * v 17 * v 46 * v 47 + v 17 * v 46 * v 54 + v 5 * v 17 * v 47 * v 54 + v 12 * v 17 * v 46 * v 62 + v 5 * v 12 * v 17 * v 47 * v 62,
    -- product-high-0x043
    v 10 * v 11 + v 0 * v 11 * v 16 + v 11 * v 41 + v 10 * v 11 * v 46 + v 0 * v 11 * v 16 * v 46 + v 11 * v 41 * v 46 + v 0 * v 11 * v 47 + v 0 * v 11 * v 46 * v 47 + v 11 * v 65 + v 11 * v 46 * v 65,
    -- product-high-0x061
    v 11 + v 10 * v 11 + v 11 * v 15 + v 11 * v 16 + v 0 * v 11 * v 16 + v 5 * v 11 * v 16 + v 11 * v 40 + v 11 * v 41 + v 11 * v 15 * v 41 + v 5 * v 11 * v 16 * v 41 + v 11 * v 46 + v 10 * v 11 * v 46 + v 0 * v 11 * v 16 * v 46 + v 11 * v 47 + v 0 * v 11 * v 47 + v 5 * v 11 * v 47 + v 5 * v 10 * v 11 * v 47 + v 0 * v 11 * v 15 * v 47 + v 11 * v 58 + v 11 * v 47 * v 62 + v 11 * v 65 + v 11 * v 46 * v 65,
    -- product-high-0x062
    v 11 * v 15 + v 5 * v 11 * v 16 + v 11 * v 15 * v 41 + v 5 * v 11 * v 16 * v 41 + v 11 * v 46 + v 11 * v 41 * v 46 + v 5 * v 11 * v 47 + v 5 * v 11 * v 41 * v 47 + v 47 * v 65 + v 41 * v 47 * v 65,
    -- product-high-0x064
    v 12 * v 15 * v 17 + v 5 * v 12 * v 16 * v 17 + v 12 * v 17 * v 46 + v 5 * v 12 * v 17 * v 47,
    -- product-high-0x0a1
    v 5 * v 10 * v 11 * v 17 + v 0 * v 5 * v 11 * v 15 * v 17 + v 5 * v 11 * v 17 * v 41 + v 0 * v 5 * v 11 * v 17 * v 46 + v 0 * v 12 * v 17 * v 46 + v 5 * v 10 * v 12 * v 17 * v 46 + v 0 * v 12 * v 15 * v 17 * v 46 + v 5 * v 12 * v 17 * v 41 * v 46 + v 5 * v 10 * v 12 * v 17 * v 47 + v 0 * v 5 * v 12 * v 15 * v 17 * v 47 + v 5 * v 12 * v 17 * v 41 * v 47 + v 0 * v 5 * v 12 * v 17 * v 46 * v 47 + v 5 * v 11 * v 17 * v 59 + v 41 * v 59 + v 17 * v 41 * v 59 + v 12 * v 46 * v 59 + v 5 * v 12 * v 47 * v 59 + v 5 * v 11 * v 17 * v 62 + v 12 * v 17 * v 46 * v 62 + v 5 * v 12 * v 17 * v 47 * v 62,
    -- product-high-0x0a2
    v 5 * v 17 * v 65 + v 5 * v 17 * v 41 * v 65,
    -- product-high-0x0c1
    0,
    -- product-high-0x0e0
    v 12 * v 15 * v 17 + v 5 * v 12 * v 16 * v 17 + v 12 * v 17 * v 46 + v 5 * v 12 * v 17 * v 47,
    -- quotient-6
    v 5 * v 12 + v 5 * v 12 * v 15 + v 5 * v 12 * v 17 + v 5 * v 12 * v 15 * v 17 + v 12 * v 25 + v 12 * v 17 * v 25 + v 5 * v 12 * v 40 + v 5 * v 12 * v 17 * v 40 + v 5 * v 12 * v 46 + v 5 * v 12 * v 17 * v 46 + v 46 * v 54 + v 17 * v 46 * v 54 + v 12 * v 57 + v 12 * v 17 * v 57 + v 41 * v 59 + v 17 * v 41 * v 59,
    -- quotient-13
    1 + v 11 + v 5 * v 12 + v 5 * v 12 * v 15 + v 11 * v 16 + v 12 * v 25 + v 11 * v 40 + v 5 * v 12 * v 40 + v 5 * v 12 * v 46 + v 11 * v 47 + v 47 * v 53 + v 46 * v 54 + v 12 * v 57 + v 11 * v 58,
    -- quotient-14
    v 5 * v 13 * v 17 * v 25 + v 5 * v 17 * v 33 + v 5 * v 17 * v 25 * v 33 + v 3 * v 5 * v 17 * v 35 + v 5 * v 13 * v 17 * v 40 + v 3 * v 5 * v 15 * v 17 * v 40 + v 5 * v 13 * v 17 * v 44 + v 5 * v 15 * v 17 * v 44 + v 3 * v 5 * v 15 * v 17 * v 44 + v 5 * v 13 * v 17 * v 46 + v 3 * v 5 * v 13 * v 17 * v 46 + v 3 * v 5 * v 15 * v 17 * v 46 + v 5 * v 17 * v 53 + v 5 * v 17 * v 46 * v 55 + v 5 * v 17 * v 44 * v 57 + v 5 * v 11 * v 17 * v 59,
    -- quotient-20
    v 5 * v 12 * v 17 + v 5 * v 12 * v 16 * v 17 + v 5 * v 13 * v 17 * v 25 + v 5 * v 17 * v 33 + v 5 * v 17 * v 25 * v 33 + v 3 * v 5 * v 17 * v 35 + v 5 * v 12 * v 17 * v 40 + v 5 * v 13 * v 17 * v 40 + v 3 * v 5 * v 15 * v 17 * v 40 + v 5 * v 13 * v 17 * v 44 + v 5 * v 15 * v 17 * v 44 + v 3 * v 5 * v 15 * v 17 * v 44 + v 5 * v 13 * v 17 * v 46 + v 3 * v 5 * v 13 * v 17 * v 46 + v 3 * v 5 * v 15 * v 17 * v 46 + v 5 * v 12 * v 17 * v 47 + v 5 * v 17 * v 47 * v 54 + v 5 * v 17 * v 46 * v 55 + v 5 * v 17 * v 44 * v 57 + v 5 * v 12 * v 17 * v 58,
    -- quotient-36
    v 5 * v 12 * v 17 + v 5 * v 12 * v 15 * v 17 + v 12 * v 17 * v 25 + v 5 * v 12 * v 17 * v 40 + v 5 * v 12 * v 17 * v 46 + v 12 * v 17 * v 57 + v 12 * v 46 * v 59,
    -- quotient-39
    v 5 * v 12 * v 17 + v 5 * v 12 * v 16 * v 17 + v 5 * v 12 * v 17 * v 40 + v 5 * v 12 * v 17 * v 47 + v 5 * v 12 * v 17 * v 58 + v 5 * v 12 * v 47 * v 59
  ]

private def zeroOneAlignedCorrectionZeroReducedCombination (v : Fin 71 → F₂) : F₂ :=
  zeroOneAlignedCorrectionZeroReducedMultiplier v 0 * zeroOneAlignedCorrectionZeroReducedConstraint v 0 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 1 * zeroOneAlignedCorrectionZeroReducedConstraint v 1 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 2 * zeroOneAlignedCorrectionZeroReducedConstraint v 2 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 3 * zeroOneAlignedCorrectionZeroReducedConstraint v 3 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 4 * zeroOneAlignedCorrectionZeroReducedConstraint v 4 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 5 * zeroOneAlignedCorrectionZeroReducedConstraint v 5 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 6 * zeroOneAlignedCorrectionZeroReducedConstraint v 6 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 7 * zeroOneAlignedCorrectionZeroReducedConstraint v 7 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 8 * zeroOneAlignedCorrectionZeroReducedConstraint v 8 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 9 * zeroOneAlignedCorrectionZeroReducedConstraint v 9 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 10 * zeroOneAlignedCorrectionZeroReducedConstraint v 10 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 11 * zeroOneAlignedCorrectionZeroReducedConstraint v 11 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 12 * zeroOneAlignedCorrectionZeroReducedConstraint v 12 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 13 * zeroOneAlignedCorrectionZeroReducedConstraint v 13 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 14 * zeroOneAlignedCorrectionZeroReducedConstraint v 14 +
  zeroOneAlignedCorrectionZeroReducedMultiplier v 15 * zeroOneAlignedCorrectionZeroReducedConstraint v 15

private theorem f2_mul_self (x : F₂) : x * x = x := by
  rcases f2_eq_zero_or_one x with h | h <;> simp [h]

private theorem f2_two_eq_zero : (2 : F₂) = 0 :=
  CharTwo.two_eq_zero

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_0 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 0 * zeroOneAlignedCorrectionZeroReducedConstraint v 0 =
      zeroOneAlignedCorrectionZeroReducedProduct v 0 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_1 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 1 * zeroOneAlignedCorrectionZeroReducedConstraint v 1 =
      zeroOneAlignedCorrectionZeroReducedProduct v 1 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_2 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 2 * zeroOneAlignedCorrectionZeroReducedConstraint v 2 =
      zeroOneAlignedCorrectionZeroReducedProduct v 2 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_3 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 3 * zeroOneAlignedCorrectionZeroReducedConstraint v 3 =
      zeroOneAlignedCorrectionZeroReducedProduct v 3 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_4 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 4 * zeroOneAlignedCorrectionZeroReducedConstraint v 4 =
      zeroOneAlignedCorrectionZeroReducedProduct v 4 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_5 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 5 * zeroOneAlignedCorrectionZeroReducedConstraint v 5 =
      zeroOneAlignedCorrectionZeroReducedProduct v 5 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_6 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 6 * zeroOneAlignedCorrectionZeroReducedConstraint v 6 =
      zeroOneAlignedCorrectionZeroReducedProduct v 6 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_7 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 7 * zeroOneAlignedCorrectionZeroReducedConstraint v 7 =
      zeroOneAlignedCorrectionZeroReducedProduct v 7 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_8 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 8 * zeroOneAlignedCorrectionZeroReducedConstraint v 8 =
      zeroOneAlignedCorrectionZeroReducedProduct v 8 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_9 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 9 * zeroOneAlignedCorrectionZeroReducedConstraint v 9 =
      zeroOneAlignedCorrectionZeroReducedProduct v 9 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_10 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 10 * zeroOneAlignedCorrectionZeroReducedConstraint v 10 =
      zeroOneAlignedCorrectionZeroReducedProduct v 10 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_11 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 11 * zeroOneAlignedCorrectionZeroReducedConstraint v 11 =
      zeroOneAlignedCorrectionZeroReducedProduct v 11 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_12 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 12 * zeroOneAlignedCorrectionZeroReducedConstraint v 12 =
      zeroOneAlignedCorrectionZeroReducedProduct v 12 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_13 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 13 * zeroOneAlignedCorrectionZeroReducedConstraint v 13 =
      zeroOneAlignedCorrectionZeroReducedProduct v 13 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_14 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 14 * zeroOneAlignedCorrectionZeroReducedConstraint v 14 =
      zeroOneAlignedCorrectionZeroReducedProduct v 14 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionZeroReduced_product_15 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionZeroReducedMultiplier v 15 * zeroOneAlignedCorrectionZeroReducedConstraint v 15 =
      zeroOneAlignedCorrectionZeroReducedProduct v 15 := by
  simp [zeroOneAlignedCorrectionZeroReducedMultiplier, zeroOneAlignedCorrectionZeroReducedConstraint,
    zeroOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionZeroReduced_certificate (v : Fin 71 → F₂) :
    (1 : F₂) = zeroOneAlignedCorrectionZeroReducedCombination v := by
  unfold zeroOneAlignedCorrectionZeroReducedCombination
  rw [zeroOneAlignedCorrectionZeroReduced_product_0, zeroOneAlignedCorrectionZeroReduced_product_1, zeroOneAlignedCorrectionZeroReduced_product_2, zeroOneAlignedCorrectionZeroReduced_product_3, zeroOneAlignedCorrectionZeroReduced_product_4, zeroOneAlignedCorrectionZeroReduced_product_5, zeroOneAlignedCorrectionZeroReduced_product_6, zeroOneAlignedCorrectionZeroReduced_product_7, zeroOneAlignedCorrectionZeroReduced_product_8, zeroOneAlignedCorrectionZeroReduced_product_9, zeroOneAlignedCorrectionZeroReduced_product_10, zeroOneAlignedCorrectionZeroReduced_product_11, zeroOneAlignedCorrectionZeroReduced_product_12, zeroOneAlignedCorrectionZeroReduced_product_13, zeroOneAlignedCorrectionZeroReduced_product_14, zeroOneAlignedCorrectionZeroReduced_product_15]
  simp [zeroOneAlignedCorrectionZeroReducedProduct]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]
  all_goals ring

/-- The selected reduced equations generate the unit ideal. -/
theorem zeroOne_aligned_correctionZero_reduced_inconsistent
    (v : Fin 71 → F₂)
    (hzero : ∀ i : Fin 16, zeroOneAlignedCorrectionZeroReducedConstraint v i = 0) :
    False := by
  have hone : (1 : F₂) = 0 := by
    rw [zeroOneAlignedCorrectionZeroReduced_certificate v]
    simp [zeroOneAlignedCorrectionZeroReducedCombination, hzero]
  exact one_ne_zero hone

end
end UnrestrictedBooleanMul.N5
