import UnrestrictedBooleanMul.ANF

/-!
# Reduced aligned certificate: `OneOneAlignedCorrectionZero`

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

/-- The 13 reduced semantic generators in this unit certificate. -/
def oneOneAlignedCorrectionZeroReducedConstraint (v : Fin 71 → F₂) : Fin 13 → F₂ :=
  ![
    -- product-high-0x023
    v 1 * v 5 * v 10 + v 0 * v 1 * v 15 + v 1 * v 15 * v 41 + v 1 * v 10 * v 46 + v 53 + v 1 * v 62 + v 65 + v 41 * v 65,
    -- product-high-0x025
    v 2 * v 5 * v 10 + v 0 * v 2 * v 15 + v 2 * v 15 * v 41 + v 2 * v 10 * v 46 + v 54 + v 2 * v 62,
    -- product-high-0x043
    v 0 * v 1 + v 1 * v 6 * v 10 + v 1 * v 41 + v 1 * v 10 * v 47 + v 1 * v 65,
    -- product-high-0x061
    1 + v 0 + v 5 + v 6 * v 10 + v 6 * v 15 + v 40 + v 41 + v 5 * v 41 + v 6 * v 15 * v 41 + v 46 + v 0 * v 46 + v 6 * v 10 * v 46 + v 10 * v 47 + v 5 * v 10 * v 47 + v 15 * v 47 + v 0 * v 15 * v 47 + v 58 + v 47 * v 62 + v 65 + v 46 * v 65,
    -- product-high-0x062
    v 1 * v 5 + v 1 * v 6 * v 15 + v 1 * v 46 + v 1 * v 15 * v 47 + v 47 * v 65,
    -- product-high-0x0a1
    v 5 * v 7 * v 10 + v 0 * v 7 * v 15 + v 7 * v 15 * v 41 + v 7 * v 10 * v 46 + v 59 + v 7 * v 62,
    -- product-high-0x0a2
    v 7 * v 65,
    -- quotient-6
    v 2 * v 5 + v 0 * v 7 + v 7 * v 10 + v 0 * v 7 * v 10 + v 2 * v 15 + v 2 * v 5 * v 15 + v 7 * v 20 + v 2 * v 25 + v 7 * v 30 + v 2 * v 35 + v 7 * v 10 * v 40 + v 2 * v 15 * v 40 + v 7 * v 41 + v 7 * v 10 * v 41 + v 2 * v 46 + v 2 * v 15 * v 46 + v 7 * v 52 + v 46 * v 54 + v 2 * v 57 + v 41 * v 59,
    -- quotient-13
    1 + v 1 + v 2 * v 5 + v 2 * v 15 + v 2 * v 5 * v 15 + v 2 * v 25 + v 2 * v 35 + v 1 * v 40 + v 2 * v 15 * v 40 + v 2 * v 46 + v 2 * v 15 * v 46 + v 47 * v 53 + v 46 * v 54 + v 2 * v 57 + v 1 * v 58,
    -- quotient-14
    v 15 * v 23 + v 3 * v 25 + v 13 * v 25 + v 23 * v 25 + v 3 * v 35 + v 23 * v 35 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 5 * v 44 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 3 * v 46 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 7 * v 53 + v 46 * v 55 + v 44 * v 57 + v 1 * v 59,
    -- quotient-20
    v 2 + v 15 * v 23 + v 3 * v 25 + v 13 * v 25 + v 23 * v 25 + v 3 * v 35 + v 23 * v 35 + v 2 * v 40 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 5 * v 44 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 3 * v 46 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 47 * v 54 + v 46 * v 55 + v 44 * v 57 + v 2 * v 58,
    -- quotient-36
    v 5 * v 7 + v 7 * v 15 + v 5 * v 7 * v 15 + v 7 * v 25 + v 7 * v 35 + v 7 * v 15 * v 40 + v 7 * v 46 + v 7 * v 15 * v 46 + v 7 * v 57 + v 46 * v 59,
    -- quotient-39
    v 7 + v 7 * v 40 + v 7 * v 58 + v 47 * v 59
  ]

private def oneOneAlignedCorrectionZeroReducedMultiplier (v : Fin 71 → F₂) : Fin 13 → F₂ :=
  ![
    -- product-high-0x023
    v 7 * v 15 + v 47,
    -- product-high-0x025
    v 7 * v 46 + v 7 * v 15 * v 47,
    -- product-high-0x043
    1 + v 46,
    -- product-high-0x061
    v 1,
    -- product-high-0x062
    1 + v 41,
    -- product-high-0x0a1
    v 1 * v 7 * v 15 + v 41 + v 7 * v 41 + v 2 * v 46 + v 2 * v 15 * v 47,
    -- product-high-0x0a2
    v 15 + v 15 * v 41,
    -- quotient-6
    1 + v 7,
    -- quotient-13
    1,
    -- quotient-14
    v 7 * v 15,
    -- quotient-20
    v 7 * v 15,
    -- quotient-36
    v 2,
    -- quotient-39
    v 2 * v 15
  ]

private def oneOneAlignedCorrectionZeroReducedProduct (v : Fin 71 → F₂) : Fin 13 → F₂ :=
  ![
    -- product-high-0x023
    v 0 * v 1 * v 7 * v 15 + v 1 * v 5 * v 7 * v 10 * v 15 + v 1 * v 7 * v 15 * v 41 + v 1 * v 7 * v 10 * v 15 * v 46 + v 1 * v 5 * v 10 * v 47 + v 0 * v 1 * v 15 * v 47 + v 1 * v 15 * v 41 * v 47 + v 1 * v 10 * v 46 * v 47 + v 7 * v 15 * v 53 + v 47 * v 53 + v 1 * v 7 * v 15 * v 62 + v 1 * v 47 * v 62 + v 7 * v 15 * v 65 + v 7 * v 15 * v 41 * v 65 + v 47 * v 65 + v 41 * v 47 * v 65,
    -- product-high-0x025
    v 2 * v 7 * v 10 * v 46 + v 2 * v 5 * v 7 * v 10 * v 46 + v 0 * v 2 * v 7 * v 15 * v 46 + v 2 * v 7 * v 15 * v 41 * v 46 + v 0 * v 2 * v 7 * v 15 * v 47 + v 2 * v 5 * v 7 * v 10 * v 15 * v 47 + v 2 * v 7 * v 15 * v 41 * v 47 + v 2 * v 7 * v 10 * v 15 * v 46 * v 47 + v 7 * v 46 * v 54 + v 7 * v 15 * v 47 * v 54 + v 2 * v 7 * v 46 * v 62 + v 2 * v 7 * v 15 * v 47 * v 62,
    -- product-high-0x043
    v 0 * v 1 + v 1 * v 6 * v 10 + v 1 * v 41 + v 0 * v 1 * v 46 + v 1 * v 6 * v 10 * v 46 + v 1 * v 41 * v 46 + v 1 * v 10 * v 47 + v 1 * v 10 * v 46 * v 47 + v 1 * v 65 + v 1 * v 46 * v 65,
    -- product-high-0x061
    v 1 + v 0 * v 1 + v 1 * v 5 + v 1 * v 6 * v 10 + v 1 * v 6 * v 15 + v 1 * v 40 + v 1 * v 41 + v 1 * v 5 * v 41 + v 1 * v 6 * v 15 * v 41 + v 1 * v 46 + v 0 * v 1 * v 46 + v 1 * v 6 * v 10 * v 46 + v 1 * v 10 * v 47 + v 1 * v 5 * v 10 * v 47 + v 1 * v 15 * v 47 + v 0 * v 1 * v 15 * v 47 + v 1 * v 58 + v 1 * v 47 * v 62 + v 1 * v 65 + v 1 * v 46 * v 65,
    -- product-high-0x062
    v 1 * v 5 + v 1 * v 6 * v 15 + v 1 * v 5 * v 41 + v 1 * v 6 * v 15 * v 41 + v 1 * v 46 + v 1 * v 41 * v 46 + v 1 * v 15 * v 47 + v 1 * v 15 * v 41 * v 47 + v 47 * v 65 + v 41 * v 47 * v 65,
    -- product-high-0x0a1
    v 0 * v 1 * v 7 * v 15 + v 1 * v 5 * v 7 * v 10 * v 15 + v 1 * v 7 * v 15 * v 41 + v 2 * v 7 * v 10 * v 46 + v 2 * v 5 * v 7 * v 10 * v 46 + v 0 * v 2 * v 7 * v 15 * v 46 + v 1 * v 7 * v 10 * v 15 * v 46 + v 2 * v 7 * v 15 * v 41 * v 46 + v 0 * v 2 * v 7 * v 15 * v 47 + v 2 * v 5 * v 7 * v 10 * v 15 * v 47 + v 2 * v 7 * v 15 * v 41 * v 47 + v 2 * v 7 * v 10 * v 15 * v 46 * v 47 + v 1 * v 7 * v 15 * v 59 + v 41 * v 59 + v 7 * v 41 * v 59 + v 2 * v 46 * v 59 + v 2 * v 15 * v 47 * v 59 + v 1 * v 7 * v 15 * v 62 + v 2 * v 7 * v 46 * v 62 + v 2 * v 7 * v 15 * v 47 * v 62,
    -- product-high-0x0a2
    v 7 * v 15 * v 65 + v 7 * v 15 * v 41 * v 65,
    -- quotient-6
    v 2 * v 5 + v 2 * v 5 * v 7 + v 2 * v 15 + v 2 * v 5 * v 15 + v 2 * v 7 * v 15 + v 2 * v 5 * v 7 * v 15 + v 2 * v 25 + v 2 * v 7 * v 25 + v 2 * v 35 + v 2 * v 7 * v 35 + v 2 * v 15 * v 40 + v 2 * v 7 * v 15 * v 40 + v 2 * v 46 + v 2 * v 7 * v 46 + v 2 * v 15 * v 46 + v 2 * v 7 * v 15 * v 46 + v 46 * v 54 + v 7 * v 46 * v 54 + v 2 * v 57 + v 2 * v 7 * v 57 + v 41 * v 59 + v 7 * v 41 * v 59,
    -- quotient-13
    1 + v 1 + v 2 * v 5 + v 2 * v 15 + v 2 * v 5 * v 15 + v 2 * v 25 + v 2 * v 35 + v 1 * v 40 + v 2 * v 15 * v 40 + v 2 * v 46 + v 2 * v 15 * v 46 + v 47 * v 53 + v 46 * v 54 + v 2 * v 57 + v 1 * v 58,
    -- quotient-14
    v 7 * v 15 * v 23 + v 3 * v 7 * v 15 * v 25 + v 7 * v 13 * v 15 * v 25 + v 7 * v 15 * v 23 * v 25 + v 3 * v 7 * v 15 * v 35 + v 7 * v 15 * v 23 * v 35 + v 3 * v 7 * v 15 * v 40 + v 5 * v 7 * v 13 * v 15 * v 40 + v 3 * v 7 * v 15 * v 44 + v 5 * v 7 * v 13 * v 15 * v 44 + v 3 * v 7 * v 13 * v 15 * v 46 + v 5 * v 7 * v 13 * v 15 * v 46 + v 7 * v 15 * v 53 + v 7 * v 15 * v 46 * v 55 + v 7 * v 15 * v 44 * v 57 + v 1 * v 7 * v 15 * v 59,
    -- quotient-20
    v 2 * v 7 * v 15 + v 7 * v 15 * v 23 + v 3 * v 7 * v 15 * v 25 + v 7 * v 13 * v 15 * v 25 + v 7 * v 15 * v 23 * v 25 + v 3 * v 7 * v 15 * v 35 + v 7 * v 15 * v 23 * v 35 + v 2 * v 7 * v 15 * v 40 + v 3 * v 7 * v 15 * v 40 + v 5 * v 7 * v 13 * v 15 * v 40 + v 3 * v 7 * v 15 * v 44 + v 5 * v 7 * v 13 * v 15 * v 44 + v 3 * v 7 * v 13 * v 15 * v 46 + v 5 * v 7 * v 13 * v 15 * v 46 + v 7 * v 15 * v 47 * v 54 + v 7 * v 15 * v 46 * v 55 + v 7 * v 15 * v 44 * v 57 + v 2 * v 7 * v 15 * v 58,
    -- quotient-36
    v 2 * v 5 * v 7 + v 2 * v 7 * v 15 + v 2 * v 5 * v 7 * v 15 + v 2 * v 7 * v 25 + v 2 * v 7 * v 35 + v 2 * v 7 * v 15 * v 40 + v 2 * v 7 * v 46 + v 2 * v 7 * v 15 * v 46 + v 2 * v 7 * v 57 + v 2 * v 46 * v 59,
    -- quotient-39
    v 2 * v 7 * v 15 + v 2 * v 7 * v 15 * v 40 + v 2 * v 7 * v 15 * v 58 + v 2 * v 15 * v 47 * v 59
  ]

private def oneOneAlignedCorrectionZeroReducedCombination (v : Fin 71 → F₂) : F₂ :=
  oneOneAlignedCorrectionZeroReducedMultiplier v 0 * oneOneAlignedCorrectionZeroReducedConstraint v 0 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 1 * oneOneAlignedCorrectionZeroReducedConstraint v 1 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 2 * oneOneAlignedCorrectionZeroReducedConstraint v 2 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 3 * oneOneAlignedCorrectionZeroReducedConstraint v 3 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 4 * oneOneAlignedCorrectionZeroReducedConstraint v 4 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 5 * oneOneAlignedCorrectionZeroReducedConstraint v 5 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 6 * oneOneAlignedCorrectionZeroReducedConstraint v 6 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 7 * oneOneAlignedCorrectionZeroReducedConstraint v 7 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 8 * oneOneAlignedCorrectionZeroReducedConstraint v 8 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 9 * oneOneAlignedCorrectionZeroReducedConstraint v 9 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 10 * oneOneAlignedCorrectionZeroReducedConstraint v 10 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 11 * oneOneAlignedCorrectionZeroReducedConstraint v 11 +
  oneOneAlignedCorrectionZeroReducedMultiplier v 12 * oneOneAlignedCorrectionZeroReducedConstraint v 12

private theorem f2_mul_self (x : F₂) : x * x = x := by
  rcases f2_eq_zero_or_one x with h | h <;> simp [h]

private theorem f2_two_eq_zero : (2 : F₂) = 0 :=
  CharTwo.two_eq_zero

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_0 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 0 * oneOneAlignedCorrectionZeroReducedConstraint v 0 =
      oneOneAlignedCorrectionZeroReducedProduct v 0 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_1 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 1 * oneOneAlignedCorrectionZeroReducedConstraint v 1 =
      oneOneAlignedCorrectionZeroReducedProduct v 1 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_2 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 2 * oneOneAlignedCorrectionZeroReducedConstraint v 2 =
      oneOneAlignedCorrectionZeroReducedProduct v 2 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_3 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 3 * oneOneAlignedCorrectionZeroReducedConstraint v 3 =
      oneOneAlignedCorrectionZeroReducedProduct v 3 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_4 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 4 * oneOneAlignedCorrectionZeroReducedConstraint v 4 =
      oneOneAlignedCorrectionZeroReducedProduct v 4 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_5 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 5 * oneOneAlignedCorrectionZeroReducedConstraint v 5 =
      oneOneAlignedCorrectionZeroReducedProduct v 5 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_6 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 6 * oneOneAlignedCorrectionZeroReducedConstraint v 6 =
      oneOneAlignedCorrectionZeroReducedProduct v 6 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_7 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 7 * oneOneAlignedCorrectionZeroReducedConstraint v 7 =
      oneOneAlignedCorrectionZeroReducedProduct v 7 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_8 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 8 * oneOneAlignedCorrectionZeroReducedConstraint v 8 =
      oneOneAlignedCorrectionZeroReducedProduct v 8 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_9 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 9 * oneOneAlignedCorrectionZeroReducedConstraint v 9 =
      oneOneAlignedCorrectionZeroReducedProduct v 9 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_10 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 10 * oneOneAlignedCorrectionZeroReducedConstraint v 10 =
      oneOneAlignedCorrectionZeroReducedProduct v 10 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_11 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 11 * oneOneAlignedCorrectionZeroReducedConstraint v 11 =
      oneOneAlignedCorrectionZeroReducedProduct v 11 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionZeroReduced_product_12 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionZeroReducedMultiplier v 12 * oneOneAlignedCorrectionZeroReducedConstraint v 12 =
      oneOneAlignedCorrectionZeroReducedProduct v 12 := by
  simp [oneOneAlignedCorrectionZeroReducedMultiplier, oneOneAlignedCorrectionZeroReducedConstraint,
    oneOneAlignedCorrectionZeroReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionZeroReduced_certificate (v : Fin 71 → F₂) :
    (1 : F₂) = oneOneAlignedCorrectionZeroReducedCombination v := by
  unfold oneOneAlignedCorrectionZeroReducedCombination
  rw [oneOneAlignedCorrectionZeroReduced_product_0, oneOneAlignedCorrectionZeroReduced_product_1, oneOneAlignedCorrectionZeroReduced_product_2, oneOneAlignedCorrectionZeroReduced_product_3, oneOneAlignedCorrectionZeroReduced_product_4, oneOneAlignedCorrectionZeroReduced_product_5, oneOneAlignedCorrectionZeroReduced_product_6, oneOneAlignedCorrectionZeroReduced_product_7, oneOneAlignedCorrectionZeroReduced_product_8, oneOneAlignedCorrectionZeroReduced_product_9, oneOneAlignedCorrectionZeroReduced_product_10, oneOneAlignedCorrectionZeroReduced_product_11, oneOneAlignedCorrectionZeroReduced_product_12]
  simp [oneOneAlignedCorrectionZeroReducedProduct]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]
  all_goals ring

/-- The selected reduced equations generate the unit ideal. -/
theorem oneOne_aligned_correctionZero_reduced_inconsistent
    (v : Fin 71 → F₂)
    (hzero : ∀ i : Fin 13, oneOneAlignedCorrectionZeroReducedConstraint v i = 0) :
    False := by
  have hone : (1 : F₂) = 0 := by
    rw [oneOneAlignedCorrectionZeroReduced_certificate v]
    simp [oneOneAlignedCorrectionZeroReducedCombination, hzero]
  exact one_ne_zero hone

end
end UnrestrictedBooleanMul.N5
