import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawBase

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192

def zeroOneRInfRawMultiplier_13_part_0 (v : Fin 71 → F₂) : F₂ :=
  v 40 + v 43 + v 45 + v 46 + v 50 + v 5 * v 12 * v 33 + v 2 * v 5 * v 12 * v 33 + v 3 * v 5 * v 12 * v 33 + v 5 * v 7 * v 12 * v 33 + v 5 * v 8 * v 12 * v 33 + v 5 * v 12 * v 22 * v 33 + v 5 * v 12 * v 25 * v 33 + v 5 * v 12 * v 32 * v 33 + v 5 * v 13 * v 22 * v 32 + v 2 * v 3 * v 5 * v 12 * v 33 + v 2 * v 5 * v 7 * v 12 * v 33

def zeroOneRInfRawProduct_13_part_0 (v : Fin 71 → F₂) : F₂ :=
  v 40 * v 63 + v 40 * v 68 + v 43 * v 63 + v 43 * v 68 + v 45 * v 63 + v 45 * v 68 + v 46 * v 63 + v 46 * v 68 + v 50 * v 63 + v 50 * v 68 + v 2 * v 15 * v 40 + v 2 * v 15 * v 43 + v 2 * v 15 * v 45 + v 2 * v 15 * v 46 + v 2 * v 15 * v 50 + v 5 * v 12 * v 33 + v 5 * v 12 * v 40 + v 5 * v 12 * v 43 + v 5 * v 12 * v 45 + v 5 * v 12 * v 46 + v 5 * v 12 * v 50 + v 2 * v 5 * v 12 * v 33 + v 2 * v 35 * v 40 * v 70 + v 2 * v 35 * v 43 * v 70 + v 2 * v 35 * v 45 * v 70 + v 2 * v 35 * v 46 * v 70 + v 2 * v 35 * v 50 * v 70 + v 3 * v 5 * v 12 * v 33 + v 5 * v 7 * v 12 * v 33 + v 5 * v 8 * v 12 * v 33 + v 5 * v 12 * v 22 * v 33 + v 5 * v 12 * v 25 * v 33 + v 5 * v 12 * v 32 * v 33 + v 5 * v 12 * v 33 * v 63 + v 5 * v 12 * v 33 * v 68 + v 5 * v 32 * v 40 * v 70 + v 5 * v 32 * v 43 * v 70 + v 5 * v 32 * v 45 * v 70 + v 5 * v 32 * v 46 * v 70 + v 5 * v 32 * v 50 * v 70 + v 12 * v 25 * v 40 * v 70 + v 12 * v 25 * v 43 * v 70 + v 12 * v 25 * v 45 * v 70 + v 12 * v 25 * v 46 * v 70 + v 12 * v 25 * v 50 * v 70 + v 15 * v 22 * v 40 * v 70 + v 15 * v 22 * v 43 * v 70 + v 15 * v 22 * v 45 * v 70 + v 15 * v 22 * v 46 * v 70 + v 15 * v 22 * v 50 * v 70 + v 22 * v 35 * v 40 * v 70 + v 22 * v 35 * v 43 * v 70 + v 22 * v 35 * v 45 * v 70 + v 22 * v 35 * v 46 * v 70 + v 22 * v 35 * v 50 * v 70 + v 25 * v 32 * v 40 * v 70 + v 25 * v 32 * v 43 * v 70 + v 25 * v 32 * v 45 * v 70 + v 25 * v 32 * v 46 * v 70 + v 25 * v 32 * v 50 * v 70 + v 2 * v 3 * v 5 * v 12 * v 33 + v 2 * v 5 * v 7 * v 12 * v 33 + v 2 * v 5 * v 12 * v 33 * v 63 + v 2 * v 5 * v 12 * v 33 * v 68 + v 3 * v 5 * v 12 * v 33 * v 63 + v 3 * v 5 * v 12 * v 33 * v 68 + v 5 * v 7 * v 12 * v 33 * v 63 + v 5 * v 7 * v 12 * v 33 * v 68 + v 5 * v 8 * v 12 * v 33 * v 63 + v 5 * v 8 * v 12 * v 33 * v 68 + v 5 * v 12 * v 13 * v 22 * v 32 + v 5 * v 12 * v 22 * v 33 * v 63 + v 5 * v 12 * v 22 * v 33 * v 68 + v 5 * v 12 * v 25 * v 33 * v 63 + v 5 * v 12 * v 25 * v 33 * v 68 + v 5 * v 12 * v 32 * v 33 * v 63 + v 5 * v 12 * v 32 * v 33 * v 68 + v 5 * v 13 * v 22 * v 32 * v 63 + v 5 * v 13 * v 22 * v 32 * v 68 + v 5 * v 13 * v 22 * v 32 * v 70 + v 2 * v 3 * v 5 * v 12 * v 33 * v 63 + v 2 * v 3 * v 5 * v 12 * v 33 * v 68 + v 2 * v 5 * v 7 * v 12 * v 33 * v 63 + v 2 * v 5 * v 7 * v 12 * v 33 * v 68 + v 2 * v 5 * v 8 * v 12 * v 15 * v 33 + v 2 * v 5 * v 12 * v 15 * v 22 * v 33 + v 2 * v 5 * v 12 * v 15 * v 25 * v 33 + v 2 * v 5 * v 12 * v 15 * v 32 * v 33 + v 2 * v 5 * v 12 * v 25 * v 33 * v 70 + v 2 * v 5 * v 12 * v 32 * v 33 * v 70 + v 2 * v 5 * v 13 * v 15 * v 22 * v 32 + v 3 * v 5 * v 12 * v 25 * v 33 * v 70 + v 3 * v 5 * v 12 * v 32 * v 33 * v 70 + v 5 * v 7 * v 12 * v 25 * v 33 * v 70 + v 5 * v 7 * v 12 * v 32 * v 33 * v 70 + v 5 * v 8 * v 12 * v 25 * v 33 * v 70 + v 5 * v 8 * v 12 * v 32 * v 33 * v 70 + v 5 * v 12 * v 22 * v 25 * v 33 * v 70 + v 5 * v 12 * v 22 * v 32 * v 33 * v 70 + v 5 * v 12 * v 25 * v 32 * v 33 * v 70 + v 5 * v 13 * v 15 * v 22 * v 32 * v 70 + v 5 * v 13 * v 22 * v 25 * v 32 * v 70 + v 5 * v 13 * v 22 * v 32 * v 35 * v 70 + v 2 * v 3 * v 5 * v 12 * v 25 * v 33 * v 70 + v 2 * v 3 * v 5 * v 12 * v 32 * v 33 * v 70 + v 2 * v 5 * v 7 * v 12 * v 25 * v 33 * v 70 + v 2 * v 5 * v 7 * v 12 * v 32 * v 33 * v 70 + v 2 * v 5 * v 8 * v 12 * v 33 * v 35 * v 70 + v 2 * v 5 * v 12 * v 15 * v 22 * v 33 * v 70 + v 2 * v 5 * v 12 * v 25 * v 32 * v 33 * v 70 + v 2 * v 5 * v 12 * v 25 * v 33 * v 35 * v 70 + v 2 * v 5 * v 12 * v 32 * v 33 * v 35 * v 70 + v 2 * v 5 * v 13 * v 22 * v 32 * v 35 * v 70 + v 3 * v 5 * v 12 * v 15 * v 22 * v 33 * v 70 + v 3 * v 5 * v 12 * v 22 * v 33 * v 35 * v 70 + v 3 * v 5 * v 12 * v 25 * v 32 * v 33 * v 70 + v 5 * v 7 * v 12 * v 15 * v 22 * v 33 * v 70 + v 5 * v 7 * v 12 * v 22 * v 33 * v 35 * v 70 + v 5 * v 7 * v 12 * v 25 * v 32 * v 33 * v 70 + v 5 * v 8 * v 12 * v 15 * v 22 * v 33 * v 70 + v 5 * v 8 * v 12 * v 22 * v 33 * v 35 * v 70 + v 5 * v 8 * v 12 * v 25 * v 32 * v 33 * v 70 + v 5 * v 12 * v 13 * v 22 * v 25 * v 32 * v 70 + v 5 * v 12 * v 15 * v 22 * v 25 * v 33 * v 70 + v 5 * v 12 * v 15 * v 22 * v 32 * v 33 * v 70 + v 5 * v 12 * v 22 * v 25 * v 32 * v 33 * v 70 + v 5 * v 12 * v 22 * v 25 * v 33 * v 35 * v 70 + v 5 * v 12 * v 22 * v 32 * v 33 * v 35 * v 70 + v 2 * v 3 * v 5 * v 12 * v 15 * v 22 * v 33 * v 70 + v 2 * v 3 * v 5 * v 12 * v 22 * v 33 * v 35 * v 70 + v 2 * v 3 * v 5 * v 12 * v 25 * v 32 * v 33 * v 70 + v 2 * v 5 * v 7 * v 12 * v 15 * v 22 * v 33 * v 70 + v 2 * v 5 * v 7 * v 12 * v 22 * v 33 * v 35 * v 70 + v 2 * v 5 * v 7 * v 12 * v 25 * v 32 * v 33 * v 70

set_option maxHeartbeats 3000000 in
theorem zeroOneRInfRaw_product_13_part_0 (v : Fin 71 → F₂) :
    zeroOneRInfRawMultiplier_13_part_0 v * zeroOneRInfRawConstraint v 13 =
      zeroOneRInfRawProduct_13_part_0 v := by
  simp [zeroOneRInfRawMultiplier_13_part_0, zeroOneRInfRawConstraint, zeroOneRInfRawProduct_13_part_0, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, zeroOneRInfRaw_f2_mul_self]
  all_goals (try rw [zeroOneRInfRaw_f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [zeroOneRInfRaw_f2_two_eq_zero, CharTwo.ofNat_eq_mod]

end
end UnrestrictedBooleanMul.N5
