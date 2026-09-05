import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawBase

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192

def zeroOneRInfRawMultiplier_10 (v : Fin 71 → F₂) : F₂ :=
  1 + v 45

def zeroOneRInfRawProduct_10 (v : Fin 71 → F₂) : F₂ :=
  v 9 * v 15 * v 43 + v 5 * v 19 * v 43 + v 9 * v 15 * v 43 * v 45 + v 5 * v 19 * v 43 * v 45 + v 9 * v 12 * v 46 + v 2 * v 19 * v 46 + v 9 * v 12 * v 45 * v 46 + v 2 * v 19 * v 45 * v 46 + v 5 * v 12 * v 50 + v 2 * v 15 * v 50 + v 5 * v 12 * v 45 * v 50 + v 2 * v 15 * v 45 * v 50 + v 46 * v 63 + v 45 * v 46 * v 63 + v 50 * v 63 + v 45 * v 50 * v 63 + v 50 * v 68 + v 45 * v 50 * v 68 + v 46 * v 69 + v 45 * v 46 * v 69 + v 19 * v 25 * v 43 * v 70 + v 15 * v 29 * v 43 * v 70 + v 9 * v 35 * v 43 * v 70 + v 29 * v 35 * v 43 * v 70 + v 5 * v 39 * v 43 * v 70 + v 25 * v 39 * v 43 * v 70 + v 19 * v 25 * v 43 * v 45 * v 70 + v 15 * v 29 * v 43 * v 45 * v 70 + v 9 * v 35 * v 43 * v 45 * v 70 + v 29 * v 35 * v 43 * v 45 * v 70 + v 5 * v 39 * v 43 * v 45 * v 70 + v 25 * v 39 * v 43 * v 45 * v 70 + v 19 * v 22 * v 46 * v 70 + v 12 * v 29 * v 46 * v 70 + v 9 * v 32 * v 46 * v 70 + v 29 * v 32 * v 46 * v 70 + v 2 * v 39 * v 46 * v 70 + v 22 * v 39 * v 46 * v 70 + v 19 * v 22 * v 45 * v 46 * v 70 + v 12 * v 29 * v 45 * v 46 * v 70 + v 9 * v 32 * v 45 * v 46 * v 70 + v 29 * v 32 * v 45 * v 46 * v 70 + v 2 * v 39 * v 45 * v 46 * v 70 + v 22 * v 39 * v 45 * v 46 * v 70 + v 15 * v 22 * v 50 * v 70 + v 12 * v 25 * v 50 * v 70 + v 5 * v 32 * v 50 * v 70 + v 25 * v 32 * v 50 * v 70 + v 2 * v 35 * v 50 * v 70 + v 22 * v 35 * v 50 * v 70 + v 15 * v 22 * v 45 * v 50 * v 70 + v 12 * v 25 * v 45 * v 50 * v 70 + v 5 * v 32 * v 45 * v 50 * v 70 + v 25 * v 32 * v 45 * v 50 * v 70 + v 2 * v 35 * v 45 * v 50 * v 70 + v 22 * v 35 * v 45 * v 50 * v 70

set_option maxHeartbeats 10000000 in
theorem zeroOneRInfRaw_product_10 (v : Fin 71 → F₂) :
    zeroOneRInfRawMultiplier_10 v * zeroOneRInfRawConstraint v 10 =
      zeroOneRInfRawProduct_10 v := by
  simp [zeroOneRInfRawMultiplier_10, zeroOneRInfRawConstraint,
    zeroOneRInfRawProduct_10, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, zeroOneRInfRaw_f2_mul_self]
  all_goals (try rw [zeroOneRInfRaw_f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [zeroOneRInfRaw_f2_two_eq_zero]

end
end UnrestrictedBooleanMul.N5
