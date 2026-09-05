import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts0
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts1
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts3
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts4
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts5
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts6
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts7
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts8
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts9

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192

private def zeroOneRInfRawCombination (v : Fin 71 → F₂) : F₂ :=
  zeroOneRInfRawMultiplier_0 v * zeroOneRInfRawConstraint v 0 +
  zeroOneRInfRawMultiplier_1 v * zeroOneRInfRawConstraint v 1 +
  zeroOneRInfRawMultiplier_2 v * zeroOneRInfRawConstraint v 2 +
  zeroOneRInfRawMultiplier_3 v * zeroOneRInfRawConstraint v 3 +
  zeroOneRInfRawMultiplier_4 v * zeroOneRInfRawConstraint v 4 +
  zeroOneRInfRawMultiplier_5 v * zeroOneRInfRawConstraint v 5 +
  zeroOneRInfRawMultiplier_6 v * zeroOneRInfRawConstraint v 6 +
  zeroOneRInfRawMultiplier_7 v * zeroOneRInfRawConstraint v 7 +
  zeroOneRInfRawMultiplier_8 v * zeroOneRInfRawConstraint v 8 +
  zeroOneRInfRawMultiplier_9 v * zeroOneRInfRawConstraint v 9 +
  zeroOneRInfRawMultiplier_10 v * zeroOneRInfRawConstraint v 10 +
  zeroOneRInfRawMultiplier_11 v * zeroOneRInfRawConstraint v 11 +
  zeroOneRInfRawMultiplier_12 v * zeroOneRInfRawConstraint v 12 +
  zeroOneRInfRawMultiplier_13 v * zeroOneRInfRawConstraint v 13 +
  zeroOneRInfRawMultiplier_14 v * zeroOneRInfRawConstraint v 14 +
  zeroOneRInfRawMultiplier_15 v * zeroOneRInfRawConstraint v 15 +
  zeroOneRInfRawMultiplier_16 v * zeroOneRInfRawConstraint v 16 +
  zeroOneRInfRawMultiplier_17 v * zeroOneRInfRawConstraint v 17 +
  zeroOneRInfRawMultiplier_18 v * zeroOneRInfRawConstraint v 18 +
  zeroOneRInfRawMultiplier_19 v * zeroOneRInfRawConstraint v 19 +
  zeroOneRInfRawMultiplier_20 v * zeroOneRInfRawConstraint v 20 +
  zeroOneRInfRawMultiplier_21 v * zeroOneRInfRawConstraint v 21 +
  zeroOneRInfRawMultiplier_22 v * zeroOneRInfRawConstraint v 22 +
  zeroOneRInfRawMultiplier_23 v * zeroOneRInfRawConstraint v 23 +
  zeroOneRInfRawMultiplier_24 v * zeroOneRInfRawConstraint v 24 +
  zeroOneRInfRawMultiplier_25 v * zeroOneRInfRawConstraint v 25 +
  zeroOneRInfRawMultiplier_26 v * zeroOneRInfRawConstraint v 26 +
  zeroOneRInfRawMultiplier_27 v * zeroOneRInfRawConstraint v 27 +
  zeroOneRInfRawMultiplier_28 v * zeroOneRInfRawConstraint v 28 +
  zeroOneRInfRawMultiplier_29 v * zeroOneRInfRawConstraint v 29 +
  zeroOneRInfRawMultiplier_30 v * zeroOneRInfRawConstraint v 30 +
  zeroOneRInfRawMultiplier_31 v * zeroOneRInfRawConstraint v 31 +
  zeroOneRInfRawMultiplier_32 v * zeroOneRInfRawConstraint v 32 +
  zeroOneRInfRawMultiplier_33 v * zeroOneRInfRawConstraint v 33 +
  zeroOneRInfRawMultiplier_34 v * zeroOneRInfRawConstraint v 34 +
  zeroOneRInfRawMultiplier_35 v * zeroOneRInfRawConstraint v 35 +
  zeroOneRInfRawMultiplier_36 v * zeroOneRInfRawConstraint v 36 +
  zeroOneRInfRawMultiplier_37 v * zeroOneRInfRawConstraint v 37 +
  zeroOneRInfRawMultiplier_38 v * zeroOneRInfRawConstraint v 38 +
  zeroOneRInfRawMultiplier_39 v * zeroOneRInfRawConstraint v 39 +
  zeroOneRInfRawMultiplier_40 v * zeroOneRInfRawConstraint v 40 +
  zeroOneRInfRawMultiplier_41 v * zeroOneRInfRawConstraint v 41 +
  zeroOneRInfRawMultiplier_42 v * zeroOneRInfRawConstraint v 42 +
  zeroOneRInfRawMultiplier_43 v * zeroOneRInfRawConstraint v 43 +
  zeroOneRInfRawMultiplier_44 v * zeroOneRInfRawConstraint v 44 +
  zeroOneRInfRawMultiplier_45 v * zeroOneRInfRawConstraint v 45 +
  zeroOneRInfRawMultiplier_46 v * zeroOneRInfRawConstraint v 46 +
  zeroOneRInfRawMultiplier_47 v * zeroOneRInfRawConstraint v 47 +
  zeroOneRInfRawMultiplier_48 v * zeroOneRInfRawConstraint v 48 +
  zeroOneRInfRawMultiplier_49 v * zeroOneRInfRawConstraint v 49

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneRInfRaw_certificate (v : Fin 71 → F₂) :
    zeroOneRInfRawTarget v = zeroOneRInfRawCombination v := by
  unfold zeroOneRInfRawCombination
  rw [zeroOneRInfRaw_product_0, zeroOneRInfRaw_product_1, zeroOneRInfRaw_product_2, zeroOneRInfRaw_product_3, zeroOneRInfRaw_product_4, zeroOneRInfRaw_product_5, zeroOneRInfRaw_product_6, zeroOneRInfRaw_product_7, zeroOneRInfRaw_product_8, zeroOneRInfRaw_product_9, zeroOneRInfRaw_product_10, zeroOneRInfRaw_product_11, zeroOneRInfRaw_product_12, zeroOneRInfRaw_product_13, zeroOneRInfRaw_product_14, zeroOneRInfRaw_product_15, zeroOneRInfRaw_product_16, zeroOneRInfRaw_product_17, zeroOneRInfRaw_product_18, zeroOneRInfRaw_product_19, zeroOneRInfRaw_product_20, zeroOneRInfRaw_product_21, zeroOneRInfRaw_product_22, zeroOneRInfRaw_product_23, zeroOneRInfRaw_product_24, zeroOneRInfRaw_product_25, zeroOneRInfRaw_product_26, zeroOneRInfRaw_product_27, zeroOneRInfRaw_product_28, zeroOneRInfRaw_product_29, zeroOneRInfRaw_product_30, zeroOneRInfRaw_product_31, zeroOneRInfRaw_product_32, zeroOneRInfRaw_product_33, zeroOneRInfRaw_product_34, zeroOneRInfRaw_product_35, zeroOneRInfRaw_product_36, zeroOneRInfRaw_product_37, zeroOneRInfRaw_product_38, zeroOneRInfRaw_product_39, zeroOneRInfRaw_product_40, zeroOneRInfRaw_product_41, zeroOneRInfRaw_product_42, zeroOneRInfRaw_product_43, zeroOneRInfRaw_product_44, zeroOneRInfRaw_product_45, zeroOneRInfRaw_product_46, zeroOneRInfRaw_product_47, zeroOneRInfRaw_product_48, zeroOneRInfRaw_product_49]
  simp [zeroOneRInfRawTarget, zeroOneRInfRawProduct_0, zeroOneRInfRawProduct_1, zeroOneRInfRawProduct_2, zeroOneRInfRawProduct_3, zeroOneRInfRawProduct_4, zeroOneRInfRawProduct_5, zeroOneRInfRawProduct_6, zeroOneRInfRawProduct_7, zeroOneRInfRawProduct_8, zeroOneRInfRawProduct_9, zeroOneRInfRawProduct_10, zeroOneRInfRawProduct_11, zeroOneRInfRawProduct_12, zeroOneRInfRawProduct_13, zeroOneRInfRawProduct_14, zeroOneRInfRawProduct_15, zeroOneRInfRawProduct_16, zeroOneRInfRawProduct_17, zeroOneRInfRawProduct_18, zeroOneRInfRawProduct_19, zeroOneRInfRawProduct_20, zeroOneRInfRawProduct_21, zeroOneRInfRawProduct_22, zeroOneRInfRawProduct_23, zeroOneRInfRawProduct_24, zeroOneRInfRawProduct_25, zeroOneRInfRawProduct_26, zeroOneRInfRawProduct_27, zeroOneRInfRawProduct_28, zeroOneRInfRawProduct_29, zeroOneRInfRawProduct_30, zeroOneRInfRawProduct_31, zeroOneRInfRawProduct_32, zeroOneRInfRawProduct_33, zeroOneRInfRawProduct_34, zeroOneRInfRawProduct_35, zeroOneRInfRawProduct_36, zeroOneRInfRawProduct_37, zeroOneRInfRawProduct_38, zeroOneRInfRawProduct_39, zeroOneRInfRawProduct_40, zeroOneRInfRawProduct_41, zeroOneRInfRawProduct_42, zeroOneRInfRawProduct_43, zeroOneRInfRawProduct_44, zeroOneRInfRawProduct_45, zeroOneRInfRawProduct_46, zeroOneRInfRawProduct_47, zeroOneRInfRawProduct_48, zeroOneRInfRawProduct_49] <;>
    ring_nf <;>
    simp [CharTwo.ofNat_eq_mod] <;>
    ring

set_option maxRecDepth 8192 in
theorem zeroOne_RInf_Raw_history_missing_eq_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i : Fin 50, zeroOneRInfRawConstraint v i = 0) :
    zeroOneRInfRawTarget v = 0 := by
  rw [zeroOneRInfRaw_certificate v]
  simp [zeroOneRInfRawCombination, hzero]

end
end UnrestrictedBooleanMul.N5
