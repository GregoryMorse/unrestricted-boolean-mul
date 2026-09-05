import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawBase
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part0
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part1
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part2
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part3
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part4
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part5
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part6
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part7
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part8
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part9
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part10
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part11
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part12
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part13
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part14
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part15
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRawProducts2Product13Part16

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192

def zeroOneRInfRawMultiplier_13 (v : Fin 71 → F₂) : F₂ :=
  zeroOneRInfRawMultiplier_13_part_0 v +
  zeroOneRInfRawMultiplier_13_part_1 v +
  zeroOneRInfRawMultiplier_13_part_2 v +
  zeroOneRInfRawMultiplier_13_part_3 v +
  zeroOneRInfRawMultiplier_13_part_4 v +
  zeroOneRInfRawMultiplier_13_part_5 v +
  zeroOneRInfRawMultiplier_13_part_6 v +
  zeroOneRInfRawMultiplier_13_part_7 v +
  zeroOneRInfRawMultiplier_13_part_8 v +
  zeroOneRInfRawMultiplier_13_part_9 v +
  zeroOneRInfRawMultiplier_13_part_10 v +
  zeroOneRInfRawMultiplier_13_part_11 v +
  zeroOneRInfRawMultiplier_13_part_12 v +
  zeroOneRInfRawMultiplier_13_part_13 v +
  zeroOneRInfRawMultiplier_13_part_14 v +
  zeroOneRInfRawMultiplier_13_part_15 v +
  zeroOneRInfRawMultiplier_13_part_16 v

def zeroOneRInfRawProduct_13 (v : Fin 71 → F₂) : F₂ :=
  zeroOneRInfRawProduct_13_part_0 v +
  zeroOneRInfRawProduct_13_part_1 v +
  zeroOneRInfRawProduct_13_part_2 v +
  zeroOneRInfRawProduct_13_part_3 v +
  zeroOneRInfRawProduct_13_part_4 v +
  zeroOneRInfRawProduct_13_part_5 v +
  zeroOneRInfRawProduct_13_part_6 v +
  zeroOneRInfRawProduct_13_part_7 v +
  zeroOneRInfRawProduct_13_part_8 v +
  zeroOneRInfRawProduct_13_part_9 v +
  zeroOneRInfRawProduct_13_part_10 v +
  zeroOneRInfRawProduct_13_part_11 v +
  zeroOneRInfRawProduct_13_part_12 v +
  zeroOneRInfRawProduct_13_part_13 v +
  zeroOneRInfRawProduct_13_part_14 v +
  zeroOneRInfRawProduct_13_part_15 v +
  zeroOneRInfRawProduct_13_part_16 v

set_option maxHeartbeats 3000000 in
theorem zeroOneRInfRaw_product_13 (v : Fin 71 → F₂) :
    zeroOneRInfRawMultiplier_13 v * zeroOneRInfRawConstraint v 13 =
      zeroOneRInfRawProduct_13 v := by
  have hpart_0 := zeroOneRInfRaw_product_13_part_0 v
  have hpart_1 := zeroOneRInfRaw_product_13_part_1 v
  have hpart_2 := zeroOneRInfRaw_product_13_part_2 v
  have hpart_3 := zeroOneRInfRaw_product_13_part_3 v
  have hpart_4 := zeroOneRInfRaw_product_13_part_4 v
  have hpart_5 := zeroOneRInfRaw_product_13_part_5 v
  have hpart_6 := zeroOneRInfRaw_product_13_part_6 v
  have hpart_7 := zeroOneRInfRaw_product_13_part_7 v
  have hpart_8 := zeroOneRInfRaw_product_13_part_8 v
  have hpart_9 := zeroOneRInfRaw_product_13_part_9 v
  have hpart_10 := zeroOneRInfRaw_product_13_part_10 v
  have hpart_11 := zeroOneRInfRaw_product_13_part_11 v
  have hpart_12 := zeroOneRInfRaw_product_13_part_12 v
  have hpart_13 := zeroOneRInfRaw_product_13_part_13 v
  have hpart_14 := zeroOneRInfRaw_product_13_part_14 v
  have hpart_15 := zeroOneRInfRaw_product_13_part_15 v
  have hpart_16 := zeroOneRInfRaw_product_13_part_16 v
  have hsum_0 :
      zeroOneRInfRawMultiplier_13_part_0 v * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v := hpart_0
  have hsum_1 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v := by
    rw [add_mul, hsum_0, hpart_1]
  have hsum_2 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v := by
    rw [add_mul, hsum_1, hpart_2]
  have hsum_3 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v := by
    rw [add_mul, hsum_2, hpart_3]
  have hsum_4 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v := by
    rw [add_mul, hsum_3, hpart_4]
  have hsum_5 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v := by
    rw [add_mul, hsum_4, hpart_5]
  have hsum_6 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v := by
    rw [add_mul, hsum_5, hpart_6]
  have hsum_7 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v := by
    rw [add_mul, hsum_6, hpart_7]
  have hsum_8 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v := by
    rw [add_mul, hsum_7, hpart_8]
  have hsum_9 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v + zeroOneRInfRawMultiplier_13_part_9 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v + zeroOneRInfRawProduct_13_part_9 v := by
    rw [add_mul, hsum_8, hpart_9]
  have hsum_10 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v + zeroOneRInfRawMultiplier_13_part_9 v + zeroOneRInfRawMultiplier_13_part_10 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v + zeroOneRInfRawProduct_13_part_9 v + zeroOneRInfRawProduct_13_part_10 v := by
    rw [add_mul, hsum_9, hpart_10]
  have hsum_11 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v + zeroOneRInfRawMultiplier_13_part_9 v + zeroOneRInfRawMultiplier_13_part_10 v + zeroOneRInfRawMultiplier_13_part_11 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v + zeroOneRInfRawProduct_13_part_9 v + zeroOneRInfRawProduct_13_part_10 v + zeroOneRInfRawProduct_13_part_11 v := by
    rw [add_mul, hsum_10, hpart_11]
  have hsum_12 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v + zeroOneRInfRawMultiplier_13_part_9 v + zeroOneRInfRawMultiplier_13_part_10 v + zeroOneRInfRawMultiplier_13_part_11 v + zeroOneRInfRawMultiplier_13_part_12 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v + zeroOneRInfRawProduct_13_part_9 v + zeroOneRInfRawProduct_13_part_10 v + zeroOneRInfRawProduct_13_part_11 v + zeroOneRInfRawProduct_13_part_12 v := by
    rw [add_mul, hsum_11, hpart_12]
  have hsum_13 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v + zeroOneRInfRawMultiplier_13_part_9 v + zeroOneRInfRawMultiplier_13_part_10 v + zeroOneRInfRawMultiplier_13_part_11 v + zeroOneRInfRawMultiplier_13_part_12 v + zeroOneRInfRawMultiplier_13_part_13 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v + zeroOneRInfRawProduct_13_part_9 v + zeroOneRInfRawProduct_13_part_10 v + zeroOneRInfRawProduct_13_part_11 v + zeroOneRInfRawProduct_13_part_12 v + zeroOneRInfRawProduct_13_part_13 v := by
    rw [add_mul, hsum_12, hpart_13]
  have hsum_14 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v + zeroOneRInfRawMultiplier_13_part_9 v + zeroOneRInfRawMultiplier_13_part_10 v + zeroOneRInfRawMultiplier_13_part_11 v + zeroOneRInfRawMultiplier_13_part_12 v + zeroOneRInfRawMultiplier_13_part_13 v + zeroOneRInfRawMultiplier_13_part_14 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v + zeroOneRInfRawProduct_13_part_9 v + zeroOneRInfRawProduct_13_part_10 v + zeroOneRInfRawProduct_13_part_11 v + zeroOneRInfRawProduct_13_part_12 v + zeroOneRInfRawProduct_13_part_13 v + zeroOneRInfRawProduct_13_part_14 v := by
    rw [add_mul, hsum_13, hpart_14]
  have hsum_15 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v + zeroOneRInfRawMultiplier_13_part_9 v + zeroOneRInfRawMultiplier_13_part_10 v + zeroOneRInfRawMultiplier_13_part_11 v + zeroOneRInfRawMultiplier_13_part_12 v + zeroOneRInfRawMultiplier_13_part_13 v + zeroOneRInfRawMultiplier_13_part_14 v + zeroOneRInfRawMultiplier_13_part_15 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v + zeroOneRInfRawProduct_13_part_9 v + zeroOneRInfRawProduct_13_part_10 v + zeroOneRInfRawProduct_13_part_11 v + zeroOneRInfRawProduct_13_part_12 v + zeroOneRInfRawProduct_13_part_13 v + zeroOneRInfRawProduct_13_part_14 v + zeroOneRInfRawProduct_13_part_15 v := by
    rw [add_mul, hsum_14, hpart_15]
  have hsum_16 :
      (zeroOneRInfRawMultiplier_13_part_0 v + zeroOneRInfRawMultiplier_13_part_1 v + zeroOneRInfRawMultiplier_13_part_2 v + zeroOneRInfRawMultiplier_13_part_3 v + zeroOneRInfRawMultiplier_13_part_4 v + zeroOneRInfRawMultiplier_13_part_5 v + zeroOneRInfRawMultiplier_13_part_6 v + zeroOneRInfRawMultiplier_13_part_7 v + zeroOneRInfRawMultiplier_13_part_8 v + zeroOneRInfRawMultiplier_13_part_9 v + zeroOneRInfRawMultiplier_13_part_10 v + zeroOneRInfRawMultiplier_13_part_11 v + zeroOneRInfRawMultiplier_13_part_12 v + zeroOneRInfRawMultiplier_13_part_13 v + zeroOneRInfRawMultiplier_13_part_14 v + zeroOneRInfRawMultiplier_13_part_15 v + zeroOneRInfRawMultiplier_13_part_16 v) * zeroOneRInfRawConstraint v 13 =
        zeroOneRInfRawProduct_13_part_0 v + zeroOneRInfRawProduct_13_part_1 v + zeroOneRInfRawProduct_13_part_2 v + zeroOneRInfRawProduct_13_part_3 v + zeroOneRInfRawProduct_13_part_4 v + zeroOneRInfRawProduct_13_part_5 v + zeroOneRInfRawProduct_13_part_6 v + zeroOneRInfRawProduct_13_part_7 v + zeroOneRInfRawProduct_13_part_8 v + zeroOneRInfRawProduct_13_part_9 v + zeroOneRInfRawProduct_13_part_10 v + zeroOneRInfRawProduct_13_part_11 v + zeroOneRInfRawProduct_13_part_12 v + zeroOneRInfRawProduct_13_part_13 v + zeroOneRInfRawProduct_13_part_14 v + zeroOneRInfRawProduct_13_part_15 v + zeroOneRInfRawProduct_13_part_16 v := by
    rw [add_mul, hsum_15, hpart_16]
  unfold zeroOneRInfRawMultiplier_13 zeroOneRInfRawProduct_13
  exact hsum_16

end
end UnrestrictedBooleanMul.N5
