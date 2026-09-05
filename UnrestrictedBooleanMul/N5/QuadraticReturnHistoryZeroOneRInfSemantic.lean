import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneRInfRaw

/-!
# Semantic bridge for the `ZeroOneRInf` return-history certificate

This generated module relates every raw Boolean-polynomial generator to a
literal ANF coefficient or to a genuine target-quotient row.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem zeroOneRInfRawTarget_eq_missingCoordinate
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawTarget p.vector =
      returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [returnHistoryMissingCoordinate, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetZeroSeven : ({0, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {7}, {0, 7}} := by decide
  have hpowersetZeroEight : ({0, 8} : Finset (Fin 10)).powerset =
      {∅, {0}, {8}, {0, 8}} := by decide
  have hpowersetOneNine : ({1, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {9}, {1, 9}} := by decide
  have hpowersetTwoNine : ({2, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {9}, {2, 9}} := by decide
  rw [hpowersetZeroSeven, hpowersetZeroEight, hpowersetOneNine,
    hpowersetTwoNine]
  simp (config := { decide := true }) [zeroOneRInfRawTarget]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_0_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 0 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_1_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 1 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 3, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 3, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {3}, {0, 3}, {5}, {0, 5}, {3, 5}, {0, 3, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_2_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 2 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {7}, {0, 7}, {5, 7}, {0, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_3_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 3 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 5, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 8} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {8}, {0, 8}, {5, 8}, {0, 5, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_4_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 4 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 4, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 5} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {5}, {2, 5}, {4, 5}, {2, 4, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_5_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 5 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 4, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 5} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {5}, {3, 5}, {4, 5}, {3, 4, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_6_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 6 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 4, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 7} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {7}, {3, 7}, {4, 7}, {3, 4, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_7_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 7 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 4, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 8} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {8}, {3, 8}, {4, 8}, {3, 4, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_8_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 8 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {9}, {2, 9}, {4, 9}, {2, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_9_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 9 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {9}, {3, 9}, {4, 9}, {3, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_10_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 10 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {5}, {2, 5}, {9}, {2, 9}, {5, 9}, {2, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_11_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 11 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {5}, {3, 5}, {9}, {3, 9}, {5, 9}, {3, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_12_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 12 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}, {9}, {4, 9}, {5, 9}, {4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_13_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 13 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {5}, {2, 5}, {4, 5}, {2, 4, 5}, {9}, {2, 9}, {4, 9}, {2, 4, 9}, {5, 9}, {2, 5, 9}, {4, 5, 9}, {2, 4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_14_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 14 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {5}, {3, 5}, {4, 5}, {3, 4, 5}, {9}, {3, 9}, {4, 9}, {3, 4, 9}, {5, 9}, {3, 5, 9}, {4, 5, 9}, {3, 4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_15_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 15 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {7}, {3, 7}, {9}, {3, 9}, {7, 9}, {3, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_16_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 16 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({4, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {7}, {4, 7}, {9}, {4, 9}, {7, 9}, {4, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_17_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 17 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 4, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {7}, {3, 7}, {4, 7}, {3, 4, 7}, {9}, {3, 9}, {4, 9}, {3, 4, 9}, {7, 9}, {3, 7, 9}, {4, 7, 9}, {3, 4, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_18_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 18 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {8}, {3, 8}, {9}, {3, 9}, {8, 9}, {3, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_19_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 19 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({4, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {8}, {4, 8}, {9}, {4, 9}, {8, 9}, {4, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_20_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 20 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 4, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {8}, {3, 8}, {4, 8}, {3, 4, 8}, {9}, {3, 9}, {4, 9}, {3, 4, 9}, {8, 9}, {3, 8, 9}, {4, 8, 9}, {3, 4, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_21_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 21 =
      mixedReturnQuotientCoordinate 0
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 0
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({0, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {7}, {0, 7}} := by decide
  have hpowersetSecond : ({2, 5} : Finset (Fin 10)).powerset =
      {∅, {2}, {5}, {2, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_22_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 22 =
      mixedReturnQuotientCoordinate 1
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 1
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({0, 8} : Finset (Fin 10)).powerset =
      {∅, {0}, {8}, {0, 8}} := by decide
  have hpowersetSecond : ({3, 5} : Finset (Fin 10)).powerset =
      {∅, {3}, {5}, {3, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_23_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 23 =
      mixedReturnQuotientCoordinate 4
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 4
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({1, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {9}, {1, 9}} := by decide
  have hpowersetSecond : ({4, 6} : Finset (Fin 10)).powerset =
      {∅, {4}, {6}, {4, 6}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_24_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 24 =
      mixedReturnQuotientCoordinate 8
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 8
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({2, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {9}, {2, 9}} := by decide
  have hpowersetSecond : ({4, 7} : Finset (Fin 10)).powerset =
      {∅, {4}, {7}, {4, 7}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_25_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 25 =
      mixedReturnQuotientCoordinate 11
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 11
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({3, 7} : Finset (Fin 10)).powerset =
      {∅, {3}, {7}, {3, 7}} := by decide
  have hpowersetSecond : ({4, 6} : Finset (Fin 10)).powerset =
      {∅, {4}, {6}, {4, 6}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_26_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 26 =
      mixedReturnQuotientCoordinate 10
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 10
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({3, 8} : Finset (Fin 10)).powerset =
      {∅, {3}, {8}, {3, 8}} := by decide
  have hpowersetSecond : ({4, 7} : Finset (Fin 10)).powerset =
      {∅, {4}, {7}, {4, 7}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_27_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 27 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 4, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 6} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {6}, {2, 6}, {4, 6}, {2, 4, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_28_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 28 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {6}, {2, 6}, {9}, {2, 9}, {6, 9}, {2, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_29_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 29 =
      mixedReturnQuotientCoordinate 5
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 5
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({2, 6} : Finset (Fin 10)).powerset =
      {∅, {2}, {6}, {2, 6}} := by decide
  have hpowersetSecond : ({3, 5} : Finset (Fin 10)).powerset =
      {∅, {3}, {5}, {3, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_30_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 30 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {6}, {4, 6}, {9}, {4, 9}, {6, 9}, {4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_31_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 31 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {6}, {2, 6}, {4, 6}, {2, 4, 6}, {9}, {2, 9}, {4, 9}, {2, 4, 9}, {6, 9}, {2, 6, 9}, {4, 6, 9}, {2, 4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_32_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 32 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({0, 4, 5, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {6}, {0, 6}, {4, 6}, {0, 4, 6}, {5, 6}, {0, 5, 6}, {4, 5, 6}, {0, 4, 5, 6}, {9}, {0, 9}, {4, 9}, {0, 4, 9}, {5, 9}, {0, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {6, 9}, {0, 6, 9}, {4, 6, 9}, {0, 4, 6, 9}, {5, 6, 9}, {0, 5, 6, 9}, {4, 5, 6, 9}, {0, 4, 5, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_33_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 33 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_34_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 34 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({0, 4, 5, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {8}, {0, 8}, {4, 8}, {0, 4, 8}, {5, 8}, {0, 5, 8}, {4, 5, 8}, {0, 4, 5, 8}, {9}, {0, 9}, {4, 9}, {0, 4, 9}, {5, 9}, {0, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {8, 9}, {0, 8, 9}, {4, 8, 9}, {0, 4, 8, 9}, {5, 8, 9}, {0, 5, 8, 9}, {4, 5, 8, 9}, {0, 4, 5, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_35_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 35 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({0, 4, 5, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {7}, {0, 7}, {4, 7}, {0, 4, 7}, {5, 7}, {0, 5, 7}, {4, 5, 7}, {0, 4, 5, 7}, {9}, {0, 9}, {4, 9}, {0, 4, 9}, {5, 9}, {0, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {7, 9}, {0, 7, 9}, {4, 7, 9}, {0, 4, 7, 9}, {5, 7, 9}, {0, 5, 7, 9}, {4, 5, 7, 9}, {0, 4, 5, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_36_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 36 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({4, 5, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 5, 8} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}, {8}, {4, 8}, {5, 8}, {4, 5, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_37_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 37 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({5, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({5, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {5}, {8}, {5, 8}, {9}, {5, 9}, {8, 9}, {5, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_38_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 38 =
      alignedReturnQuotientCoordinate 2
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        alignedReturnQuotientCoordinate 2
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [alignedReturnQuotientCoordinate, alignedReturnQuotientPair,
    quadraticProjection, quadraticPair, aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({5, 8} : Finset (Fin 10)).powerset =
      {∅, {5}, {8}, {5, 8}} := by decide
  rw [hpowersetFirst]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_39_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 39 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({4, 5, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 5, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}, {8}, {4, 8}, {5, 8}, {4, 5, 8}, {9}, {4, 9}, {5, 9}, {4, 5, 9}, {8, 9}, {4, 8, 9}, {5, 8, 9}, {4, 5, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_40_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 40 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({4, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}, {7}, {4, 7}, {5, 7}, {4, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_41_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 41 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({5, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({5, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {5}, {7}, {5, 7}, {9}, {5, 9}, {7, 9}, {5, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_42_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 42 =
      alignedReturnQuotientCoordinate 0
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        alignedReturnQuotientCoordinate 0
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [alignedReturnQuotientCoordinate, alignedReturnQuotientPair,
    quadraticProjection, quadraticPair, aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({5, 7} : Finset (Fin 10)).powerset =
      {∅, {5}, {7}, {5, 7}} := by decide
  rw [hpowersetFirst]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_43_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 43 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({4, 5, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 5, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}, {7}, {4, 7}, {5, 7}, {4, 5, 7}, {9}, {4, 9}, {5, 9}, {4, 5, 9}, {7, 9}, {4, 7, 9}, {5, 7, 9}, {4, 5, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_44_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 44 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({0, 2, 4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {4}, {0, 4}, {2, 4}, {0, 2, 4}, {5}, {0, 5}, {2, 5}, {0, 2, 5}, {4, 5}, {0, 4, 5}, {2, 4, 5}, {0, 2, 4, 5}, {9}, {0, 9}, {2, 9}, {0, 2, 9}, {4, 9}, {0, 4, 9}, {2, 4, 9}, {0, 2, 4, 9}, {5, 9}, {0, 5, 9}, {2, 5, 9}, {0, 2, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {2, 4, 5, 9}, {0, 2, 4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_45_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 45 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({3, 4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {6}, {3, 6}, {4, 6}, {3, 4, 6}, {9}, {3, 9}, {4, 9}, {3, 4, 9}, {6, 9}, {3, 6, 9}, {4, 6, 9}, {3, 4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_46_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 46 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 4, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {7}, {2, 7}, {4, 7}, {2, 4, 7}, {9}, {2, 9}, {4, 9}, {2, 4, 9}, {7, 9}, {2, 7, 9}, {4, 7, 9}, {2, 4, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_47_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 47 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 3, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 3, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {3}, {2, 3}, {4}, {2, 4}, {3, 4}, {2, 3, 4}, {9}, {2, 9}, {3, 9}, {2, 3, 9}, {4, 9}, {2, 4, 9}, {3, 4, 9}, {2, 3, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_48_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 48 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({2, 4, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {8}, {2, 8}, {4, 8}, {2, 4, 8}, {9}, {2, 9}, {4, 9}, {2, 4, 9}, {8, 9}, {2, 8, 9}, {4, 8, 9}, {2, 4, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneRInf_constraint_49_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneRInfRawConstraint p.vector 49 =
      (mixedReturnFeedbackProduct .zeroOne .infinity p).coeff
        ⟨({0, 3, 4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 3, 4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {3}, {0, 3}, {4}, {0, 4}, {3, 4}, {0, 3, 4}, {5}, {0, 5}, {3, 5}, {0, 3, 5}, {4, 5}, {0, 4, 5}, {3, 4, 5}, {0, 3, 4, 5}, {9}, {0, 9}, {3, 9}, {0, 3, 9}, {4, 9}, {0, 4, 9}, {3, 4, 9}, {0, 3, 4, 9}, {5, 9}, {0, 5, 9}, {3, 5, 9}, {0, 3, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {3, 4, 5, 9}, {0, 3, 4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- The literal quadratic-history hypotheses discharge every equation in
the `ZeroOneRInf` raw certificate. -/
theorem zeroOneRInf_equations_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .zeroOne p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne
      .infinity p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p))) :
    ∀ i : Fin 50, zeroOneRInfRawConstraint p.vector i = 0 := by
  intro i
  fin_cases i
  · change zeroOneRInfRawConstraint p.vector (0 : Fin 50) = 0
    rw [zeroOneRInf_constraint_0_eq_returned_coeff]
    exact hreturned ⟨{0, 2, 5}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (1 : Fin 50) = 0
    rw [zeroOneRInf_constraint_1_eq_returned_coeff]
    exact hreturned ⟨{0, 3, 5}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (2 : Fin 50) = 0
    rw [zeroOneRInf_constraint_2_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 7}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (3 : Fin 50) = 0
    rw [zeroOneRInf_constraint_3_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 8}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (4 : Fin 50) = 0
    rw [zeroOneRInf_constraint_4_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 5}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (5 : Fin 50) = 0
    rw [zeroOneRInf_constraint_5_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 5}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (6 : Fin 50) = 0
    rw [zeroOneRInf_constraint_6_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 7}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (7 : Fin 50) = 0
    rw [zeroOneRInf_constraint_7_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 8}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (8 : Fin 50) = 0
    rw [zeroOneRInf_constraint_8_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (9 : Fin 50) = 0
    rw [zeroOneRInf_constraint_9_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (10 : Fin 50) = 0
    rw [zeroOneRInf_constraint_10_eq_feedback_coeff]
    exact hfeedback ⟨{2, 5, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (11 : Fin 50) = 0
    rw [zeroOneRInf_constraint_11_eq_feedback_coeff]
    exact hfeedback ⟨{3, 5, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (12 : Fin 50) = 0
    rw [zeroOneRInf_constraint_12_eq_feedback_coeff]
    exact hfeedback ⟨{4, 5, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (13 : Fin 50) = 0
    rw [zeroOneRInf_constraint_13_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 5, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (14 : Fin 50) = 0
    rw [zeroOneRInf_constraint_14_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 5, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (15 : Fin 50) = 0
    rw [zeroOneRInf_constraint_15_eq_feedback_coeff]
    exact hfeedback ⟨{3, 7, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (16 : Fin 50) = 0
    rw [zeroOneRInf_constraint_16_eq_feedback_coeff]
    exact hfeedback ⟨{4, 7, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (17 : Fin 50) = 0
    rw [zeroOneRInf_constraint_17_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 7, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (18 : Fin 50) = 0
    rw [zeroOneRInf_constraint_18_eq_feedback_coeff]
    exact hfeedback ⟨{3, 8, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (19 : Fin 50) = 0
    rw [zeroOneRInf_constraint_19_eq_feedback_coeff]
    exact hfeedback ⟨{4, 8, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (20 : Fin 50) = 0
    rw [zeroOneRInf_constraint_20_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 8, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (21 : Fin 50) = 0
    rw [zeroOneRInf_constraint_21_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 0
  · change zeroOneRInfRawConstraint p.vector (22 : Fin 50) = 0
    rw [zeroOneRInf_constraint_22_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 1
  · change zeroOneRInfRawConstraint p.vector (23 : Fin 50) = 0
    rw [zeroOneRInf_constraint_23_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 4
  · change zeroOneRInfRawConstraint p.vector (24 : Fin 50) = 0
    rw [zeroOneRInf_constraint_24_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 8
  · change zeroOneRInfRawConstraint p.vector (25 : Fin 50) = 0
    rw [zeroOneRInf_constraint_25_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 11
  · change zeroOneRInfRawConstraint p.vector (26 : Fin 50) = 0
    rw [zeroOneRInf_constraint_26_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 10
  · change zeroOneRInfRawConstraint p.vector (27 : Fin 50) = 0
    rw [zeroOneRInf_constraint_27_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 6}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (28 : Fin 50) = 0
    rw [zeroOneRInf_constraint_28_eq_feedback_coeff]
    exact hfeedback ⟨{2, 6, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (29 : Fin 50) = 0
    rw [zeroOneRInf_constraint_29_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 5
  · change zeroOneRInfRawConstraint p.vector (30 : Fin 50) = 0
    rw [zeroOneRInf_constraint_30_eq_feedback_coeff]
    exact hfeedback ⟨{4, 6, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (31 : Fin 50) = 0
    rw [zeroOneRInf_constraint_31_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 6, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (32 : Fin 50) = 0
    rw [zeroOneRInf_constraint_32_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 6, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (33 : Fin 50) = 0
    rw [zeroOneRInf_constraint_33_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 6}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (34 : Fin 50) = 0
    rw [zeroOneRInf_constraint_34_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 8, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (35 : Fin 50) = 0
    rw [zeroOneRInf_constraint_35_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 7, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (36 : Fin 50) = 0
    rw [zeroOneRInf_constraint_36_eq_feedback_coeff]
    exact hfeedback ⟨{4, 5, 8}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (37 : Fin 50) = 0
    rw [zeroOneRInf_constraint_37_eq_feedback_coeff]
    exact hfeedback ⟨{5, 8, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (38 : Fin 50) = 0
    rw [zeroOneRInf_constraint_38_eq_quotient_row]
    exact alignedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 2
  · change zeroOneRInfRawConstraint p.vector (39 : Fin 50) = 0
    rw [zeroOneRInf_constraint_39_eq_feedback_coeff]
    exact hfeedback ⟨{4, 5, 8, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (40 : Fin 50) = 0
    rw [zeroOneRInf_constraint_40_eq_feedback_coeff]
    exact hfeedback ⟨{4, 5, 7}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (41 : Fin 50) = 0
    rw [zeroOneRInf_constraint_41_eq_feedback_coeff]
    exact hfeedback ⟨{5, 7, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (42 : Fin 50) = 0
    rw [zeroOneRInf_constraint_42_eq_quotient_row]
    exact alignedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 0
  · change zeroOneRInfRawConstraint p.vector (43 : Fin 50) = 0
    rw [zeroOneRInf_constraint_43_eq_feedback_coeff]
    exact hfeedback ⟨{4, 5, 7, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (44 : Fin 50) = 0
    rw [zeroOneRInf_constraint_44_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 4, 5, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (45 : Fin 50) = 0
    rw [zeroOneRInf_constraint_45_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 6, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (46 : Fin 50) = 0
    rw [zeroOneRInf_constraint_46_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 7, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (47 : Fin 50) = 0
    rw [zeroOneRInf_constraint_47_eq_feedback_coeff]
    exact hfeedback ⟨{2, 3, 4, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (48 : Fin 50) = 0
    rw [zeroOneRInf_constraint_48_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 8, 9}⟩ (by decide)
  · change zeroOneRInfRawConstraint p.vector (49 : Fin 50) = 0
    rw [zeroOneRInf_constraint_49_eq_feedback_coeff]
    exact hfeedback ⟨{0, 3, 4, 5, 9}⟩ (by decide)

/-- Kernel-checked vanishing of the sparse missing-target row for this
mixed history leaf. -/
theorem zeroOneRInf_missingCoordinate_eq_zero_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .zeroOne p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne
      .infinity p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p))) :
    returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p)) = 0 := by
  rw [← zeroOneRInfRawTarget_eq_missingCoordinate p]
  exact zeroOne_RInf_Raw_history_missing_eq_zero p.vector
    (zeroOneRInf_equations_of_quadratic_history p hreturned hfeedback hprojection)

/-- Circuit-facing missing-coset exclusion for this normalized mixed
history leaf. -/
theorem firstOrderMissingFunctional_eq_zero_of_zeroOneRInf_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .zeroOne p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne
      .infinity p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget :
      quadraticProjection 10 (mixedReturnSection .zeroOne p) +
          quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .infinity p) =
        targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  let q := quadraticProjection 10 (mixedReturnSection .zeroOne p)
  let r := quadraticProjection 10
    (mixedReturnFeedbackProduct .zeroOne .infinity p)
  have hprojection : quadraticQuotientProjection q =
      quadraticQuotientProjection r :=
    quadraticQuotientProjection_eq_of_add_eq_target q r c htarget
  exact firstOrderMissingFunctional_eq_zero_of_missingCoordinate q r c
    (zeroOneRInf_missingCoordinate_eq_zero_of_quadratic_history p
      hreturned hfeedback hprojection) htarget

end
end N5
end UnrestrictedBooleanMul
