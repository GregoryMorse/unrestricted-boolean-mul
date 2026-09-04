import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneTwoR1Raw

/-!
# Semantic bridge for the `OneTwoR1` return-history certificate

This generated module relates every raw Boolean-polynomial generator to a
literal ANF coefficient or to a genuine target-quotient row.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem oneTwoR1RawTarget_eq_missingCoordinate
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawTarget p.vector =
      returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p)) := by
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
  simp (config := { decide := true }) [oneTwoR1RawTarget]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_0_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 0 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_1_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 1 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_2_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 2 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({1, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {1}, {2}, {1, 2}, {5}, {1, 5}, {2, 5}, {1, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_3_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 3 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_4_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 4 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({1, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {6}, {1, 6}, {5, 6}, {1, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_5_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 5 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {9}, {0, 9}, {5, 9}, {0, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_6_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 6 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({1, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {9}, {1, 9}, {5, 9}, {1, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_7_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 7 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_8_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 8 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_9_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 9 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 1, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {6}, {0, 6}, {1, 6}, {0, 1, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_10_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 10 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 2, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {6}, {0, 6}, {2, 6}, {0, 2, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_11_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 11 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_12_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 12 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({1, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {6}, {1, 6}, {5, 6}, {1, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_13_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 13 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 1, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {6}, {0, 6}, {1, 6}, {0, 1, 6}, {5, 6}, {0, 5, 6}, {1, 5, 6}, {0, 1, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_14_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 14 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({2, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {2}, {5}, {2, 5}, {6}, {2, 6}, {5, 6}, {2, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_15_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 15 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 2, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}, {6}, {0, 6}, {2, 6}, {0, 2, 6}, {5, 6}, {0, 5, 6}, {2, 5, 6}, {0, 2, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_16_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 16 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 1, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {9}, {0, 9}, {1, 9}, {0, 1, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_17_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 17 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 2, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {9}, {0, 9}, {2, 9}, {0, 2, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_18_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 18 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {9}, {0, 9}, {5, 9}, {0, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_19_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 19 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({1, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {9}, {1, 9}, {5, 9}, {1, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_20_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 20 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 1, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {9}, {0, 9}, {1, 9}, {0, 1, 9}, {5, 9}, {0, 5, 9}, {1, 5, 9}, {0, 1, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_21_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 21 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({2, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {5}, {2, 5}, {9}, {2, 9}, {5, 9}, {2, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_22_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 22 =
      (mixedReturnFeedbackProduct .oneTwo .one p).coeff
        ⟨({0, 2, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}, {9}, {0, 9}, {2, 9}, {0, 2, 9}, {5, 9}, {0, 5, 9}, {2, 5, 9}, {0, 2, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_23_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 23 =
      mixedReturnQuotientCoordinate 0
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 0
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p)) := by
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
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_24_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 24 =
      mixedReturnQuotientCoordinate 1
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 1
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p)) := by
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
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_25_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 25 =
      mixedReturnQuotientCoordinate 2
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 2
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({1, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {6}, {1, 6}} := by decide
  have hpowersetSecond : ({2, 5} : Finset (Fin 10)).powerset =
      {∅, {2}, {5}, {2, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoR1_constraint_26_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoR1RawConstraint p.vector 26 =
      mixedReturnQuotientCoordinate 5
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 5
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p)) := by
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
  simp (config := { decide := true }) [oneTwoR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- The literal quadratic-history hypotheses discharge every equation in
the `OneTwoR1` raw certificate. -/
theorem oneTwoR1_equations_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo
      .one p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p))) :
    ∀ i : Fin 27, oneTwoR1RawConstraint p.vector i = 0 := by
  intro i
  fin_cases i
  · change oneTwoR1RawConstraint p.vector (0 : Fin 27) = 0
    rw [oneTwoR1_constraint_0_eq_returned_coeff]
    exact hreturned ⟨{0, 1, 5}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (1 : Fin 27) = 0
    rw [oneTwoR1_constraint_1_eq_returned_coeff]
    exact hreturned ⟨{0, 2, 5}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (2 : Fin 27) = 0
    rw [oneTwoR1_constraint_2_eq_returned_coeff]
    exact hreturned ⟨{1, 2, 5}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (3 : Fin 27) = 0
    rw [oneTwoR1_constraint_3_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (4 : Fin 27) = 0
    rw [oneTwoR1_constraint_4_eq_returned_coeff]
    exact hreturned ⟨{1, 5, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (5 : Fin 27) = 0
    rw [oneTwoR1_constraint_5_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (6 : Fin 27) = 0
    rw [oneTwoR1_constraint_6_eq_returned_coeff]
    exact hreturned ⟨{1, 5, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (7 : Fin 27) = 0
    rw [oneTwoR1_constraint_7_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (8 : Fin 27) = 0
    rw [oneTwoR1_constraint_8_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 5}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (9 : Fin 27) = 0
    rw [oneTwoR1_constraint_9_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (10 : Fin 27) = 0
    rw [oneTwoR1_constraint_10_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (11 : Fin 27) = 0
    rw [oneTwoR1_constraint_11_eq_feedback_coeff]
    exact hfeedback ⟨{0, 5, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (12 : Fin 27) = 0
    rw [oneTwoR1_constraint_12_eq_feedback_coeff]
    exact hfeedback ⟨{1, 5, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (13 : Fin 27) = 0
    rw [oneTwoR1_constraint_13_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (14 : Fin 27) = 0
    rw [oneTwoR1_constraint_14_eq_feedback_coeff]
    exact hfeedback ⟨{2, 5, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (15 : Fin 27) = 0
    rw [oneTwoR1_constraint_15_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 5, 6}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (16 : Fin 27) = 0
    rw [oneTwoR1_constraint_16_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (17 : Fin 27) = 0
    rw [oneTwoR1_constraint_17_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (18 : Fin 27) = 0
    rw [oneTwoR1_constraint_18_eq_feedback_coeff]
    exact hfeedback ⟨{0, 5, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (19 : Fin 27) = 0
    rw [oneTwoR1_constraint_19_eq_feedback_coeff]
    exact hfeedback ⟨{1, 5, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (20 : Fin 27) = 0
    rw [oneTwoR1_constraint_20_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (21 : Fin 27) = 0
    rw [oneTwoR1_constraint_21_eq_feedback_coeff]
    exact hfeedback ⟨{2, 5, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (22 : Fin 27) = 0
    rw [oneTwoR1_constraint_22_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 5, 9}⟩ (by decide)
  · change oneTwoR1RawConstraint p.vector (23 : Fin 27) = 0
    rw [oneTwoR1_constraint_23_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 0
  · change oneTwoR1RawConstraint p.vector (24 : Fin 27) = 0
    rw [oneTwoR1_constraint_24_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 1
  · change oneTwoR1RawConstraint p.vector (25 : Fin 27) = 0
    rw [oneTwoR1_constraint_25_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 2
  · change oneTwoR1RawConstraint p.vector (26 : Fin 27) = 0
    rw [oneTwoR1_constraint_26_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 5

/-- Kernel-checked vanishing of the sparse missing-target row for this
mixed history leaf. -/
theorem oneTwoR1_missingCoordinate_eq_zero_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo
      .one p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p))) :
    returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p)) = 0 := by
  rw [← oneTwoR1RawTarget_eq_missingCoordinate p]
  exact oneTwo_R1_Raw_history_missing_eq_zero p.vector
    (oneTwoR1_equations_of_quadratic_history p hreturned hfeedback hprojection)

/-- Circuit-facing missing-coset exclusion for this normalized mixed
history leaf. -/
theorem firstOrderMissingFunctional_eq_zero_of_oneTwoR1_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo
      .one p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget :
      quadraticProjection 10 (mixedReturnSection .oneTwo p) +
          quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .one p) =
        targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  let q := quadraticProjection 10 (mixedReturnSection .oneTwo p)
  let r := quadraticProjection 10
    (mixedReturnFeedbackProduct .oneTwo .one p)
  have hprojection : quadraticQuotientProjection q =
      quadraticQuotientProjection r :=
    quadraticQuotientProjection_eq_of_add_eq_target q r c htarget
  exact firstOrderMissingFunctional_eq_zero_of_missingCoordinate q r c
    (oneTwoR1_missingCoordinate_eq_zero_of_quadratic_history p
      hreturned hfeedback hprojection) htarget

end
end N5
end UnrestrictedBooleanMul
