import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneTwoRInfRaw

/-!
# Semantic bridge for the `OneTwoRInf` return-history certificate

This generated module relates every raw Boolean-polynomial generator to a
literal ANF coefficient or to a genuine target-quotient row.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem oneTwoRInfRawTarget_eq_missingCoordinate
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawTarget p.vector =
      returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
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
  simp (config := { decide := true }) [oneTwoRInfRawTarget]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_0_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 0 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_1_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 1 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_2_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 2 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({1, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {1}, {2}, {1, 2}, {5}, {1, 5}, {2, 5}, {1, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_3_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 3 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 3, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 3, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {3}, {0, 3}, {5}, {0, 5}, {3, 5}, {0, 3, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_4_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 4 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({1, 3, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 3, 5} : Finset (Fin 10)).powerset =
      {∅, {1}, {3}, {1, 3}, {5}, {1, 5}, {3, 5}, {1, 3, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_5_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 5 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_6_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 6 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({1, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {6}, {1, 6}, {5, 6}, {1, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_7_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 7 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {7}, {0, 7}, {5, 7}, {0, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_8_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 8 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({1, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {7}, {1, 7}, {5, 7}, {1, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_9_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 9 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({0, 5, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 8} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {8}, {0, 8}, {5, 8}, {0, 5, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_10_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 10 =
      (mixedReturnSection .oneTwo p).coeff
        ⟨({1, 5, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 8} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {8}, {1, 8}, {5, 8}, {1, 5, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_11_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 11 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({1, 4, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 4, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {4}, {1, 4}, {6}, {1, 6}, {4, 6}, {1, 4, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_12_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 12 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({3, 4, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 6} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {6}, {3, 6}, {4, 6}, {3, 4, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_13_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 13 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({1, 4, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 4, 7} : Finset (Fin 10)).powerset =
      {∅, {1}, {4}, {1, 4}, {7}, {1, 7}, {4, 7}, {1, 4, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_14_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 14 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({2, 4, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 7} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {7}, {2, 7}, {4, 7}, {2, 4, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_15_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 15 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({2, 4, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 8} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {8}, {2, 8}, {4, 8}, {2, 4, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_16_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 16 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({3, 4, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 8} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {8}, {3, 8}, {4, 8}, {3, 4, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_17_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 17 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({1, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {4}, {1, 4}, {9}, {1, 9}, {4, 9}, {1, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_18_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 18 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({2, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {9}, {2, 9}, {4, 9}, {2, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_19_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 19 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({3, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {9}, {3, 9}, {4, 9}, {3, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_20_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 20 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({1, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {6}, {1, 6}, {9}, {1, 9}, {6, 9}, {1, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_21_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 21 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({3, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {6}, {3, 6}, {9}, {3, 9}, {6, 9}, {3, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_22_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 22 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {6}, {4, 6}, {9}, {4, 9}, {6, 9}, {4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_23_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 23 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({1, 4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {4}, {1, 4}, {6}, {1, 6}, {4, 6}, {1, 4, 6}, {9}, {1, 9}, {4, 9}, {1, 4, 9}, {6, 9}, {1, 6, 9}, {4, 6, 9}, {1, 4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_24_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 24 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({3, 4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {6}, {3, 6}, {4, 6}, {3, 4, 6}, {9}, {3, 9}, {4, 9}, {3, 4, 9}, {6, 9}, {3, 6, 9}, {4, 6, 9}, {3, 4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_25_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 25 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({1, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {7}, {1, 7}, {9}, {1, 9}, {7, 9}, {1, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_26_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 26 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({2, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {7}, {2, 7}, {9}, {2, 9}, {7, 9}, {2, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_27_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 27 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({4, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {7}, {4, 7}, {9}, {4, 9}, {7, 9}, {4, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_28_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 28 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({1, 4, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 4, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {4}, {1, 4}, {7}, {1, 7}, {4, 7}, {1, 4, 7}, {9}, {1, 9}, {4, 9}, {1, 4, 9}, {7, 9}, {1, 7, 9}, {4, 7, 9}, {1, 4, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_29_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 29 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({2, 4, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {7}, {2, 7}, {4, 7}, {2, 4, 7}, {9}, {2, 9}, {4, 9}, {2, 4, 9}, {7, 9}, {2, 7, 9}, {4, 7, 9}, {2, 4, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_30_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 30 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({2, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {8}, {2, 8}, {9}, {2, 9}, {8, 9}, {2, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_31_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 31 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({3, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {8}, {3, 8}, {9}, {3, 9}, {8, 9}, {3, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_32_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 32 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({4, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {8}, {4, 8}, {9}, {4, 9}, {8, 9}, {4, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_33_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 33 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({2, 4, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {8}, {2, 8}, {4, 8}, {2, 4, 8}, {9}, {2, 9}, {4, 9}, {2, 4, 9}, {8, 9}, {2, 8, 9}, {4, 8, 9}, {2, 4, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_34_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 34 =
      (mixedReturnFeedbackProduct .oneTwo .infinity p).coeff
        ⟨({3, 4, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {8}, {3, 8}, {4, 8}, {3, 4, 8}, {9}, {3, 9}, {4, 9}, {3, 4, 9}, {8, 9}, {3, 8, 9}, {4, 8, 9}, {3, 4, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_35_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 35 =
      mixedReturnQuotientCoordinate 0
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 0
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
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
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_36_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 36 =
      mixedReturnQuotientCoordinate 1
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 1
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
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
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_37_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 37 =
      mixedReturnQuotientCoordinate 2
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 2
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
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
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_38_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 38 =
      mixedReturnQuotientCoordinate 3
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 3
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({1, 7} : Finset (Fin 10)).powerset =
      {∅, {1}, {7}, {1, 7}} := by decide
  have hpowersetSecond : ({3, 5} : Finset (Fin 10)).powerset =
      {∅, {3}, {5}, {3, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_39_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 39 =
      mixedReturnQuotientCoordinate 4
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 4
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
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
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_40_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 40 =
      mixedReturnQuotientCoordinate 6
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 6
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({2, 7} : Finset (Fin 10)).powerset =
      {∅, {2}, {7}, {2, 7}} := by decide
  have hpowersetSecond : ({4, 5} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_41_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 41 =
      mixedReturnQuotientCoordinate 7
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 7
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({2, 8} : Finset (Fin 10)).powerset =
      {∅, {2}, {8}, {2, 8}} := by decide
  have hpowersetSecond : ({4, 6} : Finset (Fin 10)).powerset =
      {∅, {4}, {6}, {4, 6}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_42_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 42 =
      mixedReturnQuotientCoordinate 8
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 8
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
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
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_43_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 43 =
      mixedReturnQuotientCoordinate 9
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 9
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({3, 6} : Finset (Fin 10)).powerset =
      {∅, {3}, {6}, {3, 6}} := by decide
  have hpowersetSecond : ({4, 5} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneTwoRInf_constraint_44_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneTwoRInfRawConstraint p.vector 44 =
      mixedReturnQuotientCoordinate 10
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        mixedReturnQuotientCoordinate 10
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) := by
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
  simp (config := { decide := true }) [oneTwoRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- The literal quadratic-history hypotheses discharge every equation in
the `OneTwoRInf` raw certificate. -/
theorem oneTwoRInf_equations_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo
      .infinity p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p))) :
    ∀ i : Fin 45, oneTwoRInfRawConstraint p.vector i = 0 := by
  intro i
  fin_cases i
  · change oneTwoRInfRawConstraint p.vector (0 : Fin 45) = 0
    rw [oneTwoRInf_constraint_0_eq_returned_coeff]
    exact hreturned ⟨{0, 1, 5}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (1 : Fin 45) = 0
    rw [oneTwoRInf_constraint_1_eq_returned_coeff]
    exact hreturned ⟨{0, 2, 5}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (2 : Fin 45) = 0
    rw [oneTwoRInf_constraint_2_eq_returned_coeff]
    exact hreturned ⟨{1, 2, 5}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (3 : Fin 45) = 0
    rw [oneTwoRInf_constraint_3_eq_returned_coeff]
    exact hreturned ⟨{0, 3, 5}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (4 : Fin 45) = 0
    rw [oneTwoRInf_constraint_4_eq_returned_coeff]
    exact hreturned ⟨{1, 3, 5}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (5 : Fin 45) = 0
    rw [oneTwoRInf_constraint_5_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 6}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (6 : Fin 45) = 0
    rw [oneTwoRInf_constraint_6_eq_returned_coeff]
    exact hreturned ⟨{1, 5, 6}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (7 : Fin 45) = 0
    rw [oneTwoRInf_constraint_7_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 7}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (8 : Fin 45) = 0
    rw [oneTwoRInf_constraint_8_eq_returned_coeff]
    exact hreturned ⟨{1, 5, 7}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (9 : Fin 45) = 0
    rw [oneTwoRInf_constraint_9_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 8}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (10 : Fin 45) = 0
    rw [oneTwoRInf_constraint_10_eq_returned_coeff]
    exact hreturned ⟨{1, 5, 8}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (11 : Fin 45) = 0
    rw [oneTwoRInf_constraint_11_eq_feedback_coeff]
    exact hfeedback ⟨{1, 4, 6}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (12 : Fin 45) = 0
    rw [oneTwoRInf_constraint_12_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 6}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (13 : Fin 45) = 0
    rw [oneTwoRInf_constraint_13_eq_feedback_coeff]
    exact hfeedback ⟨{1, 4, 7}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (14 : Fin 45) = 0
    rw [oneTwoRInf_constraint_14_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 7}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (15 : Fin 45) = 0
    rw [oneTwoRInf_constraint_15_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 8}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (16 : Fin 45) = 0
    rw [oneTwoRInf_constraint_16_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 8}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (17 : Fin 45) = 0
    rw [oneTwoRInf_constraint_17_eq_feedback_coeff]
    exact hfeedback ⟨{1, 4, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (18 : Fin 45) = 0
    rw [oneTwoRInf_constraint_18_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (19 : Fin 45) = 0
    rw [oneTwoRInf_constraint_19_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (20 : Fin 45) = 0
    rw [oneTwoRInf_constraint_20_eq_feedback_coeff]
    exact hfeedback ⟨{1, 6, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (21 : Fin 45) = 0
    rw [oneTwoRInf_constraint_21_eq_feedback_coeff]
    exact hfeedback ⟨{3, 6, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (22 : Fin 45) = 0
    rw [oneTwoRInf_constraint_22_eq_feedback_coeff]
    exact hfeedback ⟨{4, 6, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (23 : Fin 45) = 0
    rw [oneTwoRInf_constraint_23_eq_feedback_coeff]
    exact hfeedback ⟨{1, 4, 6, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (24 : Fin 45) = 0
    rw [oneTwoRInf_constraint_24_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 6, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (25 : Fin 45) = 0
    rw [oneTwoRInf_constraint_25_eq_feedback_coeff]
    exact hfeedback ⟨{1, 7, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (26 : Fin 45) = 0
    rw [oneTwoRInf_constraint_26_eq_feedback_coeff]
    exact hfeedback ⟨{2, 7, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (27 : Fin 45) = 0
    rw [oneTwoRInf_constraint_27_eq_feedback_coeff]
    exact hfeedback ⟨{4, 7, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (28 : Fin 45) = 0
    rw [oneTwoRInf_constraint_28_eq_feedback_coeff]
    exact hfeedback ⟨{1, 4, 7, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (29 : Fin 45) = 0
    rw [oneTwoRInf_constraint_29_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 7, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (30 : Fin 45) = 0
    rw [oneTwoRInf_constraint_30_eq_feedback_coeff]
    exact hfeedback ⟨{2, 8, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (31 : Fin 45) = 0
    rw [oneTwoRInf_constraint_31_eq_feedback_coeff]
    exact hfeedback ⟨{3, 8, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (32 : Fin 45) = 0
    rw [oneTwoRInf_constraint_32_eq_feedback_coeff]
    exact hfeedback ⟨{4, 8, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (33 : Fin 45) = 0
    rw [oneTwoRInf_constraint_33_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 8, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (34 : Fin 45) = 0
    rw [oneTwoRInf_constraint_34_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 8, 9}⟩ (by decide)
  · change oneTwoRInfRawConstraint p.vector (35 : Fin 45) = 0
    rw [oneTwoRInf_constraint_35_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 0
  · change oneTwoRInfRawConstraint p.vector (36 : Fin 45) = 0
    rw [oneTwoRInf_constraint_36_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 1
  · change oneTwoRInfRawConstraint p.vector (37 : Fin 45) = 0
    rw [oneTwoRInf_constraint_37_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 2
  · change oneTwoRInfRawConstraint p.vector (38 : Fin 45) = 0
    rw [oneTwoRInf_constraint_38_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 3
  · change oneTwoRInfRawConstraint p.vector (39 : Fin 45) = 0
    rw [oneTwoRInf_constraint_39_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 4
  · change oneTwoRInfRawConstraint p.vector (40 : Fin 45) = 0
    rw [oneTwoRInf_constraint_40_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 6
  · change oneTwoRInfRawConstraint p.vector (41 : Fin 45) = 0
    rw [oneTwoRInf_constraint_41_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 7
  · change oneTwoRInfRawConstraint p.vector (42 : Fin 45) = 0
    rw [oneTwoRInf_constraint_42_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 8
  · change oneTwoRInfRawConstraint p.vector (43 : Fin 45) = 0
    rw [oneTwoRInf_constraint_43_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 9
  · change oneTwoRInfRawConstraint p.vector (44 : Fin 45) = 0
    rw [oneTwoRInf_constraint_44_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 10

/-- Kernel-checked vanishing of the sparse missing-target row for this
mixed history leaf. -/
theorem oneTwoRInf_missingCoordinate_eq_zero_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo
      .infinity p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p))) :
    returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .oneTwo p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p)) = 0 := by
  rw [← oneTwoRInfRawTarget_eq_missingCoordinate p]
  exact oneTwo_RInf_Raw_history_missing_eq_zero p.vector
    (oneTwoRInf_equations_of_quadratic_history p hreturned hfeedback hprojection)

/-- Circuit-facing missing-coset exclusion for this normalized mixed
history leaf. -/
theorem firstOrderMissingFunctional_eq_zero_of_oneTwoRInf_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneTwo p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneTwo
      .infinity p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget :
      quadraticProjection 10 (mixedReturnSection .oneTwo p) +
          quadraticProjection 10
            (mixedReturnFeedbackProduct .oneTwo .infinity p) =
        targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  let q := quadraticProjection 10 (mixedReturnSection .oneTwo p)
  let r := quadraticProjection 10
    (mixedReturnFeedbackProduct .oneTwo .infinity p)
  have hprojection : quadraticQuotientProjection q =
      quadraticQuotientProjection r :=
    quadraticQuotientProjection_eq_of_add_eq_target q r c htarget
  exact firstOrderMissingFunctional_eq_zero_of_missingCoordinate q r c
    (oneTwoRInf_missingCoordinate_eq_zero_of_quadratic_history p
      hreturned hfeedback hprojection) htarget

end
end N5
end UnrestrictedBooleanMul
