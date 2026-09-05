import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneRInfRaw

/-!
# Semantic bridge for the `OneOneRInf` return-history certificate

This generated module relates every raw Boolean-polynomial generator to a
literal ANF coefficient or to a genuine target-quotient row.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem oneOneRInfRawTarget_eq_missingCoordinate
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawTarget p.vector =
      returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawTarget]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_0_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 0 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_1_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 1 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_2_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 2 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 3, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 3, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {3}, {0, 3}, {5}, {0, 5}, {3, 5}, {0, 3, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_3_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 3 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_4_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 4 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {7}, {0, 7}, {5, 7}, {0, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_5_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 5 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 5, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 8} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {8}, {0, 8}, {5, 8}, {0, 5, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_6_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 6 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({1, 4, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 4, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {4}, {1, 4}, {6}, {1, 6}, {4, 6}, {1, 4, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_7_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 7 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({2, 4, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 6} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {6}, {2, 6}, {4, 6}, {2, 4, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_8_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 8 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({3, 4, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 7} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {7}, {3, 7}, {4, 7}, {3, 4, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_9_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 9 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({3, 4, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 8} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {8}, {3, 8}, {4, 8}, {3, 4, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_10_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 10 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({1, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {4}, {1, 4}, {9}, {1, 9}, {4, 9}, {1, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_11_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 11 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({2, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {9}, {2, 9}, {4, 9}, {2, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_12_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 12 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({3, 4, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {9}, {3, 9}, {4, 9}, {3, 4, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_13_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 13 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({1, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {6}, {1, 6}, {9}, {1, 9}, {6, 9}, {1, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_14_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 14 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({2, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {6}, {2, 6}, {9}, {2, 9}, {6, 9}, {2, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_15_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 15 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {6}, {4, 6}, {9}, {4, 9}, {6, 9}, {4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_16_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 16 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({1, 4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {1}, {4}, {1, 4}, {6}, {1, 6}, {4, 6}, {1, 4, 6}, {9}, {1, 9}, {4, 9}, {1, 4, 9}, {6, 9}, {1, 6, 9}, {4, 6, 9}, {1, 4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_17_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 17 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({2, 4, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 4, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {2}, {4}, {2, 4}, {6}, {2, 6}, {4, 6}, {2, 4, 6}, {9}, {2, 9}, {4, 9}, {2, 4, 9}, {6, 9}, {2, 6, 9}, {4, 6, 9}, {2, 4, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_18_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 18 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({3, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {7}, {3, 7}, {9}, {3, 9}, {7, 9}, {3, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_19_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 19 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({4, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {7}, {4, 7}, {9}, {4, 9}, {7, 9}, {4, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_20_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 20 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({3, 4, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {7}, {3, 7}, {4, 7}, {3, 4, 7}, {9}, {3, 9}, {4, 9}, {3, 4, 9}, {7, 9}, {3, 7, 9}, {4, 7, 9}, {3, 4, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_21_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 21 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({3, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {8}, {3, 8}, {9}, {3, 9}, {8, 9}, {3, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_22_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 22 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({4, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {4}, {8}, {4, 8}, {9}, {4, 9}, {8, 9}, {4, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_23_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 23 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({3, 4, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({3, 4, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {3}, {4}, {3, 4}, {8}, {3, 8}, {4, 8}, {3, 4, 8}, {9}, {3, 9}, {4, 9}, {3, 4, 9}, {8, 9}, {3, 8, 9}, {4, 8, 9}, {3, 4, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_24_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 24 =
      mixedReturnQuotientCoordinate 0
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 0
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_25_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 25 =
      mixedReturnQuotientCoordinate 1
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 1
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_26_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 26 =
      mixedReturnQuotientCoordinate 2
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 2
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_27_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 27 =
      mixedReturnQuotientCoordinate 4
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 4
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_28_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 28 =
      mixedReturnQuotientCoordinate 5
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 5
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_29_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 29 =
      mixedReturnQuotientCoordinate 8
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 8
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_30_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 30 =
      mixedReturnQuotientCoordinate 11
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 11
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_31_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 31 =
      mixedReturnQuotientCoordinate 10
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 10
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) := by
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
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_32_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 32 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({0, 4, 5, 8, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 8, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {8}, {0, 8}, {4, 8}, {0, 4, 8}, {5, 8}, {0, 5, 8}, {4, 5, 8}, {0, 4, 5, 8}, {9}, {0, 9}, {4, 9}, {0, 4, 9}, {5, 9}, {0, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {8, 9}, {0, 8, 9}, {4, 8, 9}, {0, 4, 8, 9}, {5, 8, 9}, {0, 5, 8, 9}, {4, 5, 8, 9}, {0, 4, 5, 8, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_33_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 33 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({0, 4, 5, 7, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 7, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {7}, {0, 7}, {4, 7}, {0, 4, 7}, {5, 7}, {0, 5, 7}, {4, 5, 7}, {0, 4, 5, 7}, {9}, {0, 9}, {4, 9}, {0, 4, 9}, {5, 9}, {0, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {7, 9}, {0, 7, 9}, {4, 7, 9}, {0, 4, 7, 9}, {5, 7, 9}, {0, 5, 7, 9}, {4, 5, 7, 9}, {0, 4, 5, 7, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_34_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 34 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({0, 4, 5, 6, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 6, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {6}, {0, 6}, {4, 6}, {0, 4, 6}, {5, 6}, {0, 5, 6}, {4, 5, 6}, {0, 4, 5, 6}, {9}, {0, 9}, {4, 9}, {0, 4, 9}, {5, 9}, {0, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {6, 9}, {0, 6, 9}, {4, 6, 9}, {0, 4, 6, 9}, {5, 6, 9}, {0, 5, 6, 9}, {4, 5, 6, 9}, {0, 4, 5, 6, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_35_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 35 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({0, 3, 4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 3, 4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {3}, {0, 3}, {4}, {0, 4}, {3, 4}, {0, 3, 4}, {5}, {0, 5}, {3, 5}, {0, 3, 5}, {4, 5}, {0, 4, 5}, {3, 4, 5}, {0, 3, 4, 5}, {9}, {0, 9}, {3, 9}, {0, 3, 9}, {4, 9}, {0, 4, 9}, {3, 4, 9}, {0, 3, 4, 9}, {5, 9}, {0, 5, 9}, {3, 5, 9}, {0, 3, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {3, 4, 5, 9}, {0, 3, 4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_36_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 36 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({0, 2, 4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {4}, {0, 4}, {2, 4}, {0, 2, 4}, {5}, {0, 5}, {2, 5}, {0, 2, 5}, {4, 5}, {0, 4, 5}, {2, 4, 5}, {0, 2, 4, 5}, {9}, {0, 9}, {2, 9}, {0, 2, 9}, {4, 9}, {0, 4, 9}, {2, 4, 9}, {0, 2, 4, 9}, {5, 9}, {0, 5, 9}, {2, 5, 9}, {0, 2, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {2, 4, 5, 9}, {0, 2, 4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneRInf_constraint_37_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneRInfRawConstraint p.vector 37 =
      (mixedReturnFeedbackProduct .oneOneDifference .infinity p).coeff
        ⟨({0, 1, 4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {4}, {0, 4}, {1, 4}, {0, 1, 4}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {4, 5}, {0, 4, 5}, {1, 4, 5}, {0, 1, 4, 5}, {9}, {0, 9}, {1, 9}, {0, 1, 9}, {4, 9}, {0, 4, 9}, {1, 4, 9}, {0, 1, 4, 9}, {5, 9}, {0, 5, 9}, {1, 5, 9}, {0, 1, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}, {1, 4, 5, 9}, {0, 1, 4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneRInfRawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- The literal quadratic-history hypotheses discharge every equation in
the `OneOneRInf` raw certificate. -/
theorem oneOneRInf_equations_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference
      .infinity p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p))) :
    ∀ i : Fin 38, oneOneRInfRawConstraint p.vector i = 0 := by
  intro i
  fin_cases i
  · change oneOneRInfRawConstraint p.vector (0 : Fin 38) = 0
    rw [oneOneRInf_constraint_0_eq_returned_coeff]
    exact hreturned ⟨{0, 1, 5}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (1 : Fin 38) = 0
    rw [oneOneRInf_constraint_1_eq_returned_coeff]
    exact hreturned ⟨{0, 2, 5}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (2 : Fin 38) = 0
    rw [oneOneRInf_constraint_2_eq_returned_coeff]
    exact hreturned ⟨{0, 3, 5}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (3 : Fin 38) = 0
    rw [oneOneRInf_constraint_3_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 6}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (4 : Fin 38) = 0
    rw [oneOneRInf_constraint_4_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 7}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (5 : Fin 38) = 0
    rw [oneOneRInf_constraint_5_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 8}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (6 : Fin 38) = 0
    rw [oneOneRInf_constraint_6_eq_feedback_coeff]
    exact hfeedback ⟨{1, 4, 6}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (7 : Fin 38) = 0
    rw [oneOneRInf_constraint_7_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 6}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (8 : Fin 38) = 0
    rw [oneOneRInf_constraint_8_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 7}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (9 : Fin 38) = 0
    rw [oneOneRInf_constraint_9_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 8}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (10 : Fin 38) = 0
    rw [oneOneRInf_constraint_10_eq_feedback_coeff]
    exact hfeedback ⟨{1, 4, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (11 : Fin 38) = 0
    rw [oneOneRInf_constraint_11_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (12 : Fin 38) = 0
    rw [oneOneRInf_constraint_12_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (13 : Fin 38) = 0
    rw [oneOneRInf_constraint_13_eq_feedback_coeff]
    exact hfeedback ⟨{1, 6, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (14 : Fin 38) = 0
    rw [oneOneRInf_constraint_14_eq_feedback_coeff]
    exact hfeedback ⟨{2, 6, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (15 : Fin 38) = 0
    rw [oneOneRInf_constraint_15_eq_feedback_coeff]
    exact hfeedback ⟨{4, 6, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (16 : Fin 38) = 0
    rw [oneOneRInf_constraint_16_eq_feedback_coeff]
    exact hfeedback ⟨{1, 4, 6, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (17 : Fin 38) = 0
    rw [oneOneRInf_constraint_17_eq_feedback_coeff]
    exact hfeedback ⟨{2, 4, 6, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (18 : Fin 38) = 0
    rw [oneOneRInf_constraint_18_eq_feedback_coeff]
    exact hfeedback ⟨{3, 7, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (19 : Fin 38) = 0
    rw [oneOneRInf_constraint_19_eq_feedback_coeff]
    exact hfeedback ⟨{4, 7, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (20 : Fin 38) = 0
    rw [oneOneRInf_constraint_20_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 7, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (21 : Fin 38) = 0
    rw [oneOneRInf_constraint_21_eq_feedback_coeff]
    exact hfeedback ⟨{3, 8, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (22 : Fin 38) = 0
    rw [oneOneRInf_constraint_22_eq_feedback_coeff]
    exact hfeedback ⟨{4, 8, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (23 : Fin 38) = 0
    rw [oneOneRInf_constraint_23_eq_feedback_coeff]
    exact hfeedback ⟨{3, 4, 8, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (24 : Fin 38) = 0
    rw [oneOneRInf_constraint_24_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 0
  · change oneOneRInfRawConstraint p.vector (25 : Fin 38) = 0
    rw [oneOneRInf_constraint_25_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 1
  · change oneOneRInfRawConstraint p.vector (26 : Fin 38) = 0
    rw [oneOneRInf_constraint_26_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 2
  · change oneOneRInfRawConstraint p.vector (27 : Fin 38) = 0
    rw [oneOneRInf_constraint_27_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 4
  · change oneOneRInfRawConstraint p.vector (28 : Fin 38) = 0
    rw [oneOneRInf_constraint_28_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 5
  · change oneOneRInfRawConstraint p.vector (29 : Fin 38) = 0
    rw [oneOneRInf_constraint_29_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 8
  · change oneOneRInfRawConstraint p.vector (30 : Fin 38) = 0
    rw [oneOneRInf_constraint_30_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 11
  · change oneOneRInfRawConstraint p.vector (31 : Fin 38) = 0
    rw [oneOneRInf_constraint_31_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 10
  · change oneOneRInfRawConstraint p.vector (32 : Fin 38) = 0
    rw [oneOneRInf_constraint_32_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 8, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (33 : Fin 38) = 0
    rw [oneOneRInf_constraint_33_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 7, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (34 : Fin 38) = 0
    rw [oneOneRInf_constraint_34_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 6, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (35 : Fin 38) = 0
    rw [oneOneRInf_constraint_35_eq_feedback_coeff]
    exact hfeedback ⟨{0, 3, 4, 5, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (36 : Fin 38) = 0
    rw [oneOneRInf_constraint_36_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 4, 5, 9}⟩ (by decide)
  · change oneOneRInfRawConstraint p.vector (37 : Fin 38) = 0
    rw [oneOneRInf_constraint_37_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 4, 5, 9}⟩ (by decide)

/-- Kernel-checked vanishing of the sparse missing-target row for this
mixed history leaf. -/
theorem oneOneRInf_missingCoordinate_eq_zero_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference
      .infinity p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p))) :
    returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p)) = 0 := by
  rw [← oneOneRInfRawTarget_eq_missingCoordinate p]
  exact oneOne_RInf_Raw_history_missing_eq_zero p.vector
    (oneOneRInf_equations_of_quadratic_history p hreturned hfeedback hprojection)

/-- Circuit-facing missing-coset exclusion for this normalized mixed
history leaf. -/
theorem firstOrderMissingFunctional_eq_zero_of_oneOneRInf_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference
      .infinity p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget :
      quadraticProjection 10 (mixedReturnSection .oneOneDifference p) +
          quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .infinity p) =
        targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  let q := quadraticProjection 10 (mixedReturnSection .oneOneDifference p)
  let r := quadraticProjection 10
    (mixedReturnFeedbackProduct .oneOneDifference .infinity p)
  have hprojection : quadraticQuotientProjection q =
      quadraticQuotientProjection r :=
    quadraticQuotientProjection_eq_of_add_eq_target q r c htarget
  exact firstOrderMissingFunctional_eq_zero_of_missingCoordinate q r c
    (oneOneRInf_missingCoordinate_eq_zero_of_quadratic_history p
      hreturned hfeedback hprojection) htarget

end
end N5
end UnrestrictedBooleanMul
