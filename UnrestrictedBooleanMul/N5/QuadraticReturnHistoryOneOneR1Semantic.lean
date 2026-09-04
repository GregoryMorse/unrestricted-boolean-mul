import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneR1Raw

/-!
# Semantic bridge for the `OneOneR1` return-history certificate

This generated module relates every raw Boolean-polynomial generator to a
literal ANF coefficient or to a genuine target-quotient row.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem oneOneR1RawTarget_eq_missingCoordinate
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawTarget p.vector =
      returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p)) := by
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
  simp (config := { decide := true }) [oneOneR1RawTarget]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_0_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 0 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_1_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 1 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 4, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_2_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 2 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_3_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 3 =
      (mixedReturnSection .oneOneDifference p).coeff
        ⟨({0, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {7}, {0, 7}, {5, 7}, {0, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_4_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 4 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_5_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 5 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 4, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_6_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 6 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 1, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {6}, {0, 6}, {1, 6}, {0, 1, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_7_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 7 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 4, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {6}, {0, 6}, {4, 6}, {0, 4, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_8_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 8 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_9_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 9 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({1, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {6}, {1, 6}, {5, 6}, {1, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_10_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 10 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 1, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {6}, {0, 6}, {1, 6}, {0, 1, 6}, {5, 6}, {0, 5, 6}, {1, 5, 6}, {0, 1, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_11_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 11 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({4, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}, {6}, {4, 6}, {5, 6}, {4, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_12_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 12 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 4, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {6}, {0, 6}, {4, 6}, {0, 4, 6}, {5, 6}, {0, 5, 6}, {4, 5, 6}, {0, 4, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_13_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 13 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 1, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {7}, {0, 7}, {1, 7}, {0, 1, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_14_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 14 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 4, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {7}, {0, 7}, {4, 7}, {0, 4, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_15_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 15 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {7}, {0, 7}, {5, 7}, {0, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_16_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 16 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({1, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {7}, {1, 7}, {5, 7}, {1, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_17_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 17 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 1, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {7}, {0, 7}, {1, 7}, {0, 1, 7}, {5, 7}, {0, 5, 7}, {1, 5, 7}, {0, 1, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_18_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 18 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({4, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({4, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {4}, {5}, {4, 5}, {7}, {4, 7}, {5, 7}, {4, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_19_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 19 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 4, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {7}, {0, 7}, {4, 7}, {0, 4, 7}, {5, 7}, {0, 5, 7}, {4, 5, 7}, {0, 4, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_20_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 20 =
      mixedReturnQuotientCoordinate 0
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 0
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p)) := by
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
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_21_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 21 =
      mixedReturnQuotientCoordinate 1
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 1
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p)) := by
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
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_22_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 22 =
      mixedReturnQuotientCoordinate 2
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 2
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p)) := by
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
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_23_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 23 =
      mixedReturnQuotientCoordinate 3
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 3
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p)) := by
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
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_24_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 24 =
      mixedReturnQuotientCoordinate 4
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 4
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p)) := by
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
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_25_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 25 =
      mixedReturnQuotientCoordinate 8
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        mixedReturnQuotientCoordinate 8
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p)) := by
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
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_26_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 26 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 1, 5, 6, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5, 6, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {6}, {0, 6}, {1, 6}, {0, 1, 6}, {5, 6}, {0, 5, 6}, {1, 5, 6}, {0, 1, 5, 6}, {7}, {0, 7}, {1, 7}, {0, 1, 7}, {5, 7}, {0, 5, 7}, {1, 5, 7}, {0, 1, 5, 7}, {6, 7}, {0, 6, 7}, {1, 6, 7}, {0, 1, 6, 7}, {5, 6, 7}, {0, 5, 6, 7}, {1, 5, 6, 7}, {0, 1, 5, 6, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem oneOneR1_constraint_27_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    oneOneR1RawConstraint p.vector 27 =
      (mixedReturnFeedbackProduct .oneOneDifference .one p).coeff
        ⟨({0, 1, 4, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 4, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {4}, {0, 4}, {1, 4}, {0, 1, 4}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {4, 5}, {0, 4, 5}, {1, 4, 5}, {0, 1, 4, 5}, {6}, {0, 6}, {1, 6}, {0, 1, 6}, {4, 6}, {0, 4, 6}, {1, 4, 6}, {0, 1, 4, 6}, {5, 6}, {0, 5, 6}, {1, 5, 6}, {0, 1, 5, 6}, {4, 5, 6}, {0, 4, 5, 6}, {1, 4, 5, 6}, {0, 1, 4, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [oneOneR1RawConstraint]
  simp_mixed_return_history
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- The literal quadratic-history hypotheses discharge every equation in
the `OneOneR1` raw certificate. -/
theorem oneOneR1_equations_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference
      .one p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p))) :
    ∀ i : Fin 28, oneOneR1RawConstraint p.vector i = 0 := by
  intro i
  fin_cases i
  · change oneOneR1RawConstraint p.vector (0 : Fin 28) = 0
    rw [oneOneR1_constraint_0_eq_returned_coeff]
    exact hreturned ⟨{0, 1, 5}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (1 : Fin 28) = 0
    rw [oneOneR1_constraint_1_eq_returned_coeff]
    exact hreturned ⟨{0, 4, 5}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (2 : Fin 28) = 0
    rw [oneOneR1_constraint_2_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 6}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (3 : Fin 28) = 0
    rw [oneOneR1_constraint_3_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (4 : Fin 28) = 0
    rw [oneOneR1_constraint_4_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (5 : Fin 28) = 0
    rw [oneOneR1_constraint_5_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (6 : Fin 28) = 0
    rw [oneOneR1_constraint_6_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 6}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (7 : Fin 28) = 0
    rw [oneOneR1_constraint_7_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 6}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (8 : Fin 28) = 0
    rw [oneOneR1_constraint_8_eq_feedback_coeff]
    exact hfeedback ⟨{0, 5, 6}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (9 : Fin 28) = 0
    rw [oneOneR1_constraint_9_eq_feedback_coeff]
    exact hfeedback ⟨{1, 5, 6}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (10 : Fin 28) = 0
    rw [oneOneR1_constraint_10_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5, 6}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (11 : Fin 28) = 0
    rw [oneOneR1_constraint_11_eq_feedback_coeff]
    exact hfeedback ⟨{4, 5, 6}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (12 : Fin 28) = 0
    rw [oneOneR1_constraint_12_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 6}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (13 : Fin 28) = 0
    rw [oneOneR1_constraint_13_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (14 : Fin 28) = 0
    rw [oneOneR1_constraint_14_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (15 : Fin 28) = 0
    rw [oneOneR1_constraint_15_eq_feedback_coeff]
    exact hfeedback ⟨{0, 5, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (16 : Fin 28) = 0
    rw [oneOneR1_constraint_16_eq_feedback_coeff]
    exact hfeedback ⟨{1, 5, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (17 : Fin 28) = 0
    rw [oneOneR1_constraint_17_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (18 : Fin 28) = 0
    rw [oneOneR1_constraint_18_eq_feedback_coeff]
    exact hfeedback ⟨{4, 5, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (19 : Fin 28) = 0
    rw [oneOneR1_constraint_19_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (20 : Fin 28) = 0
    rw [oneOneR1_constraint_20_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 0
  · change oneOneR1RawConstraint p.vector (21 : Fin 28) = 0
    rw [oneOneR1_constraint_21_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 1
  · change oneOneR1RawConstraint p.vector (22 : Fin 28) = 0
    rw [oneOneR1_constraint_22_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 2
  · change oneOneR1RawConstraint p.vector (23 : Fin 28) = 0
    rw [oneOneR1_constraint_23_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 3
  · change oneOneR1RawConstraint p.vector (24 : Fin 28) = 0
    rw [oneOneR1_constraint_24_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 4
  · change oneOneR1RawConstraint p.vector (25 : Fin 28) = 0
    rw [oneOneR1_constraint_25_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection _ _ hprojection 8
  · change oneOneR1RawConstraint p.vector (26 : Fin 28) = 0
    rw [oneOneR1_constraint_26_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5, 6, 7}⟩ (by decide)
  · change oneOneR1RawConstraint p.vector (27 : Fin 28) = 0
    rw [oneOneR1_constraint_27_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 4, 5, 6}⟩ (by decide)

/-- Kernel-checked vanishing of the sparse missing-target row for this
mixed history leaf. -/
theorem oneOneR1_missingCoordinate_eq_zero_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference
      .one p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p))) :
    returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .oneOneDifference p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p)) = 0 := by
  rw [← oneOneR1RawTarget_eq_missingCoordinate p]
  exact oneOne_R1_Raw_history_missing_eq_zero p.vector
    (oneOneR1_equations_of_quadratic_history p hreturned hfeedback hprojection)

/-- Circuit-facing missing-coset exclusion for this normalized mixed
history leaf. -/
theorem firstOrderMissingFunctional_eq_zero_of_oneOneR1_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference
      .one p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget :
      quadraticProjection 10 (mixedReturnSection .oneOneDifference p) +
          quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .one p) =
        targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  let q := quadraticProjection 10 (mixedReturnSection .oneOneDifference p)
  let r := quadraticProjection 10
    (mixedReturnFeedbackProduct .oneOneDifference .one p)
  have hprojection : quadraticQuotientProjection q =
      quadraticQuotientProjection r :=
    quadraticQuotientProjection_eq_of_add_eq_target q r c htarget
  exact firstOrderMissingFunctional_eq_zero_of_missingCoordinate q r c
    (oneOneR1_missingCoordinate_eq_zero_of_quadratic_history p
      hreturned hfeedback hprojection) htarget

end
end N5
end UnrestrictedBooleanMul
