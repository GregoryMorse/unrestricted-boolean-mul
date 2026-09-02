import UnrestrictedBooleanMul.N5.CostedSuffix
import UnrestrictedBooleanMul.N5.CompletionDeficit
import UnrestrictedBooleanMul.N5.DefectOneCapacity
import UnrestrictedBooleanMul.N5.DefectTwoCapacity
import UnrestrictedBooleanMul.N5.LowDefectPrefix
import UnrestrictedBooleanMul.N5.MainInterface
import UnrestrictedBooleanMul.N5.RegimeClosure

/-!
# Cost-preserving final regime split

The original fixed-envelope formulation of first-order saturation is false.
For the twelve-gate lower bound it is also unnecessarily strong: the proof
only has to exclude target rank nine within the number of gates that remain
after the last all-quadratic prefix.

This module records that exact replacement and performs all final circuit
bookkeeping.  The two regime predicates retain the actual prefix state and
the exact suffix length, so a feedback collision that spends two gates to
gain one target direction is charged correctly.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- No exact-cost defect-legal suffix within `budget` gates reaches all nine
target directions. -/
def NoTargetCompletionWithin
    (W : Submodule F₂ (ANF 10)) (budget : Nat) : Prop :=
  ∀ k V, k ≤ budget → CostedDefectLegalSuffix W k V →
    stateTargetRank V ≤ 8

/-- Correct circuit-facing consequence required from the two-defect
quadratic-prefix analysis. -/
def CostedTwoDefectQuadraticPrefixes : Prop :=
  ∀ {j : Nat} (C : Circuit 10 12),
    j ≤ 12 →
    AllQuadraticPrefix C j →
    N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) = 2 →
    NoTargetCompletionWithin (N4.circuitFlag C j) (12 - j)

/-- Correct circuit-facing consequence required from the defect-at-most-one
quadratic-prefix analysis.  Unlike `FirstOrderSaturation`, this predicate
does not assert containment in one fixed target hyperplane. -/
def CostedFirstOrderQuadraticPrefixes : Prop :=
  ∀ {j : Nat} (C : Circuit 10 12),
    j ≤ 12 →
    AllQuadraticPrefix C j →
    N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) ≤ 1 →
    NoTargetCompletionWithin (N4.circuitFlag C j) (12 - j)

/-- The genuinely unresolved two-defect range after the sharp capacity-six
bound: a last quadratic prefix at gate ten or later closes by counting alone. -/
def CostedTwoDefectEarlyPrefixes : Prop :=
  ∀ {j : Nat} (C : Circuit 10 12),
    j ≤ 9 →
    AllQuadraticPrefix C j →
    N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) = 2 →
    NoTargetCompletionWithin (N4.circuitFlag C j) (12 - j)

/-- The genuinely unresolved first-order ranges after the sharp capacity
bounds: `j <= 8` at defect one and `j <= 6` at defect zero. -/
def CostedFirstOrderEarlyPrefixes : Prop :=
  (∀ {j : Nat} (C : Circuit 10 12),
      j ≤ 8 →
      AllQuadraticPrefix C j →
      N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) = 1 →
      NoTargetCompletionWithin (N4.circuitFlag C j) (12 - j)) ∧
  (∀ {j : Nat} (C : Circuit 10 12),
      j ≤ 6 →
      AllQuadraticPrefix C j →
      N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) = 0 →
      NoTargetCompletionWithin (N4.circuitFlag C j) (12 - j))

/-- A stable rank-eight theorem remains a sufficient, though deliberately
stronger, way to establish a bounded no-completion result. -/
theorem noTargetCompletionWithin_of_stableTargetRank
    {W : Submodule F₂ (ANF 10)} {budget : Nat}
    (hstable : StableTargetRank W 8) :
    NoTargetCompletionWithin W budget := by
  intro k V hk hreach
  exact hstable V hreach.toDefectLegal

/-- Counting alone excludes completion whenever the initial target rank plus
the available exact gate budget is at most eight. -/
theorem noTargetCompletionWithin_of_rank_add_budget_le_eight
    {W : Submodule F₂ (ANF 10)} {budget : Nat}
    (hAff : affine 10 ≤ W)
    (hbound : stateTargetRank W + budget ≤ 8) :
    NoTargetCompletionWithin W budget := by
  intro k V hk hreach
  exact (hreach.targetRank_le hAff).trans (by omega)

/-- The capacity-six theorem automatically closes every late two-defect
quadratic prefix. -/
theorem costedTwoDefectQuadraticPrefixes_of_early
    (hearly : CostedTwoDefectEarlyPrefixes) :
    CostedTwoDefectQuadraticPrefixes := by
  intro j C hj hall hdef
  by_cases hjearly : j ≤ 9
  · exact hearly C hjearly hall hdef
  · apply noTargetCompletionWithin_of_rank_add_budget_le_eight
      (affine_le_wireSpace C.gate)
    have hflat := quadraticPrefixFlattening_of_all_quadratic C hj hall
    have hQ : Module.finrank F₂
        (presentationDefect hflat.generator) ≤ 2 := by
      rw [quadraticPrefixFlattening_defect_eq_flagDefect C hflat hall]
      omega
    have ht := (flattenedPrefix_targetRank_le_capacity C hflat).trans
      (targetCapacity_le_six_of_finrank_le_two _ hQ)
    change N4.flagTargetRank (N4.circuitFlag C j) (mulTarget 5) +
        (12 - j) ≤ 8
    omega

/-- The sharp capacity-five and capacity-three bounds automatically close the
late first-order prefixes, leaving only the two early ranges above. -/
theorem costedFirstOrderQuadraticPrefixes_of_early
    (hearly : CostedFirstOrderEarlyPrefixes) :
    CostedFirstOrderQuadraticPrefixes := by
  intro j C hj hall hdef
  rcases hearly with ⟨hone, hzero⟩
  by_cases hdefZero : N4.flagDefectRank
      (N4.circuitFlag C j) (mulTarget 5) = 0
  · by_cases hjearly : j ≤ 6
    · exact hzero C hjearly hall hdefZero
    · apply noTargetCompletionWithin_of_rank_add_budget_le_eight
        (affine_le_wireSpace C.gate)
      have ht := allQuadraticPrefix_targetRank_le_three_of_flagDefect_eq_zero
        C hj hall hdefZero
      change N4.flagTargetRank (N4.circuitFlag C j) (mulTarget 5) +
          (12 - j) ≤ 8
      omega
  · have hdefOne : N4.flagDefectRank
        (N4.circuitFlag C j) (mulTarget 5) = 1 := by omega
    by_cases hjearly : j ≤ 8
    · exact hone C hjearly hall hdefOne
    · apply noTargetCompletionWithin_of_rank_add_budget_le_eight
        (affine_le_wireSpace C.gate)
      have ht := allQuadraticPrefix_targetRank_le_five_of_flagDefect_le_one
        C hj hall hdef
      change N4.flagTargetRank (N4.circuitFlag C j) (mulTarget 5) +
          (12 - j) ≤ 8
      omega

/-- The costed two-defect obligation follows from the previous unbounded
stable-suffix obligation whenever that stronger theorem is available. -/
theorem costedTwoDefectQuadraticPrefixes_of_stable
    (hstable : StableTwoDefectQuadraticPrefixes) :
    CostedTwoDefectQuadraticPrefixes := by
  intro j C hj hall hdef
  have hpositive := hstable C hj hall hdef
  intro k V hk hreach
  have hAff : affine 10 ≤ N4.circuitFlag C j :=
    affine_le_wireSpace C.gate
  have hbaseDef : N4.flagDefectRank
      (N4.circuitFlag C j) (mulTarget 5) ≤ 3 := by omega
  have hmissing := suffixPostGain_le_missingTarget hAff hbaseDef
  have hgain : suffixTargetGain (N4.circuitFlag C j) V ≤
      suffixPostGain (N4.circuitFlag C j) :=
    IsSuffixGain.le_suffixPostGain hAff
      ⟨V, hreach.toDefectLegal, rfl⟩
  have hmono := stateTargetRank_mono hAff hreach.start_le
  unfold suffixDeficit at hpositive
  unfold suffixTargetGain at hgain
  omega

/-- The exact last-prefix split: the two costed algebraic regime obligations
exclude every twelve-AND circuit. -/
theorem no_twelve_gate_circuit_of_costed_regime_closure
    (hTwo : CostedTwoDefectQuadraticPrefixes)
    (hFirst : CostedFirstOrderQuadraticPrefixes) :
    ¬ HasCircuit (Mul 5) 12 := by
  rintro ⟨⟨C, hC⟩⟩
  let j := lastQuadraticPrefix C
  have hj : j ≤ 12 := lastQuadraticPrefix_le C
  have hall : AllQuadraticPrefix C j := allQuadraticPrefix_last C
  have hdefLe : N4.flagDefectRank
      (N4.circuitFlag C j) (mulTarget 5) ≤ 2 :=
    lastQuadraticPrefix_defect_le_two C hC (by omega)
  have htail : CostedDefectLegalSuffix
      (N4.circuitFlag C j) (12 - j) C.finalWire := by
    simpa using circuitTail_costedDefectLegalSuffix C hC (by omega) hj
  have hfinal := stateTargetRank_final C hC
  by_cases hdefTwo : N4.flagDefectRank
      (N4.circuitFlag C j) (mulTarget 5) = 2
  · have hbound := hTwo C hj hall hdefTwo
      (12 - j) C.finalWire (by omega) htail
    omega
  · have hdefOne : N4.flagDefectRank
        (N4.circuitFlag C j) (mulTarget 5) ≤ 1 := by omega
    have hbound := hFirst C hj hall hdefOne
      (12 - j) C.finalWire (by omega) htail
    omega

/-- Conditional exact theorem with the false fixed-envelope premise removed
from its dependency surface. -/
theorem mc_mul_five_of_costed_regime_closure
    (hTwo : CostedTwoDefectQuadraticPrefixes)
    (hFirst : CostedFirstOrderQuadraticPrefixes) : MainStatement :=
  mc_mul_five_of_no_twelve
    (no_twelve_gate_circuit_of_costed_regime_closure hTwo hFirst)

end
end N5
end UnrestrictedBooleanMul
