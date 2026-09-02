import UnrestrictedBooleanMul.N5.LowDefectPrefix
import UnrestrictedBooleanMul.N5.StableTargetInduction
import UnrestrictedBooleanMul.N5.CompletionDeficit
import UnrestrictedBooleanMul.N5.MainInterface

/-!
# Final circuit regime closure

This module performs the exhaustive split at the last all-quadratic prefix.
It isolates the two remaining structural obligations without weakening them:
the combined two-defect suffix bound and the first-order stable-envelope
theorem.  Neither obligation contains a gate-count search.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The exact circuit-facing consequence of the stable two-defect theorem. -/
def StableTwoDefectQuadraticPrefixes : Prop :=
  ∀ {r j : Nat} (C : Circuit 10 r),
    j ≤ r →
    AllQuadraticPrefix C j →
    N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) = 2 →
    1 ≤ suffixDeficit (N4.circuitFlag C j)

/-- The algebraic saturation statement for every all-quadratic circuit prefix
of defect at most one.  Keeping the prefix in the interface preserves its
decomposable flattening data, which is essential to the one-defect anchor
argument. -/
def FirstOrderSaturation : Prop :=
  ∀ {r j : Nat} (C : Circuit 10 r),
    j ≤ r →
    AllQuadraticPrefix C j →
    N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) ≤ 1 →
    StableTargetSubspace (N4.circuitFlag C j) firstOrderEnvelopeState

/-- Once the two algebraic suffix obligations are available, the last-prefix
regime split excludes every twelve-gate circuit. -/
theorem no_twelve_gate_circuit_of_regime_closure
    (hTwo : StableTwoDefectQuadraticPrefixes)
    (hFirst : FirstOrderSaturation) :
    ¬ HasCircuit (Mul 5) 12 := by
  rintro ⟨⟨C, hC⟩⟩
  let j := lastQuadraticPrefix C
  let W := N4.circuitFlag C j
  have hj : j ≤ 12 := lastQuadraticPrefix_le C
  have hall : AllQuadraticPrefix C j := allQuadraticPrefix_last C
  have hWquad : W ≤ N4.quadraticANFSpace 10 := by
    exact N4.wireSpace_le_quadratic_of_prefix C.gate hall
  have hWaff : affine 10 ≤ W := affine_le_wireSpace C.gate
  have hdefLe : N4.flagDefectRank W (mulTarget 5) ≤ 2 := by
    exact lastQuadraticPrefix_defect_le_two C hC (by omega)
  by_cases hdefTwo : N4.flagDefectRank W (mulTarget 5) = 2
  · have hpositive : 1 ≤ suffixDeficit W :=
      hTwo C hj hall hdefTwo
    exact no_circuit_completion_of_positive_suffixDeficit
      C hC (by omega) hj hpositive
  · have hdefOne : N4.flagDefectRank W (mulTarget 5) ≤ 1 := by omega
    have hstableSubspace :
        StableTargetSubspace W firstOrderEnvelopeState :=
      hFirst C hj hall hdefOne
    have hstableRank : StableTargetRank W 8 :=
      stableFirstOrder_targetRank hWaff hstableSubspace
    have htarget : stateTargetRank W ≤ 8 :=
      hstableRank W (.refl (by omega))
    have hpositive : 1 ≤ suffixDeficit W :=
      suffixDeficit_positive_of_stableTargetRank_eight
        hWaff (by omega) htarget hstableRank
    exact no_circuit_completion_of_positive_suffixDeficit
      C hC (by omega) hj hpositive

/-- Conditional exact theorem with no further circuit bookkeeping hidden in
the final statement. -/
theorem mc_mul_five_of_regime_closure
    (hTwo : StableTwoDefectQuadraticPrefixes)
    (hFirst : FirstOrderSaturation) : MainStatement :=
  mc_mul_five_of_no_twelve
    (no_twelve_gate_circuit_of_regime_closure hTwo hFirst)

end
end N5
end UnrestrictedBooleanMul
