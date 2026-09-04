import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedCorrectionZeroRaw
import UnrestrictedBooleanMul.N3Certificate
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedBase

/-!
# Affine normalization bridge: `OneOneAlignedCorrectionZero`

The reduced unit certificate is related here to the original
return-history generators by the exact affine substitutions produced
during certificate reduction.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Original semantic generators selected by the `OneOneAlignedCorrectionZero` unit certificate. -/
def oneOneAlignedCorrectionZeroOriginalConstraint (v : Fin 71 → F₂) : Fin 13 → F₂ :=
  fun i => oneOneAlignedBaseConstraint v
    ((![
      8, 9, 10, 11, 12, 16, 17, 25, 26, 27, 28, 29, 30] : Fin 13 → Fin 31) i)

/-- The affine substitution ledger used by the reduced certificate. -/
structure OneOneAlignedCorrectionZeroSubstitutions (v : Fin 71 → F₂) : Prop where
  y1 : v 31 = 1
  y2 : v 32 = 0
  y3 : v 33 = v 23
  y4 : v 34 = 0
  y6 : v 36 = 0
  y7 : v 37 = 0
  y8 : v 38 = v 28
  y9 : v 39 = v 29
  m1 : v 11 = 0
  m2 : v 12 = 0
  m4 : v 14 = 0
  m6 : v 16 = 1
  m7 : v 17 = 0
  x1 : v 21 = 1
  x2 : v 22 = 0
  x4 : v 24 = 0
  x6 : v 26 = 0
  x7 : v 27 = 0
  correctionReturn0 : v 70 = 0
  correctionTarget6 : v 68 = v 1 + v 42
  correctionTarget7 : v 69 = v 1 + v 4 + v 42 + v 45
  correctionTarget4 : v 66 = v 2 + v 43
  factorLinear2 : v 43 = v 2
  correctionTarget1 : v 63 = 0
  factorLinear4 : v 45 = v 1 + v 4 + v 42
  factorLinear7 : v 48 = v 7
  factorLinear1 : v 42 = v 1
  correctionTarget5 : v 67 = 0
  correctionTarget2 : v 64 = 0

/-- Under the exact substitution ledger, each reduced generator is
the corresponding original history generator. -/
theorem oneOneAlignedCorrectionZeroReducedConstraint_eq_original
    (v : Fin 71 → F₂)
    (h : OneOneAlignedCorrectionZeroSubstitutions v)
    (i : Fin 13) :
    oneOneAlignedCorrectionZeroReducedConstraint v i = oneOneAlignedCorrectionZeroOriginalConstraint v i := by
  fin_cases i <;>
    simp [oneOneAlignedCorrectionZeroReducedConstraint, oneOneAlignedCorrectionZeroOriginalConstraint,
      oneOneAlignedBaseConstraint, h.y1, h.y2, h.y3, h.y4, h.y6, h.y7, h.y8, h.y9, h.m1, h.m2, h.m4, h.m6, h.m7, h.x1, h.x2, h.x4, h.x6, h.x7, h.correctionReturn0, h.correctionTarget6, h.correctionTarget7, h.correctionTarget4, h.factorLinear2, h.correctionTarget1, h.factorLinear4, h.factorLinear7, h.factorLinear1, h.correctionTarget5, h.correctionTarget2] <;>
    (try ring_nf) <;>
    (try simp [N3Certificate.pow_two_f2, N3Certificate.two_eq_zero_f2,
      CharTwo.ofNat_eq_mod]) <;>
    (try ring_nf) <;>
    (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])

/-- Original selected equations plus the substitution ledger are
inconsistent. -/
theorem oneOneAlignedCorrectionZero_inconsistent_of_original
    (v : Fin 71 → F₂)
    (hsub : OneOneAlignedCorrectionZeroSubstitutions v)
    (hzero : ∀ i : Fin 13, oneOneAlignedCorrectionZeroOriginalConstraint v i = 0) :
    False := by
  apply oneOne_aligned_correctionZero_reduced_inconsistent v
  intro i
  rw [oneOneAlignedCorrectionZeroReducedConstraint_eq_original v hsub i]
  exact hzero i

end
end UnrestrictedBooleanMul.N5
