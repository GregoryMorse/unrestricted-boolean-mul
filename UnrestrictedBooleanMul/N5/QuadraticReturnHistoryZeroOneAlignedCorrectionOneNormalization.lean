import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedCorrectionOneRaw
import UnrestrictedBooleanMul.N3Certificate
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedBase

/-!
# Affine normalization bridge: `ZeroOneAlignedCorrectionOne`

The reduced unit certificate is related here to the original
return-history generators by the exact affine substitutions produced
during certificate reduction.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Original semantic generators selected by the `ZeroOneAlignedCorrectionOne` unit certificate. -/
def zeroOneAlignedCorrectionOneOriginalConstraint (v : Fin 71 → F₂) : Fin 16 → F₂ :=
  fun i => zeroOneAlignedBaseConstraint v
    ((![
      8, 9, 10, 11, 12, 14, 17, 18, 23, 24, 28, 29, 30, 31, 32, 33] : Fin 16 → Fin 34) i)

/-- The affine substitution ledger used by the reduced certificate. -/
structure ZeroOneAlignedCorrectionOneSubstitutions (v : Fin 71 → F₂) : Prop where
  x1 : v 21 = 0
  x2 : v 22 = 0
  x3 : v 23 = 0
  x4 : v 24 = 0
  x6 : v 26 = 0
  x7 : v 27 = 0
  x8 : v 28 = 0
  x9 : v 29 = 0
  ell1 : v 1 = 0
  ell2 : v 2 = 0
  ell4 : v 4 = 0
  ell6 : v 6 = 1
  ell7 : v 7 = 0
  y1 : v 31 = 1
  y2 : v 32 = 0
  y4 : v 34 = 0
  y6 : v 36 = 0
  y7 : v 37 = 0
  correctionReturn0 : v 70 = 1
  correctionTarget6 : v 68 = 1 + v 11 + v 42
  correctionTarget7 : v 69 = 1 + v 11 + v 14 + v 42 + v 45
  correctionTarget4 : v 66 = v 12 + v 43
  factorLinear2 : v 43 = v 12
  correctionTarget1 : v 63 = 0
  factorLinear4 : v 45 = 1 + v 11 + v 14 + v 42
  factorLinear7 : v 48 = v 17
  factorLinear1 : v 42 = 1 + v 11
  correctionTarget5 : v 67 = 0
  correctionTarget2 : v 64 = 0

/-- Under the exact substitution ledger, each reduced generator is
the corresponding original history generator. -/
theorem zeroOneAlignedCorrectionOneReducedConstraint_eq_original
    (v : Fin 71 → F₂)
    (h : ZeroOneAlignedCorrectionOneSubstitutions v)
    (i : Fin 16) :
    zeroOneAlignedCorrectionOneReducedConstraint v i = zeroOneAlignedCorrectionOneOriginalConstraint v i := by
  fin_cases i <;>
    simp [zeroOneAlignedCorrectionOneReducedConstraint, zeroOneAlignedCorrectionOneOriginalConstraint,
      zeroOneAlignedBaseConstraint, h.x1, h.x2, h.x3, h.x4, h.x6, h.x7, h.x8, h.x9, h.ell1, h.ell2, h.ell4, h.ell6, h.ell7, h.y1, h.y2, h.y4, h.y6, h.y7, h.correctionReturn0, h.correctionTarget6, h.correctionTarget7, h.correctionTarget4, h.factorLinear2, h.correctionTarget1, h.factorLinear4, h.factorLinear7, h.factorLinear1, h.correctionTarget5, h.correctionTarget2] <;>
    (try ring_nf) <;>
    (try simp [N3Certificate.pow_two_f2, N3Certificate.two_eq_zero_f2,
      CharTwo.ofNat_eq_mod]) <;>
    (try ring_nf) <;>
    (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])

/-- Original selected equations plus the substitution ledger are
inconsistent. -/
theorem zeroOneAlignedCorrectionOne_inconsistent_of_original
    (v : Fin 71 → F₂)
    (hsub : ZeroOneAlignedCorrectionOneSubstitutions v)
    (hzero : ∀ i : Fin 16, zeroOneAlignedCorrectionOneOriginalConstraint v i = 0) :
    False := by
  apply zeroOne_aligned_correctionOne_reduced_inconsistent v
  intro i
  rw [zeroOneAlignedCorrectionOneReducedConstraint_eq_original v hsub i]
  exact hzero i

end
end UnrestrictedBooleanMul.N5
