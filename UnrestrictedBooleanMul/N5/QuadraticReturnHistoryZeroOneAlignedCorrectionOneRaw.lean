import UnrestrictedBooleanMul.ANF

/-!
# Reduced aligned certificate: `ZeroOneAlignedCorrectionOne`

This generated module checks a sparse Boolean-polynomial unit
identity.  External algebra was used only to discover the stored
multipliers; Lean replays the identity without extra axioms.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192

/-- The 16 reduced semantic generators in this unit certificate. -/
def zeroOneAlignedCorrectionOneReducedConstraint (v : Fin 71 → F₂) : Fin 16 → F₂ :=
  ![
    -- product-high-0x023
    v 5 * v 10 + v 5 * v 10 * v 11 + v 0 * v 15 + v 0 * v 11 * v 15 + v 15 * v 20 + v 11 * v 15 * v 20 + v 10 * v 25 + v 10 * v 11 * v 25 + v 5 * v 30 + v 5 * v 11 * v 30 + v 25 * v 30 + v 11 * v 25 * v 30 + v 0 * v 35 + v 0 * v 11 * v 35 + v 20 * v 35 + v 11 * v 20 * v 35 + v 5 * v 41 + v 5 * v 11 * v 41 + v 25 * v 41 + v 11 * v 25 * v 41 + v 0 * v 46 + v 0 * v 11 * v 46 + v 20 * v 46 + v 11 * v 20 * v 46 + v 53 + v 62 + v 11 * v 62 + v 65 + v 41 * v 65,
    -- product-high-0x025
    v 5 * v 10 * v 12 + v 0 * v 12 * v 15 + v 12 * v 15 * v 20 + v 10 * v 12 * v 25 + v 5 * v 12 * v 30 + v 12 * v 25 * v 30 + v 0 * v 12 * v 35 + v 12 * v 20 * v 35 + v 5 * v 12 * v 41 + v 12 * v 25 * v 41 + v 0 * v 12 * v 46 + v 12 * v 20 * v 46 + v 54 + v 12 * v 62,
    -- product-high-0x043
    v 10 + v 10 * v 11 + v 0 * v 16 + v 0 * v 11 * v 16 + v 16 * v 20 + v 11 * v 16 * v 20 + v 30 + v 11 * v 30 + v 41 + v 11 * v 41 + v 0 * v 47 + v 0 * v 11 * v 47 + v 20 * v 47 + v 11 * v 20 * v 47 + v 65 + v 11 * v 65,
    -- product-high-0x061
    1 + v 10 + v 15 + v 16 + v 0 * v 16 + v 5 * v 16 + v 16 * v 20 + v 16 * v 25 + v 30 + v 35 + v 40 + v 41 + v 15 * v 41 + v 5 * v 16 * v 41 + v 16 * v 25 * v 41 + v 35 * v 41 + v 46 + v 10 * v 46 + v 0 * v 16 * v 46 + v 16 * v 20 * v 46 + v 30 * v 46 + v 47 + v 0 * v 47 + v 5 * v 47 + v 5 * v 10 * v 47 + v 0 * v 15 * v 47 + v 20 * v 47 + v 15 * v 20 * v 47 + v 25 * v 47 + v 10 * v 25 * v 47 + v 5 * v 30 * v 47 + v 25 * v 30 * v 47 + v 0 * v 35 * v 47 + v 20 * v 35 * v 47 + v 58 + v 47 * v 62 + v 65 + v 46 * v 65,
    -- product-high-0x062
    v 15 + v 11 * v 15 + v 5 * v 16 + v 5 * v 11 * v 16 + v 16 * v 25 + v 11 * v 16 * v 25 + v 35 + v 11 * v 35 + v 46 + v 11 * v 46 + v 5 * v 47 + v 5 * v 11 * v 47 + v 25 * v 47 + v 11 * v 25 * v 47 + v 47 * v 65,
    -- product-high-0x064
    v 12 * v 15 + v 5 * v 12 * v 16 + v 12 * v 16 * v 25 + v 12 * v 35 + v 12 * v 46 + v 5 * v 12 * v 47 + v 12 * v 25 * v 47,
    -- product-high-0x0a1
    v 5 * v 10 * v 17 + v 0 * v 15 * v 17 + v 15 * v 17 * v 20 + v 10 * v 17 * v 25 + v 5 * v 17 * v 30 + v 17 * v 25 * v 30 + v 0 * v 17 * v 35 + v 17 * v 20 * v 35 + v 5 * v 17 * v 41 + v 17 * v 25 * v 41 + v 0 * v 17 * v 46 + v 17 * v 20 * v 46 + v 59 + v 17 * v 62,
    -- product-high-0x0a2
    v 17 * v 65,
    -- product-high-0x0c1
    v 10 * v 17 + v 0 * v 16 * v 17 + v 16 * v 17 * v 20 + v 17 * v 30 + v 17 * v 41 + v 0 * v 17 * v 47 + v 17 * v 20 * v 47 + v 17 * v 65,
    -- product-high-0x0e0
    v 15 * v 17 + v 5 * v 16 * v 17 + v 16 * v 17 * v 25 + v 17 * v 35 + v 17 * v 46 + v 5 * v 17 * v 47 + v 17 * v 25 * v 47,
    -- quotient-6
    v 5 * v 12 + v 5 * v 12 * v 15 + v 0 * v 17 + v 0 * v 10 * v 17 + v 10 * v 17 * v 20 + v 12 * v 15 * v 25 + v 0 * v 17 * v 30 + v 17 * v 20 * v 30 + v 5 * v 12 * v 35 + v 12 * v 25 * v 35 + v 5 * v 12 * v 40 + v 0 * v 17 * v 40 + v 17 * v 20 * v 40 + v 12 * v 25 * v 40 + v 0 * v 17 * v 41 + v 17 * v 20 * v 41 + v 5 * v 12 * v 46 + v 12 * v 25 * v 46 + v 17 * v 52 + v 46 * v 54 + v 12 * v 57 + v 41 * v 59,
    -- quotient-13
    v 11 + v 5 * v 12 + v 5 * v 12 * v 15 + v 16 + v 11 * v 16 + v 12 * v 15 * v 25 + v 5 * v 12 * v 35 + v 12 * v 25 * v 35 + v 40 + v 11 * v 40 + v 5 * v 12 * v 40 + v 12 * v 25 * v 40 + v 5 * v 12 * v 46 + v 12 * v 25 * v 46 + v 47 + v 11 * v 47 + v 47 * v 53 + v 46 * v 54 + v 12 * v 57 + v 58 + v 11 * v 58,
    -- quotient-14
    v 13 * v 25 + v 5 * v 33 + v 25 * v 33 + v 3 * v 35 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 13 * v 25 * v 40 + v 5 * v 33 * v 40 + v 25 * v 33 * v 40 + v 3 * v 35 * v 40 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 13 * v 25 * v 44 + v 15 * v 25 * v 44 + v 5 * v 33 * v 44 + v 25 * v 33 * v 44 + v 3 * v 35 * v 44 + v 5 * v 35 * v 44 + v 25 * v 35 * v 44 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 13 * v 25 * v 46 + v 3 * v 33 * v 46 + v 5 * v 33 * v 46 + v 25 * v 33 * v 46 + v 3 * v 35 * v 46 + v 17 * v 53 + v 46 * v 55 + v 44 * v 57 + v 59 + v 11 * v 59,
    -- quotient-20
    v 12 + v 12 * v 16 + v 13 * v 25 + v 5 * v 33 + v 25 * v 33 + v 3 * v 35 + v 12 * v 40 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 13 * v 25 * v 40 + v 5 * v 33 * v 40 + v 25 * v 33 * v 40 + v 3 * v 35 * v 40 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 13 * v 25 * v 44 + v 15 * v 25 * v 44 + v 5 * v 33 * v 44 + v 25 * v 33 * v 44 + v 3 * v 35 * v 44 + v 5 * v 35 * v 44 + v 25 * v 35 * v 44 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 13 * v 25 * v 46 + v 3 * v 33 * v 46 + v 5 * v 33 * v 46 + v 25 * v 33 * v 46 + v 3 * v 35 * v 46 + v 12 * v 47 + v 47 * v 54 + v 46 * v 55 + v 44 * v 57 + v 12 * v 58,
    -- quotient-36
    v 5 * v 17 + v 5 * v 15 * v 17 + v 15 * v 17 * v 25 + v 5 * v 17 * v 35 + v 17 * v 25 * v 35 + v 5 * v 17 * v 40 + v 17 * v 25 * v 40 + v 5 * v 17 * v 46 + v 17 * v 25 * v 46 + v 17 * v 57 + v 46 * v 59,
    -- quotient-39
    v 17 + v 16 * v 17 + v 17 * v 40 + v 17 * v 47 + v 17 * v 58 + v 47 * v 59
  ]

private def zeroOneAlignedCorrectionOneReducedMultiplier (v : Fin 71 → F₂) : Fin 16 → F₂ :=
  ![
    -- product-high-0x023
    v 5 * v 17 + v 17 * v 25 + v 47,
    -- product-high-0x025
    v 17 * v 46 + v 5 * v 17 * v 47 + v 17 * v 25 * v 47,
    -- product-high-0x043
    1 + v 46,
    -- product-high-0x061
    1 + v 11,
    -- product-high-0x062
    1 + v 41,
    -- product-high-0x064
    v 17,
    -- product-high-0x0a1
    v 5 * v 17 + v 5 * v 11 * v 17 + v 17 * v 25 + v 11 * v 17 * v 25 + v 41 + v 17 * v 41 + v 12 * v 46 + v 5 * v 12 * v 47 + v 12 * v 25 * v 47,
    -- product-high-0x0a2
    1 + v 5 + v 17 + v 25 + v 5 * v 41 + v 25 * v 41,
    -- product-high-0x0c1
    1 + v 17,
    -- product-high-0x0e0
    v 12,
    -- quotient-6
    1 + v 17,
    -- quotient-13
    1,
    -- quotient-14
    v 5 * v 17 + v 17 * v 25,
    -- quotient-20
    v 5 * v 17 + v 17 * v 25,
    -- quotient-36
    v 12,
    -- quotient-39
    v 5 * v 12 + v 12 * v 25
  ]

private def zeroOneAlignedCorrectionOneReducedProduct (v : Fin 71 → F₂) : Fin 16 → F₂ :=
  ![
    -- product-high-0x023
    v 5 * v 10 * v 17 + v 5 * v 10 * v 11 * v 17 + v 0 * v 5 * v 15 * v 17 + v 0 * v 5 * v 11 * v 15 * v 17 + v 5 * v 15 * v 17 * v 20 + v 5 * v 11 * v 15 * v 17 * v 20 + v 10 * v 17 * v 25 + v 10 * v 11 * v 17 * v 25 + v 0 * v 15 * v 17 * v 25 + v 0 * v 11 * v 15 * v 17 * v 25 + v 15 * v 17 * v 20 * v 25 + v 11 * v 15 * v 17 * v 20 * v 25 + v 5 * v 17 * v 30 + v 5 * v 11 * v 17 * v 30 + v 17 * v 25 * v 30 + v 11 * v 17 * v 25 * v 30 + v 0 * v 5 * v 17 * v 35 + v 0 * v 5 * v 11 * v 17 * v 35 + v 5 * v 17 * v 20 * v 35 + v 5 * v 11 * v 17 * v 20 * v 35 + v 0 * v 17 * v 25 * v 35 + v 0 * v 11 * v 17 * v 25 * v 35 + v 17 * v 20 * v 25 * v 35 + v 11 * v 17 * v 20 * v 25 * v 35 + v 5 * v 17 * v 41 + v 5 * v 11 * v 17 * v 41 + v 17 * v 25 * v 41 + v 11 * v 17 * v 25 * v 41 + v 0 * v 5 * v 17 * v 46 + v 0 * v 5 * v 11 * v 17 * v 46 + v 5 * v 17 * v 20 * v 46 + v 5 * v 11 * v 17 * v 20 * v 46 + v 0 * v 17 * v 25 * v 46 + v 0 * v 11 * v 17 * v 25 * v 46 + v 17 * v 20 * v 25 * v 46 + v 11 * v 17 * v 20 * v 25 * v 46 + v 5 * v 10 * v 47 + v 5 * v 10 * v 11 * v 47 + v 0 * v 15 * v 47 + v 0 * v 11 * v 15 * v 47 + v 15 * v 20 * v 47 + v 11 * v 15 * v 20 * v 47 + v 10 * v 25 * v 47 + v 10 * v 11 * v 25 * v 47 + v 5 * v 30 * v 47 + v 5 * v 11 * v 30 * v 47 + v 25 * v 30 * v 47 + v 11 * v 25 * v 30 * v 47 + v 0 * v 35 * v 47 + v 0 * v 11 * v 35 * v 47 + v 20 * v 35 * v 47 + v 11 * v 20 * v 35 * v 47 + v 5 * v 41 * v 47 + v 5 * v 11 * v 41 * v 47 + v 25 * v 41 * v 47 + v 11 * v 25 * v 41 * v 47 + v 0 * v 46 * v 47 + v 0 * v 11 * v 46 * v 47 + v 20 * v 46 * v 47 + v 11 * v 20 * v 46 * v 47 + v 5 * v 17 * v 53 + v 17 * v 25 * v 53 + v 47 * v 53 + v 5 * v 17 * v 62 + v 5 * v 11 * v 17 * v 62 + v 17 * v 25 * v 62 + v 11 * v 17 * v 25 * v 62 + v 47 * v 62 + v 11 * v 47 * v 62 + v 5 * v 17 * v 65 + v 17 * v 25 * v 65 + v 5 * v 17 * v 41 * v 65 + v 17 * v 25 * v 41 * v 65 + v 47 * v 65 + v 41 * v 47 * v 65,
    -- product-high-0x025
    v 0 * v 12 * v 17 * v 46 + v 5 * v 10 * v 12 * v 17 * v 46 + v 0 * v 12 * v 15 * v 17 * v 46 + v 12 * v 17 * v 20 * v 46 + v 12 * v 15 * v 17 * v 20 * v 46 + v 10 * v 12 * v 17 * v 25 * v 46 + v 5 * v 12 * v 17 * v 30 * v 46 + v 12 * v 17 * v 25 * v 30 * v 46 + v 0 * v 12 * v 17 * v 35 * v 46 + v 12 * v 17 * v 20 * v 35 * v 46 + v 5 * v 12 * v 17 * v 41 * v 46 + v 12 * v 17 * v 25 * v 41 * v 46 + v 5 * v 10 * v 12 * v 17 * v 47 + v 0 * v 5 * v 12 * v 15 * v 17 * v 47 + v 5 * v 12 * v 15 * v 17 * v 20 * v 47 + v 10 * v 12 * v 17 * v 25 * v 47 + v 0 * v 12 * v 15 * v 17 * v 25 * v 47 + v 12 * v 15 * v 17 * v 20 * v 25 * v 47 + v 5 * v 12 * v 17 * v 30 * v 47 + v 12 * v 17 * v 25 * v 30 * v 47 + v 0 * v 5 * v 12 * v 17 * v 35 * v 47 + v 5 * v 12 * v 17 * v 20 * v 35 * v 47 + v 0 * v 12 * v 17 * v 25 * v 35 * v 47 + v 12 * v 17 * v 20 * v 25 * v 35 * v 47 + v 5 * v 12 * v 17 * v 41 * v 47 + v 12 * v 17 * v 25 * v 41 * v 47 + v 0 * v 5 * v 12 * v 17 * v 46 * v 47 + v 5 * v 12 * v 17 * v 20 * v 46 * v 47 + v 0 * v 12 * v 17 * v 25 * v 46 * v 47 + v 12 * v 17 * v 20 * v 25 * v 46 * v 47 + v 17 * v 46 * v 54 + v 5 * v 17 * v 47 * v 54 + v 17 * v 25 * v 47 * v 54 + v 12 * v 17 * v 46 * v 62 + v 5 * v 12 * v 17 * v 47 * v 62 + v 12 * v 17 * v 25 * v 47 * v 62,
    -- product-high-0x043
    v 10 + v 10 * v 11 + v 0 * v 16 + v 0 * v 11 * v 16 + v 16 * v 20 + v 11 * v 16 * v 20 + v 30 + v 11 * v 30 + v 41 + v 11 * v 41 + v 10 * v 46 + v 10 * v 11 * v 46 + v 0 * v 16 * v 46 + v 0 * v 11 * v 16 * v 46 + v 16 * v 20 * v 46 + v 11 * v 16 * v 20 * v 46 + v 30 * v 46 + v 11 * v 30 * v 46 + v 41 * v 46 + v 11 * v 41 * v 46 + v 0 * v 47 + v 0 * v 11 * v 47 + v 20 * v 47 + v 11 * v 20 * v 47 + v 0 * v 46 * v 47 + v 0 * v 11 * v 46 * v 47 + v 20 * v 46 * v 47 + v 11 * v 20 * v 46 * v 47 + v 65 + v 11 * v 65 + v 46 * v 65 + v 11 * v 46 * v 65,
    -- product-high-0x061
    1 + v 10 + v 11 + v 10 * v 11 + v 15 + v 11 * v 15 + v 16 + v 0 * v 16 + v 5 * v 16 + v 11 * v 16 + v 0 * v 11 * v 16 + v 5 * v 11 * v 16 + v 16 * v 20 + v 11 * v 16 * v 20 + v 16 * v 25 + v 11 * v 16 * v 25 + v 30 + v 11 * v 30 + v 35 + v 11 * v 35 + v 40 + v 11 * v 40 + v 41 + v 11 * v 41 + v 15 * v 41 + v 11 * v 15 * v 41 + v 5 * v 16 * v 41 + v 5 * v 11 * v 16 * v 41 + v 16 * v 25 * v 41 + v 11 * v 16 * v 25 * v 41 + v 35 * v 41 + v 11 * v 35 * v 41 + v 46 + v 10 * v 46 + v 11 * v 46 + v 10 * v 11 * v 46 + v 0 * v 16 * v 46 + v 0 * v 11 * v 16 * v 46 + v 16 * v 20 * v 46 + v 11 * v 16 * v 20 * v 46 + v 30 * v 46 + v 11 * v 30 * v 46 + v 47 + v 0 * v 47 + v 5 * v 47 + v 5 * v 10 * v 47 + v 11 * v 47 + v 0 * v 11 * v 47 + v 5 * v 11 * v 47 + v 5 * v 10 * v 11 * v 47 + v 0 * v 15 * v 47 + v 0 * v 11 * v 15 * v 47 + v 20 * v 47 + v 11 * v 20 * v 47 + v 15 * v 20 * v 47 + v 11 * v 15 * v 20 * v 47 + v 25 * v 47 + v 10 * v 25 * v 47 + v 11 * v 25 * v 47 + v 10 * v 11 * v 25 * v 47 + v 5 * v 30 * v 47 + v 5 * v 11 * v 30 * v 47 + v 25 * v 30 * v 47 + v 11 * v 25 * v 30 * v 47 + v 0 * v 35 * v 47 + v 0 * v 11 * v 35 * v 47 + v 20 * v 35 * v 47 + v 11 * v 20 * v 35 * v 47 + v 58 + v 11 * v 58 + v 47 * v 62 + v 11 * v 47 * v 62 + v 65 + v 11 * v 65 + v 46 * v 65 + v 11 * v 46 * v 65,
    -- product-high-0x062
    v 15 + v 11 * v 15 + v 5 * v 16 + v 5 * v 11 * v 16 + v 16 * v 25 + v 11 * v 16 * v 25 + v 35 + v 11 * v 35 + v 15 * v 41 + v 11 * v 15 * v 41 + v 5 * v 16 * v 41 + v 5 * v 11 * v 16 * v 41 + v 16 * v 25 * v 41 + v 11 * v 16 * v 25 * v 41 + v 35 * v 41 + v 11 * v 35 * v 41 + v 46 + v 11 * v 46 + v 41 * v 46 + v 11 * v 41 * v 46 + v 5 * v 47 + v 5 * v 11 * v 47 + v 25 * v 47 + v 11 * v 25 * v 47 + v 5 * v 41 * v 47 + v 5 * v 11 * v 41 * v 47 + v 25 * v 41 * v 47 + v 11 * v 25 * v 41 * v 47 + v 47 * v 65 + v 41 * v 47 * v 65,
    -- product-high-0x064
    v 12 * v 15 * v 17 + v 5 * v 12 * v 16 * v 17 + v 12 * v 16 * v 17 * v 25 + v 12 * v 17 * v 35 + v 12 * v 17 * v 46 + v 5 * v 12 * v 17 * v 47 + v 12 * v 17 * v 25 * v 47,
    -- product-high-0x0a1
    v 5 * v 10 * v 17 + v 5 * v 10 * v 11 * v 17 + v 0 * v 5 * v 15 * v 17 + v 0 * v 5 * v 11 * v 15 * v 17 + v 5 * v 15 * v 17 * v 20 + v 5 * v 11 * v 15 * v 17 * v 20 + v 10 * v 17 * v 25 + v 10 * v 11 * v 17 * v 25 + v 0 * v 15 * v 17 * v 25 + v 0 * v 11 * v 15 * v 17 * v 25 + v 15 * v 17 * v 20 * v 25 + v 11 * v 15 * v 17 * v 20 * v 25 + v 5 * v 17 * v 30 + v 5 * v 11 * v 17 * v 30 + v 17 * v 25 * v 30 + v 11 * v 17 * v 25 * v 30 + v 0 * v 5 * v 17 * v 35 + v 0 * v 5 * v 11 * v 17 * v 35 + v 5 * v 17 * v 20 * v 35 + v 5 * v 11 * v 17 * v 20 * v 35 + v 0 * v 17 * v 25 * v 35 + v 0 * v 11 * v 17 * v 25 * v 35 + v 17 * v 20 * v 25 * v 35 + v 11 * v 17 * v 20 * v 25 * v 35 + v 5 * v 17 * v 41 + v 5 * v 11 * v 17 * v 41 + v 17 * v 25 * v 41 + v 11 * v 17 * v 25 * v 41 + v 0 * v 5 * v 17 * v 46 + v 0 * v 5 * v 11 * v 17 * v 46 + v 0 * v 12 * v 17 * v 46 + v 5 * v 10 * v 12 * v 17 * v 46 + v 0 * v 12 * v 15 * v 17 * v 46 + v 5 * v 17 * v 20 * v 46 + v 5 * v 11 * v 17 * v 20 * v 46 + v 12 * v 17 * v 20 * v 46 + v 12 * v 15 * v 17 * v 20 * v 46 + v 0 * v 17 * v 25 * v 46 + v 0 * v 11 * v 17 * v 25 * v 46 + v 10 * v 12 * v 17 * v 25 * v 46 + v 17 * v 20 * v 25 * v 46 + v 11 * v 17 * v 20 * v 25 * v 46 + v 5 * v 12 * v 17 * v 30 * v 46 + v 12 * v 17 * v 25 * v 30 * v 46 + v 0 * v 12 * v 17 * v 35 * v 46 + v 12 * v 17 * v 20 * v 35 * v 46 + v 5 * v 12 * v 17 * v 41 * v 46 + v 12 * v 17 * v 25 * v 41 * v 46 + v 5 * v 10 * v 12 * v 17 * v 47 + v 0 * v 5 * v 12 * v 15 * v 17 * v 47 + v 5 * v 12 * v 15 * v 17 * v 20 * v 47 + v 10 * v 12 * v 17 * v 25 * v 47 + v 0 * v 12 * v 15 * v 17 * v 25 * v 47 + v 12 * v 15 * v 17 * v 20 * v 25 * v 47 + v 5 * v 12 * v 17 * v 30 * v 47 + v 12 * v 17 * v 25 * v 30 * v 47 + v 0 * v 5 * v 12 * v 17 * v 35 * v 47 + v 5 * v 12 * v 17 * v 20 * v 35 * v 47 + v 0 * v 12 * v 17 * v 25 * v 35 * v 47 + v 12 * v 17 * v 20 * v 25 * v 35 * v 47 + v 5 * v 12 * v 17 * v 41 * v 47 + v 12 * v 17 * v 25 * v 41 * v 47 + v 0 * v 5 * v 12 * v 17 * v 46 * v 47 + v 5 * v 12 * v 17 * v 20 * v 46 * v 47 + v 0 * v 12 * v 17 * v 25 * v 46 * v 47 + v 12 * v 17 * v 20 * v 25 * v 46 * v 47 + v 5 * v 17 * v 59 + v 5 * v 11 * v 17 * v 59 + v 17 * v 25 * v 59 + v 11 * v 17 * v 25 * v 59 + v 41 * v 59 + v 17 * v 41 * v 59 + v 12 * v 46 * v 59 + v 5 * v 12 * v 47 * v 59 + v 12 * v 25 * v 47 * v 59 + v 5 * v 17 * v 62 + v 5 * v 11 * v 17 * v 62 + v 17 * v 25 * v 62 + v 11 * v 17 * v 25 * v 62 + v 12 * v 17 * v 46 * v 62 + v 5 * v 12 * v 17 * v 47 * v 62 + v 12 * v 17 * v 25 * v 47 * v 62,
    -- product-high-0x0a2
    v 5 * v 17 * v 65 + v 17 * v 25 * v 65 + v 5 * v 17 * v 41 * v 65 + v 17 * v 25 * v 41 * v 65,
    -- product-high-0x0c1
    0,
    -- product-high-0x0e0
    v 12 * v 15 * v 17 + v 5 * v 12 * v 16 * v 17 + v 12 * v 16 * v 17 * v 25 + v 12 * v 17 * v 35 + v 12 * v 17 * v 46 + v 5 * v 12 * v 17 * v 47 + v 12 * v 17 * v 25 * v 47,
    -- quotient-6
    v 5 * v 12 + v 5 * v 12 * v 15 + v 5 * v 12 * v 17 + v 5 * v 12 * v 15 * v 17 + v 12 * v 15 * v 25 + v 12 * v 15 * v 17 * v 25 + v 5 * v 12 * v 35 + v 5 * v 12 * v 17 * v 35 + v 12 * v 25 * v 35 + v 12 * v 17 * v 25 * v 35 + v 5 * v 12 * v 40 + v 5 * v 12 * v 17 * v 40 + v 12 * v 25 * v 40 + v 12 * v 17 * v 25 * v 40 + v 5 * v 12 * v 46 + v 5 * v 12 * v 17 * v 46 + v 12 * v 25 * v 46 + v 12 * v 17 * v 25 * v 46 + v 46 * v 54 + v 17 * v 46 * v 54 + v 12 * v 57 + v 12 * v 17 * v 57 + v 41 * v 59 + v 17 * v 41 * v 59,
    -- quotient-13
    v 11 + v 5 * v 12 + v 5 * v 12 * v 15 + v 16 + v 11 * v 16 + v 12 * v 15 * v 25 + v 5 * v 12 * v 35 + v 12 * v 25 * v 35 + v 40 + v 11 * v 40 + v 5 * v 12 * v 40 + v 12 * v 25 * v 40 + v 5 * v 12 * v 46 + v 12 * v 25 * v 46 + v 47 + v 11 * v 47 + v 47 * v 53 + v 46 * v 54 + v 12 * v 57 + v 58 + v 11 * v 58,
    -- quotient-14
    v 13 * v 17 * v 25 + v 5 * v 13 * v 17 * v 25 + v 5 * v 17 * v 33 + v 17 * v 25 * v 33 + v 3 * v 5 * v 17 * v 35 + v 3 * v 17 * v 25 * v 35 + v 5 * v 13 * v 17 * v 40 + v 3 * v 5 * v 15 * v 17 * v 40 + v 13 * v 17 * v 25 * v 40 + v 3 * v 15 * v 17 * v 25 * v 40 + v 5 * v 17 * v 33 * v 40 + v 17 * v 25 * v 33 * v 40 + v 3 * v 5 * v 17 * v 35 * v 40 + v 3 * v 17 * v 25 * v 35 * v 40 + v 5 * v 13 * v 17 * v 44 + v 5 * v 15 * v 17 * v 44 + v 3 * v 5 * v 15 * v 17 * v 44 + v 13 * v 17 * v 25 * v 44 + v 15 * v 17 * v 25 * v 44 + v 3 * v 15 * v 17 * v 25 * v 44 + v 5 * v 17 * v 33 * v 44 + v 17 * v 25 * v 33 * v 44 + v 5 * v 17 * v 35 * v 44 + v 3 * v 5 * v 17 * v 35 * v 44 + v 17 * v 25 * v 35 * v 44 + v 3 * v 17 * v 25 * v 35 * v 44 + v 5 * v 13 * v 17 * v 46 + v 3 * v 5 * v 13 * v 17 * v 46 + v 3 * v 5 * v 15 * v 17 * v 46 + v 13 * v 17 * v 25 * v 46 + v 3 * v 13 * v 17 * v 25 * v 46 + v 3 * v 15 * v 17 * v 25 * v 46 + v 5 * v 17 * v 33 * v 46 + v 3 * v 5 * v 17 * v 33 * v 46 + v 17 * v 25 * v 33 * v 46 + v 3 * v 17 * v 25 * v 33 * v 46 + v 3 * v 5 * v 17 * v 35 * v 46 + v 3 * v 17 * v 25 * v 35 * v 46 + v 5 * v 17 * v 53 + v 17 * v 25 * v 53 + v 5 * v 17 * v 46 * v 55 + v 17 * v 25 * v 46 * v 55 + v 5 * v 17 * v 44 * v 57 + v 17 * v 25 * v 44 * v 57 + v 5 * v 17 * v 59 + v 5 * v 11 * v 17 * v 59 + v 17 * v 25 * v 59 + v 11 * v 17 * v 25 * v 59,
    -- quotient-20
    v 5 * v 12 * v 17 + v 5 * v 12 * v 16 * v 17 + v 12 * v 17 * v 25 + v 13 * v 17 * v 25 + v 5 * v 13 * v 17 * v 25 + v 12 * v 16 * v 17 * v 25 + v 5 * v 17 * v 33 + v 17 * v 25 * v 33 + v 3 * v 5 * v 17 * v 35 + v 3 * v 17 * v 25 * v 35 + v 5 * v 12 * v 17 * v 40 + v 5 * v 13 * v 17 * v 40 + v 3 * v 5 * v 15 * v 17 * v 40 + v 12 * v 17 * v 25 * v 40 + v 13 * v 17 * v 25 * v 40 + v 3 * v 15 * v 17 * v 25 * v 40 + v 5 * v 17 * v 33 * v 40 + v 17 * v 25 * v 33 * v 40 + v 3 * v 5 * v 17 * v 35 * v 40 + v 3 * v 17 * v 25 * v 35 * v 40 + v 5 * v 13 * v 17 * v 44 + v 5 * v 15 * v 17 * v 44 + v 3 * v 5 * v 15 * v 17 * v 44 + v 13 * v 17 * v 25 * v 44 + v 15 * v 17 * v 25 * v 44 + v 3 * v 15 * v 17 * v 25 * v 44 + v 5 * v 17 * v 33 * v 44 + v 17 * v 25 * v 33 * v 44 + v 5 * v 17 * v 35 * v 44 + v 3 * v 5 * v 17 * v 35 * v 44 + v 17 * v 25 * v 35 * v 44 + v 3 * v 17 * v 25 * v 35 * v 44 + v 5 * v 13 * v 17 * v 46 + v 3 * v 5 * v 13 * v 17 * v 46 + v 3 * v 5 * v 15 * v 17 * v 46 + v 13 * v 17 * v 25 * v 46 + v 3 * v 13 * v 17 * v 25 * v 46 + v 3 * v 15 * v 17 * v 25 * v 46 + v 5 * v 17 * v 33 * v 46 + v 3 * v 5 * v 17 * v 33 * v 46 + v 17 * v 25 * v 33 * v 46 + v 3 * v 17 * v 25 * v 33 * v 46 + v 3 * v 5 * v 17 * v 35 * v 46 + v 3 * v 17 * v 25 * v 35 * v 46 + v 5 * v 12 * v 17 * v 47 + v 12 * v 17 * v 25 * v 47 + v 5 * v 17 * v 47 * v 54 + v 17 * v 25 * v 47 * v 54 + v 5 * v 17 * v 46 * v 55 + v 17 * v 25 * v 46 * v 55 + v 5 * v 17 * v 44 * v 57 + v 17 * v 25 * v 44 * v 57 + v 5 * v 12 * v 17 * v 58 + v 12 * v 17 * v 25 * v 58,
    -- quotient-36
    v 5 * v 12 * v 17 + v 5 * v 12 * v 15 * v 17 + v 12 * v 15 * v 17 * v 25 + v 5 * v 12 * v 17 * v 35 + v 12 * v 17 * v 25 * v 35 + v 5 * v 12 * v 17 * v 40 + v 12 * v 17 * v 25 * v 40 + v 5 * v 12 * v 17 * v 46 + v 12 * v 17 * v 25 * v 46 + v 12 * v 17 * v 57 + v 12 * v 46 * v 59,
    -- quotient-39
    v 5 * v 12 * v 17 + v 5 * v 12 * v 16 * v 17 + v 12 * v 17 * v 25 + v 12 * v 16 * v 17 * v 25 + v 5 * v 12 * v 17 * v 40 + v 12 * v 17 * v 25 * v 40 + v 5 * v 12 * v 17 * v 47 + v 12 * v 17 * v 25 * v 47 + v 5 * v 12 * v 17 * v 58 + v 12 * v 17 * v 25 * v 58 + v 5 * v 12 * v 47 * v 59 + v 12 * v 25 * v 47 * v 59
  ]

private def zeroOneAlignedCorrectionOneReducedCombination (v : Fin 71 → F₂) : F₂ :=
  zeroOneAlignedCorrectionOneReducedMultiplier v 0 * zeroOneAlignedCorrectionOneReducedConstraint v 0 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 1 * zeroOneAlignedCorrectionOneReducedConstraint v 1 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 2 * zeroOneAlignedCorrectionOneReducedConstraint v 2 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 3 * zeroOneAlignedCorrectionOneReducedConstraint v 3 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 4 * zeroOneAlignedCorrectionOneReducedConstraint v 4 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 5 * zeroOneAlignedCorrectionOneReducedConstraint v 5 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 6 * zeroOneAlignedCorrectionOneReducedConstraint v 6 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 7 * zeroOneAlignedCorrectionOneReducedConstraint v 7 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 8 * zeroOneAlignedCorrectionOneReducedConstraint v 8 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 9 * zeroOneAlignedCorrectionOneReducedConstraint v 9 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 10 * zeroOneAlignedCorrectionOneReducedConstraint v 10 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 11 * zeroOneAlignedCorrectionOneReducedConstraint v 11 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 12 * zeroOneAlignedCorrectionOneReducedConstraint v 12 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 13 * zeroOneAlignedCorrectionOneReducedConstraint v 13 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 14 * zeroOneAlignedCorrectionOneReducedConstraint v 14 +
  zeroOneAlignedCorrectionOneReducedMultiplier v 15 * zeroOneAlignedCorrectionOneReducedConstraint v 15

private theorem f2_mul_self (x : F₂) : x * x = x := by
  rcases f2_eq_zero_or_one x with h | h <;> simp [h]

private theorem f2_two_eq_zero : (2 : F₂) = 0 :=
  CharTwo.two_eq_zero

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_0 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 0 * zeroOneAlignedCorrectionOneReducedConstraint v 0 =
      zeroOneAlignedCorrectionOneReducedProduct v 0 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_1 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 1 * zeroOneAlignedCorrectionOneReducedConstraint v 1 =
      zeroOneAlignedCorrectionOneReducedProduct v 1 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_2 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 2 * zeroOneAlignedCorrectionOneReducedConstraint v 2 =
      zeroOneAlignedCorrectionOneReducedProduct v 2 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_3 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 3 * zeroOneAlignedCorrectionOneReducedConstraint v 3 =
      zeroOneAlignedCorrectionOneReducedProduct v 3 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_4 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 4 * zeroOneAlignedCorrectionOneReducedConstraint v 4 =
      zeroOneAlignedCorrectionOneReducedProduct v 4 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_5 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 5 * zeroOneAlignedCorrectionOneReducedConstraint v 5 =
      zeroOneAlignedCorrectionOneReducedProduct v 5 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_6 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 6 * zeroOneAlignedCorrectionOneReducedConstraint v 6 =
      zeroOneAlignedCorrectionOneReducedProduct v 6 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_7 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 7 * zeroOneAlignedCorrectionOneReducedConstraint v 7 =
      zeroOneAlignedCorrectionOneReducedProduct v 7 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_8 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 8 * zeroOneAlignedCorrectionOneReducedConstraint v 8 =
      zeroOneAlignedCorrectionOneReducedProduct v 8 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_9 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 9 * zeroOneAlignedCorrectionOneReducedConstraint v 9 =
      zeroOneAlignedCorrectionOneReducedProduct v 9 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_10 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 10 * zeroOneAlignedCorrectionOneReducedConstraint v 10 =
      zeroOneAlignedCorrectionOneReducedProduct v 10 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_11 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 11 * zeroOneAlignedCorrectionOneReducedConstraint v 11 =
      zeroOneAlignedCorrectionOneReducedProduct v 11 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_12 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 12 * zeroOneAlignedCorrectionOneReducedConstraint v 12 =
      zeroOneAlignedCorrectionOneReducedProduct v 12 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_13 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 13 * zeroOneAlignedCorrectionOneReducedConstraint v 13 =
      zeroOneAlignedCorrectionOneReducedProduct v 13 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_14 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 14 * zeroOneAlignedCorrectionOneReducedConstraint v 14 =
      zeroOneAlignedCorrectionOneReducedProduct v 14 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem zeroOneAlignedCorrectionOneReduced_product_15 (v : Fin 71 → F₂) :
    zeroOneAlignedCorrectionOneReducedMultiplier v 15 * zeroOneAlignedCorrectionOneReducedConstraint v 15 =
      zeroOneAlignedCorrectionOneReducedProduct v 15 := by
  simp [zeroOneAlignedCorrectionOneReducedMultiplier, zeroOneAlignedCorrectionOneReducedConstraint,
    zeroOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem zeroOneAlignedCorrectionOneReduced_certificate (v : Fin 71 → F₂) :
    (1 : F₂) = zeroOneAlignedCorrectionOneReducedCombination v := by
  unfold zeroOneAlignedCorrectionOneReducedCombination
  rw [zeroOneAlignedCorrectionOneReduced_product_0, zeroOneAlignedCorrectionOneReduced_product_1, zeroOneAlignedCorrectionOneReduced_product_2, zeroOneAlignedCorrectionOneReduced_product_3, zeroOneAlignedCorrectionOneReduced_product_4, zeroOneAlignedCorrectionOneReduced_product_5, zeroOneAlignedCorrectionOneReduced_product_6, zeroOneAlignedCorrectionOneReduced_product_7, zeroOneAlignedCorrectionOneReduced_product_8, zeroOneAlignedCorrectionOneReduced_product_9, zeroOneAlignedCorrectionOneReduced_product_10, zeroOneAlignedCorrectionOneReduced_product_11, zeroOneAlignedCorrectionOneReduced_product_12, zeroOneAlignedCorrectionOneReduced_product_13, zeroOneAlignedCorrectionOneReduced_product_14, zeroOneAlignedCorrectionOneReduced_product_15]
  simp [zeroOneAlignedCorrectionOneReducedProduct]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]
  all_goals ring

/-- The selected reduced equations generate the unit ideal. -/
theorem zeroOne_aligned_correctionOne_reduced_inconsistent
    (v : Fin 71 → F₂)
    (hzero : ∀ i : Fin 16, zeroOneAlignedCorrectionOneReducedConstraint v i = 0) :
    False := by
  have hone : (1 : F₂) = 0 := by
    rw [zeroOneAlignedCorrectionOneReduced_certificate v]
    simp [zeroOneAlignedCorrectionOneReducedCombination, hzero]
  exact one_ne_zero hone

end
end UnrestrictedBooleanMul.N5
