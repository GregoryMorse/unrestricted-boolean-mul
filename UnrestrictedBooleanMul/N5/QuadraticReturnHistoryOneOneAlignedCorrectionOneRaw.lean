import UnrestrictedBooleanMul.ANF

/-!
# Reduced aligned certificate: `OneOneAlignedCorrectionOne`

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

/-- The 13 reduced semantic generators in this unit certificate. -/
def oneOneAlignedCorrectionOneReducedConstraint (v : Fin 71 → F₂) : Fin 13 → F₂ :=
  ![
    -- product-high-0x023
    v 5 * v 10 + v 1 * v 5 * v 10 + v 0 * v 15 + v 0 * v 1 * v 15 + v 5 * v 20 + v 1 * v 5 * v 20 + v 15 * v 20 + v 1 * v 15 * v 20 + v 0 * v 25 + v 0 * v 1 * v 25 + v 10 * v 25 + v 1 * v 10 * v 25 + v 5 * v 30 + v 1 * v 5 * v 30 + v 25 * v 30 + v 1 * v 25 * v 30 + v 0 * v 35 + v 0 * v 1 * v 35 + v 20 * v 35 + v 1 * v 20 * v 35 + v 15 * v 41 + v 1 * v 15 * v 41 + v 25 * v 41 + v 1 * v 25 * v 41 + v 35 * v 41 + v 1 * v 35 * v 41 + v 10 * v 46 + v 1 * v 10 * v 46 + v 20 * v 46 + v 1 * v 20 * v 46 + v 30 * v 46 + v 1 * v 30 * v 46 + v 53 + v 62 + v 1 * v 62 + v 65 + v 41 * v 65,
    -- product-high-0x025
    v 2 * v 5 * v 10 + v 0 * v 2 * v 15 + v 2 * v 5 * v 20 + v 2 * v 15 * v 20 + v 0 * v 2 * v 25 + v 2 * v 10 * v 25 + v 2 * v 5 * v 30 + v 2 * v 25 * v 30 + v 0 * v 2 * v 35 + v 2 * v 20 * v 35 + v 2 * v 15 * v 41 + v 2 * v 25 * v 41 + v 2 * v 35 * v 41 + v 2 * v 10 * v 46 + v 2 * v 20 * v 46 + v 2 * v 30 * v 46 + v 54 + v 2 * v 62,
    -- product-high-0x043
    v 0 + v 0 * v 1 + v 6 * v 10 + v 1 * v 6 * v 10 + v 20 + v 1 * v 20 + v 6 * v 20 + v 1 * v 6 * v 20 + v 6 * v 30 + v 1 * v 6 * v 30 + v 41 + v 1 * v 41 + v 10 * v 47 + v 1 * v 10 * v 47 + v 20 * v 47 + v 1 * v 20 * v 47 + v 30 * v 47 + v 1 * v 30 * v 47 + v 65 + v 1 * v 65,
    -- product-high-0x061
    1 + v 0 + v 5 + v 6 * v 10 + v 6 * v 15 + v 20 + v 6 * v 20 + v 25 + v 6 * v 25 + v 6 * v 30 + v 6 * v 35 + v 40 + v 41 + v 5 * v 41 + v 6 * v 15 * v 41 + v 25 * v 41 + v 6 * v 25 * v 41 + v 6 * v 35 * v 41 + v 46 + v 0 * v 46 + v 6 * v 10 * v 46 + v 20 * v 46 + v 6 * v 20 * v 46 + v 6 * v 30 * v 46 + v 10 * v 47 + v 5 * v 10 * v 47 + v 15 * v 47 + v 0 * v 15 * v 47 + v 20 * v 47 + v 5 * v 20 * v 47 + v 15 * v 20 * v 47 + v 25 * v 47 + v 0 * v 25 * v 47 + v 10 * v 25 * v 47 + v 30 * v 47 + v 5 * v 30 * v 47 + v 25 * v 30 * v 47 + v 35 * v 47 + v 0 * v 35 * v 47 + v 20 * v 35 * v 47 + v 58 + v 47 * v 62 + v 65 + v 46 * v 65,
    -- product-high-0x062
    v 5 + v 1 * v 5 + v 6 * v 15 + v 1 * v 6 * v 15 + v 25 + v 1 * v 25 + v 6 * v 25 + v 1 * v 6 * v 25 + v 6 * v 35 + v 1 * v 6 * v 35 + v 46 + v 1 * v 46 + v 15 * v 47 + v 1 * v 15 * v 47 + v 25 * v 47 + v 1 * v 25 * v 47 + v 35 * v 47 + v 1 * v 35 * v 47 + v 47 * v 65,
    -- product-high-0x0a1
    v 5 * v 7 * v 10 + v 0 * v 7 * v 15 + v 5 * v 7 * v 20 + v 7 * v 15 * v 20 + v 0 * v 7 * v 25 + v 7 * v 10 * v 25 + v 5 * v 7 * v 30 + v 7 * v 25 * v 30 + v 0 * v 7 * v 35 + v 7 * v 20 * v 35 + v 7 * v 15 * v 41 + v 7 * v 25 * v 41 + v 7 * v 35 * v 41 + v 7 * v 10 * v 46 + v 7 * v 20 * v 46 + v 7 * v 30 * v 46 + v 59 + v 7 * v 62,
    -- product-high-0x0a2
    v 7 * v 65,
    -- quotient-6
    v 2 * v 5 + v 0 * v 7 + v 7 * v 10 + v 0 * v 7 * v 10 + v 2 * v 15 + v 2 * v 5 * v 15 + v 0 * v 7 * v 20 + v 7 * v 10 * v 20 + v 2 * v 5 * v 25 + v 2 * v 15 * v 25 + v 0 * v 7 * v 30 + v 7 * v 20 * v 30 + v 2 * v 5 * v 35 + v 2 * v 25 * v 35 + v 7 * v 10 * v 40 + v 2 * v 15 * v 40 + v 7 * v 20 * v 40 + v 2 * v 25 * v 40 + v 7 * v 30 * v 40 + v 2 * v 35 * v 40 + v 7 * v 41 + v 7 * v 10 * v 41 + v 7 * v 20 * v 41 + v 7 * v 30 * v 41 + v 2 * v 46 + v 2 * v 15 * v 46 + v 2 * v 25 * v 46 + v 2 * v 35 * v 46 + v 7 * v 52 + v 46 * v 54 + v 2 * v 57 + v 41 * v 59,
    -- quotient-13
    v 1 + v 2 * v 5 + v 2 * v 15 + v 2 * v 5 * v 15 + v 2 * v 5 * v 25 + v 2 * v 15 * v 25 + v 2 * v 5 * v 35 + v 2 * v 25 * v 35 + v 40 + v 1 * v 40 + v 2 * v 15 * v 40 + v 2 * v 25 * v 40 + v 2 * v 35 * v 40 + v 2 * v 46 + v 2 * v 15 * v 46 + v 2 * v 25 * v 46 + v 2 * v 35 * v 46 + v 47 * v 53 + v 46 * v 54 + v 2 * v 57 + v 58 + v 1 * v 58,
    -- quotient-14
    v 15 * v 23 + v 3 * v 25 + v 13 * v 25 + v 23 * v 25 + v 3 * v 35 + v 23 * v 35 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 15 * v 23 * v 40 + v 3 * v 25 * v 40 + v 13 * v 25 * v 40 + v 23 * v 25 * v 40 + v 3 * v 35 * v 40 + v 23 * v 35 * v 40 + v 5 * v 44 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 15 * v 23 * v 44 + v 3 * v 25 * v 44 + v 5 * v 25 * v 44 + v 13 * v 25 * v 44 + v 15 * v 25 * v 44 + v 23 * v 25 * v 44 + v 3 * v 35 * v 44 + v 5 * v 35 * v 44 + v 23 * v 35 * v 44 + v 25 * v 35 * v 44 + v 3 * v 46 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 23 * v 46 + v 13 * v 23 * v 46 + v 15 * v 23 * v 46 + v 3 * v 25 * v 46 + v 13 * v 25 * v 46 + v 23 * v 25 * v 46 + v 3 * v 35 * v 46 + v 23 * v 35 * v 46 + v 7 * v 53 + v 46 * v 55 + v 44 * v 57 + v 59 + v 1 * v 59,
    -- quotient-20
    v 2 + v 15 * v 23 + v 3 * v 25 + v 13 * v 25 + v 23 * v 25 + v 3 * v 35 + v 23 * v 35 + v 2 * v 40 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 15 * v 23 * v 40 + v 3 * v 25 * v 40 + v 13 * v 25 * v 40 + v 23 * v 25 * v 40 + v 3 * v 35 * v 40 + v 23 * v 35 * v 40 + v 5 * v 44 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 15 * v 23 * v 44 + v 3 * v 25 * v 44 + v 5 * v 25 * v 44 + v 13 * v 25 * v 44 + v 15 * v 25 * v 44 + v 23 * v 25 * v 44 + v 3 * v 35 * v 44 + v 5 * v 35 * v 44 + v 23 * v 35 * v 44 + v 25 * v 35 * v 44 + v 3 * v 46 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 23 * v 46 + v 13 * v 23 * v 46 + v 15 * v 23 * v 46 + v 3 * v 25 * v 46 + v 13 * v 25 * v 46 + v 23 * v 25 * v 46 + v 3 * v 35 * v 46 + v 23 * v 35 * v 46 + v 47 * v 54 + v 46 * v 55 + v 44 * v 57 + v 2 * v 58,
    -- quotient-36
    v 5 * v 7 + v 7 * v 15 + v 5 * v 7 * v 15 + v 5 * v 7 * v 25 + v 7 * v 15 * v 25 + v 5 * v 7 * v 35 + v 7 * v 25 * v 35 + v 7 * v 15 * v 40 + v 7 * v 25 * v 40 + v 7 * v 35 * v 40 + v 7 * v 46 + v 7 * v 15 * v 46 + v 7 * v 25 * v 46 + v 7 * v 35 * v 46 + v 7 * v 57 + v 46 * v 59,
    -- quotient-39
    v 7 + v 7 * v 40 + v 7 * v 58 + v 47 * v 59
  ]

private def oneOneAlignedCorrectionOneReducedMultiplier (v : Fin 71 → F₂) : Fin 13 → F₂ :=
  ![
    -- product-high-0x023
    v 7 * v 15 + v 7 * v 25 + v 7 * v 35 + v 47,
    -- product-high-0x025
    v 7 * v 46 + v 7 * v 15 * v 47 + v 7 * v 25 * v 47 + v 7 * v 35 * v 47,
    -- product-high-0x043
    1 + v 46,
    -- product-high-0x061
    1 + v 1,
    -- product-high-0x062
    1 + v 41,
    -- product-high-0x0a1
    v 7 * v 15 + v 1 * v 7 * v 15 + v 7 * v 25 + v 1 * v 7 * v 25 + v 7 * v 35 + v 1 * v 7 * v 35 + v 41 + v 7 * v 41 + v 2 * v 46 + v 2 * v 15 * v 47 + v 2 * v 25 * v 47 + v 2 * v 35 * v 47,
    -- product-high-0x0a2
    v 15 + v 25 + v 35 + v 15 * v 41 + v 25 * v 41 + v 35 * v 41,
    -- quotient-6
    1 + v 7,
    -- quotient-13
    1,
    -- quotient-14
    v 7 * v 15 + v 7 * v 25 + v 7 * v 35,
    -- quotient-20
    v 7 * v 15 + v 7 * v 25 + v 7 * v 35,
    -- quotient-36
    v 2,
    -- quotient-39
    v 2 * v 15 + v 2 * v 25 + v 2 * v 35
  ]

private def oneOneAlignedCorrectionOneReducedProduct (v : Fin 71 → F₂) : Fin 13 → F₂ :=
  ![
    -- product-high-0x023
    v 0 * v 7 * v 15 + v 0 * v 1 * v 7 * v 15 + v 5 * v 7 * v 10 * v 15 + v 1 * v 5 * v 7 * v 10 * v 15 + v 7 * v 15 * v 20 + v 1 * v 7 * v 15 * v 20 + v 5 * v 7 * v 15 * v 20 + v 1 * v 5 * v 7 * v 15 * v 20 + v 0 * v 7 * v 25 + v 0 * v 1 * v 7 * v 25 + v 7 * v 10 * v 25 + v 1 * v 7 * v 10 * v 25 + v 5 * v 7 * v 10 * v 25 + v 1 * v 5 * v 7 * v 10 * v 25 + v 7 * v 10 * v 15 * v 25 + v 1 * v 7 * v 10 * v 15 * v 25 + v 5 * v 7 * v 20 * v 25 + v 1 * v 5 * v 7 * v 20 * v 25 + v 7 * v 15 * v 20 * v 25 + v 1 * v 7 * v 15 * v 20 * v 25 + v 5 * v 7 * v 15 * v 30 + v 1 * v 5 * v 7 * v 15 * v 30 + v 7 * v 25 * v 30 + v 1 * v 7 * v 25 * v 30 + v 5 * v 7 * v 25 * v 30 + v 1 * v 5 * v 7 * v 25 * v 30 + v 7 * v 15 * v 25 * v 30 + v 1 * v 7 * v 15 * v 25 * v 30 + v 0 * v 7 * v 35 + v 0 * v 1 * v 7 * v 35 + v 5 * v 7 * v 10 * v 35 + v 1 * v 5 * v 7 * v 10 * v 35 + v 7 * v 20 * v 35 + v 1 * v 7 * v 20 * v 35 + v 5 * v 7 * v 20 * v 35 + v 1 * v 5 * v 7 * v 20 * v 35 + v 7 * v 10 * v 25 * v 35 + v 1 * v 7 * v 10 * v 25 * v 35 + v 7 * v 20 * v 25 * v 35 + v 1 * v 7 * v 20 * v 25 * v 35 + v 5 * v 7 * v 30 * v 35 + v 1 * v 5 * v 7 * v 30 * v 35 + v 7 * v 25 * v 30 * v 35 + v 1 * v 7 * v 25 * v 30 * v 35 + v 7 * v 15 * v 41 + v 1 * v 7 * v 15 * v 41 + v 7 * v 25 * v 41 + v 1 * v 7 * v 25 * v 41 + v 7 * v 35 * v 41 + v 1 * v 7 * v 35 * v 41 + v 7 * v 10 * v 15 * v 46 + v 1 * v 7 * v 10 * v 15 * v 46 + v 7 * v 15 * v 20 * v 46 + v 1 * v 7 * v 15 * v 20 * v 46 + v 7 * v 10 * v 25 * v 46 + v 1 * v 7 * v 10 * v 25 * v 46 + v 7 * v 20 * v 25 * v 46 + v 1 * v 7 * v 20 * v 25 * v 46 + v 7 * v 15 * v 30 * v 46 + v 1 * v 7 * v 15 * v 30 * v 46 + v 7 * v 25 * v 30 * v 46 + v 1 * v 7 * v 25 * v 30 * v 46 + v 7 * v 10 * v 35 * v 46 + v 1 * v 7 * v 10 * v 35 * v 46 + v 7 * v 20 * v 35 * v 46 + v 1 * v 7 * v 20 * v 35 * v 46 + v 7 * v 30 * v 35 * v 46 + v 1 * v 7 * v 30 * v 35 * v 46 + v 5 * v 10 * v 47 + v 1 * v 5 * v 10 * v 47 + v 0 * v 15 * v 47 + v 0 * v 1 * v 15 * v 47 + v 5 * v 20 * v 47 + v 1 * v 5 * v 20 * v 47 + v 15 * v 20 * v 47 + v 1 * v 15 * v 20 * v 47 + v 0 * v 25 * v 47 + v 0 * v 1 * v 25 * v 47 + v 10 * v 25 * v 47 + v 1 * v 10 * v 25 * v 47 + v 5 * v 30 * v 47 + v 1 * v 5 * v 30 * v 47 + v 25 * v 30 * v 47 + v 1 * v 25 * v 30 * v 47 + v 0 * v 35 * v 47 + v 0 * v 1 * v 35 * v 47 + v 20 * v 35 * v 47 + v 1 * v 20 * v 35 * v 47 + v 15 * v 41 * v 47 + v 1 * v 15 * v 41 * v 47 + v 25 * v 41 * v 47 + v 1 * v 25 * v 41 * v 47 + v 35 * v 41 * v 47 + v 1 * v 35 * v 41 * v 47 + v 10 * v 46 * v 47 + v 1 * v 10 * v 46 * v 47 + v 20 * v 46 * v 47 + v 1 * v 20 * v 46 * v 47 + v 30 * v 46 * v 47 + v 1 * v 30 * v 46 * v 47 + v 7 * v 15 * v 53 + v 7 * v 25 * v 53 + v 7 * v 35 * v 53 + v 47 * v 53 + v 7 * v 15 * v 62 + v 1 * v 7 * v 15 * v 62 + v 7 * v 25 * v 62 + v 1 * v 7 * v 25 * v 62 + v 7 * v 35 * v 62 + v 1 * v 7 * v 35 * v 62 + v 47 * v 62 + v 1 * v 47 * v 62 + v 7 * v 15 * v 65 + v 7 * v 25 * v 65 + v 7 * v 35 * v 65 + v 7 * v 15 * v 41 * v 65 + v 7 * v 25 * v 41 * v 65 + v 7 * v 35 * v 41 * v 65 + v 47 * v 65 + v 41 * v 47 * v 65,
    -- product-high-0x025
    v 2 * v 7 * v 10 * v 46 + v 2 * v 5 * v 7 * v 10 * v 46 + v 0 * v 2 * v 7 * v 15 * v 46 + v 2 * v 7 * v 20 * v 46 + v 2 * v 5 * v 7 * v 20 * v 46 + v 2 * v 7 * v 15 * v 20 * v 46 + v 0 * v 2 * v 7 * v 25 * v 46 + v 2 * v 7 * v 10 * v 25 * v 46 + v 2 * v 7 * v 30 * v 46 + v 2 * v 5 * v 7 * v 30 * v 46 + v 2 * v 7 * v 25 * v 30 * v 46 + v 0 * v 2 * v 7 * v 35 * v 46 + v 2 * v 7 * v 20 * v 35 * v 46 + v 2 * v 7 * v 15 * v 41 * v 46 + v 2 * v 7 * v 25 * v 41 * v 46 + v 2 * v 7 * v 35 * v 41 * v 46 + v 0 * v 2 * v 7 * v 15 * v 47 + v 2 * v 5 * v 7 * v 10 * v 15 * v 47 + v 2 * v 7 * v 15 * v 20 * v 47 + v 2 * v 5 * v 7 * v 15 * v 20 * v 47 + v 0 * v 2 * v 7 * v 25 * v 47 + v 2 * v 7 * v 10 * v 25 * v 47 + v 2 * v 5 * v 7 * v 10 * v 25 * v 47 + v 2 * v 7 * v 10 * v 15 * v 25 * v 47 + v 2 * v 5 * v 7 * v 20 * v 25 * v 47 + v 2 * v 7 * v 15 * v 20 * v 25 * v 47 + v 2 * v 5 * v 7 * v 15 * v 30 * v 47 + v 2 * v 7 * v 25 * v 30 * v 47 + v 2 * v 5 * v 7 * v 25 * v 30 * v 47 + v 2 * v 7 * v 15 * v 25 * v 30 * v 47 + v 0 * v 2 * v 7 * v 35 * v 47 + v 2 * v 5 * v 7 * v 10 * v 35 * v 47 + v 2 * v 7 * v 20 * v 35 * v 47 + v 2 * v 5 * v 7 * v 20 * v 35 * v 47 + v 2 * v 7 * v 10 * v 25 * v 35 * v 47 + v 2 * v 7 * v 20 * v 25 * v 35 * v 47 + v 2 * v 5 * v 7 * v 30 * v 35 * v 47 + v 2 * v 7 * v 25 * v 30 * v 35 * v 47 + v 2 * v 7 * v 15 * v 41 * v 47 + v 2 * v 7 * v 25 * v 41 * v 47 + v 2 * v 7 * v 35 * v 41 * v 47 + v 2 * v 7 * v 10 * v 15 * v 46 * v 47 + v 2 * v 7 * v 15 * v 20 * v 46 * v 47 + v 2 * v 7 * v 10 * v 25 * v 46 * v 47 + v 2 * v 7 * v 20 * v 25 * v 46 * v 47 + v 2 * v 7 * v 15 * v 30 * v 46 * v 47 + v 2 * v 7 * v 25 * v 30 * v 46 * v 47 + v 2 * v 7 * v 10 * v 35 * v 46 * v 47 + v 2 * v 7 * v 20 * v 35 * v 46 * v 47 + v 2 * v 7 * v 30 * v 35 * v 46 * v 47 + v 7 * v 46 * v 54 + v 7 * v 15 * v 47 * v 54 + v 7 * v 25 * v 47 * v 54 + v 7 * v 35 * v 47 * v 54 + v 2 * v 7 * v 46 * v 62 + v 2 * v 7 * v 15 * v 47 * v 62 + v 2 * v 7 * v 25 * v 47 * v 62 + v 2 * v 7 * v 35 * v 47 * v 62,
    -- product-high-0x043
    v 0 + v 0 * v 1 + v 6 * v 10 + v 1 * v 6 * v 10 + v 20 + v 1 * v 20 + v 6 * v 20 + v 1 * v 6 * v 20 + v 6 * v 30 + v 1 * v 6 * v 30 + v 41 + v 1 * v 41 + v 0 * v 46 + v 0 * v 1 * v 46 + v 6 * v 10 * v 46 + v 1 * v 6 * v 10 * v 46 + v 20 * v 46 + v 1 * v 20 * v 46 + v 6 * v 20 * v 46 + v 1 * v 6 * v 20 * v 46 + v 6 * v 30 * v 46 + v 1 * v 6 * v 30 * v 46 + v 41 * v 46 + v 1 * v 41 * v 46 + v 10 * v 47 + v 1 * v 10 * v 47 + v 20 * v 47 + v 1 * v 20 * v 47 + v 30 * v 47 + v 1 * v 30 * v 47 + v 10 * v 46 * v 47 + v 1 * v 10 * v 46 * v 47 + v 20 * v 46 * v 47 + v 1 * v 20 * v 46 * v 47 + v 30 * v 46 * v 47 + v 1 * v 30 * v 46 * v 47 + v 65 + v 1 * v 65 + v 46 * v 65 + v 1 * v 46 * v 65,
    -- product-high-0x061
    1 + v 0 + v 1 + v 0 * v 1 + v 5 + v 1 * v 5 + v 6 * v 10 + v 1 * v 6 * v 10 + v 6 * v 15 + v 1 * v 6 * v 15 + v 20 + v 1 * v 20 + v 6 * v 20 + v 1 * v 6 * v 20 + v 25 + v 1 * v 25 + v 6 * v 25 + v 1 * v 6 * v 25 + v 6 * v 30 + v 1 * v 6 * v 30 + v 6 * v 35 + v 1 * v 6 * v 35 + v 40 + v 1 * v 40 + v 41 + v 1 * v 41 + v 5 * v 41 + v 1 * v 5 * v 41 + v 6 * v 15 * v 41 + v 1 * v 6 * v 15 * v 41 + v 25 * v 41 + v 1 * v 25 * v 41 + v 6 * v 25 * v 41 + v 1 * v 6 * v 25 * v 41 + v 6 * v 35 * v 41 + v 1 * v 6 * v 35 * v 41 + v 46 + v 0 * v 46 + v 1 * v 46 + v 0 * v 1 * v 46 + v 6 * v 10 * v 46 + v 1 * v 6 * v 10 * v 46 + v 20 * v 46 + v 1 * v 20 * v 46 + v 6 * v 20 * v 46 + v 1 * v 6 * v 20 * v 46 + v 6 * v 30 * v 46 + v 1 * v 6 * v 30 * v 46 + v 10 * v 47 + v 1 * v 10 * v 47 + v 5 * v 10 * v 47 + v 1 * v 5 * v 10 * v 47 + v 15 * v 47 + v 0 * v 15 * v 47 + v 1 * v 15 * v 47 + v 0 * v 1 * v 15 * v 47 + v 20 * v 47 + v 1 * v 20 * v 47 + v 5 * v 20 * v 47 + v 1 * v 5 * v 20 * v 47 + v 15 * v 20 * v 47 + v 1 * v 15 * v 20 * v 47 + v 25 * v 47 + v 0 * v 25 * v 47 + v 1 * v 25 * v 47 + v 0 * v 1 * v 25 * v 47 + v 10 * v 25 * v 47 + v 1 * v 10 * v 25 * v 47 + v 30 * v 47 + v 1 * v 30 * v 47 + v 5 * v 30 * v 47 + v 1 * v 5 * v 30 * v 47 + v 25 * v 30 * v 47 + v 1 * v 25 * v 30 * v 47 + v 35 * v 47 + v 0 * v 35 * v 47 + v 1 * v 35 * v 47 + v 0 * v 1 * v 35 * v 47 + v 20 * v 35 * v 47 + v 1 * v 20 * v 35 * v 47 + v 58 + v 1 * v 58 + v 47 * v 62 + v 1 * v 47 * v 62 + v 65 + v 1 * v 65 + v 46 * v 65 + v 1 * v 46 * v 65,
    -- product-high-0x062
    v 5 + v 1 * v 5 + v 6 * v 15 + v 1 * v 6 * v 15 + v 25 + v 1 * v 25 + v 6 * v 25 + v 1 * v 6 * v 25 + v 6 * v 35 + v 1 * v 6 * v 35 + v 5 * v 41 + v 1 * v 5 * v 41 + v 6 * v 15 * v 41 + v 1 * v 6 * v 15 * v 41 + v 25 * v 41 + v 1 * v 25 * v 41 + v 6 * v 25 * v 41 + v 1 * v 6 * v 25 * v 41 + v 6 * v 35 * v 41 + v 1 * v 6 * v 35 * v 41 + v 46 + v 1 * v 46 + v 41 * v 46 + v 1 * v 41 * v 46 + v 15 * v 47 + v 1 * v 15 * v 47 + v 25 * v 47 + v 1 * v 25 * v 47 + v 35 * v 47 + v 1 * v 35 * v 47 + v 15 * v 41 * v 47 + v 1 * v 15 * v 41 * v 47 + v 25 * v 41 * v 47 + v 1 * v 25 * v 41 * v 47 + v 35 * v 41 * v 47 + v 1 * v 35 * v 41 * v 47 + v 47 * v 65 + v 41 * v 47 * v 65,
    -- product-high-0x0a1
    v 0 * v 7 * v 15 + v 0 * v 1 * v 7 * v 15 + v 5 * v 7 * v 10 * v 15 + v 1 * v 5 * v 7 * v 10 * v 15 + v 7 * v 15 * v 20 + v 1 * v 7 * v 15 * v 20 + v 5 * v 7 * v 15 * v 20 + v 1 * v 5 * v 7 * v 15 * v 20 + v 0 * v 7 * v 25 + v 0 * v 1 * v 7 * v 25 + v 7 * v 10 * v 25 + v 1 * v 7 * v 10 * v 25 + v 5 * v 7 * v 10 * v 25 + v 1 * v 5 * v 7 * v 10 * v 25 + v 7 * v 10 * v 15 * v 25 + v 1 * v 7 * v 10 * v 15 * v 25 + v 5 * v 7 * v 20 * v 25 + v 1 * v 5 * v 7 * v 20 * v 25 + v 7 * v 15 * v 20 * v 25 + v 1 * v 7 * v 15 * v 20 * v 25 + v 5 * v 7 * v 15 * v 30 + v 1 * v 5 * v 7 * v 15 * v 30 + v 7 * v 25 * v 30 + v 1 * v 7 * v 25 * v 30 + v 5 * v 7 * v 25 * v 30 + v 1 * v 5 * v 7 * v 25 * v 30 + v 7 * v 15 * v 25 * v 30 + v 1 * v 7 * v 15 * v 25 * v 30 + v 0 * v 7 * v 35 + v 0 * v 1 * v 7 * v 35 + v 5 * v 7 * v 10 * v 35 + v 1 * v 5 * v 7 * v 10 * v 35 + v 7 * v 20 * v 35 + v 1 * v 7 * v 20 * v 35 + v 5 * v 7 * v 20 * v 35 + v 1 * v 5 * v 7 * v 20 * v 35 + v 7 * v 10 * v 25 * v 35 + v 1 * v 7 * v 10 * v 25 * v 35 + v 7 * v 20 * v 25 * v 35 + v 1 * v 7 * v 20 * v 25 * v 35 + v 5 * v 7 * v 30 * v 35 + v 1 * v 5 * v 7 * v 30 * v 35 + v 7 * v 25 * v 30 * v 35 + v 1 * v 7 * v 25 * v 30 * v 35 + v 7 * v 15 * v 41 + v 1 * v 7 * v 15 * v 41 + v 7 * v 25 * v 41 + v 1 * v 7 * v 25 * v 41 + v 7 * v 35 * v 41 + v 1 * v 7 * v 35 * v 41 + v 2 * v 7 * v 10 * v 46 + v 2 * v 5 * v 7 * v 10 * v 46 + v 0 * v 2 * v 7 * v 15 * v 46 + v 7 * v 10 * v 15 * v 46 + v 1 * v 7 * v 10 * v 15 * v 46 + v 2 * v 7 * v 20 * v 46 + v 2 * v 5 * v 7 * v 20 * v 46 + v 7 * v 15 * v 20 * v 46 + v 1 * v 7 * v 15 * v 20 * v 46 + v 2 * v 7 * v 15 * v 20 * v 46 + v 0 * v 2 * v 7 * v 25 * v 46 + v 7 * v 10 * v 25 * v 46 + v 1 * v 7 * v 10 * v 25 * v 46 + v 2 * v 7 * v 10 * v 25 * v 46 + v 7 * v 20 * v 25 * v 46 + v 1 * v 7 * v 20 * v 25 * v 46 + v 2 * v 7 * v 30 * v 46 + v 2 * v 5 * v 7 * v 30 * v 46 + v 7 * v 15 * v 30 * v 46 + v 1 * v 7 * v 15 * v 30 * v 46 + v 7 * v 25 * v 30 * v 46 + v 1 * v 7 * v 25 * v 30 * v 46 + v 2 * v 7 * v 25 * v 30 * v 46 + v 0 * v 2 * v 7 * v 35 * v 46 + v 7 * v 10 * v 35 * v 46 + v 1 * v 7 * v 10 * v 35 * v 46 + v 7 * v 20 * v 35 * v 46 + v 1 * v 7 * v 20 * v 35 * v 46 + v 2 * v 7 * v 20 * v 35 * v 46 + v 7 * v 30 * v 35 * v 46 + v 1 * v 7 * v 30 * v 35 * v 46 + v 2 * v 7 * v 15 * v 41 * v 46 + v 2 * v 7 * v 25 * v 41 * v 46 + v 2 * v 7 * v 35 * v 41 * v 46 + v 0 * v 2 * v 7 * v 15 * v 47 + v 2 * v 5 * v 7 * v 10 * v 15 * v 47 + v 2 * v 7 * v 15 * v 20 * v 47 + v 2 * v 5 * v 7 * v 15 * v 20 * v 47 + v 0 * v 2 * v 7 * v 25 * v 47 + v 2 * v 7 * v 10 * v 25 * v 47 + v 2 * v 5 * v 7 * v 10 * v 25 * v 47 + v 2 * v 7 * v 10 * v 15 * v 25 * v 47 + v 2 * v 5 * v 7 * v 20 * v 25 * v 47 + v 2 * v 7 * v 15 * v 20 * v 25 * v 47 + v 2 * v 5 * v 7 * v 15 * v 30 * v 47 + v 2 * v 7 * v 25 * v 30 * v 47 + v 2 * v 5 * v 7 * v 25 * v 30 * v 47 + v 2 * v 7 * v 15 * v 25 * v 30 * v 47 + v 0 * v 2 * v 7 * v 35 * v 47 + v 2 * v 5 * v 7 * v 10 * v 35 * v 47 + v 2 * v 7 * v 20 * v 35 * v 47 + v 2 * v 5 * v 7 * v 20 * v 35 * v 47 + v 2 * v 7 * v 10 * v 25 * v 35 * v 47 + v 2 * v 7 * v 20 * v 25 * v 35 * v 47 + v 2 * v 5 * v 7 * v 30 * v 35 * v 47 + v 2 * v 7 * v 25 * v 30 * v 35 * v 47 + v 2 * v 7 * v 15 * v 41 * v 47 + v 2 * v 7 * v 25 * v 41 * v 47 + v 2 * v 7 * v 35 * v 41 * v 47 + v 2 * v 7 * v 10 * v 15 * v 46 * v 47 + v 2 * v 7 * v 15 * v 20 * v 46 * v 47 + v 2 * v 7 * v 10 * v 25 * v 46 * v 47 + v 2 * v 7 * v 20 * v 25 * v 46 * v 47 + v 2 * v 7 * v 15 * v 30 * v 46 * v 47 + v 2 * v 7 * v 25 * v 30 * v 46 * v 47 + v 2 * v 7 * v 10 * v 35 * v 46 * v 47 + v 2 * v 7 * v 20 * v 35 * v 46 * v 47 + v 2 * v 7 * v 30 * v 35 * v 46 * v 47 + v 7 * v 15 * v 59 + v 1 * v 7 * v 15 * v 59 + v 7 * v 25 * v 59 + v 1 * v 7 * v 25 * v 59 + v 7 * v 35 * v 59 + v 1 * v 7 * v 35 * v 59 + v 41 * v 59 + v 7 * v 41 * v 59 + v 2 * v 46 * v 59 + v 2 * v 15 * v 47 * v 59 + v 2 * v 25 * v 47 * v 59 + v 2 * v 35 * v 47 * v 59 + v 7 * v 15 * v 62 + v 1 * v 7 * v 15 * v 62 + v 7 * v 25 * v 62 + v 1 * v 7 * v 25 * v 62 + v 7 * v 35 * v 62 + v 1 * v 7 * v 35 * v 62 + v 2 * v 7 * v 46 * v 62 + v 2 * v 7 * v 15 * v 47 * v 62 + v 2 * v 7 * v 25 * v 47 * v 62 + v 2 * v 7 * v 35 * v 47 * v 62,
    -- product-high-0x0a2
    v 7 * v 15 * v 65 + v 7 * v 25 * v 65 + v 7 * v 35 * v 65 + v 7 * v 15 * v 41 * v 65 + v 7 * v 25 * v 41 * v 65 + v 7 * v 35 * v 41 * v 65,
    -- quotient-6
    v 2 * v 5 + v 2 * v 5 * v 7 + v 2 * v 15 + v 2 * v 5 * v 15 + v 2 * v 7 * v 15 + v 2 * v 5 * v 7 * v 15 + v 2 * v 5 * v 25 + v 2 * v 5 * v 7 * v 25 + v 2 * v 15 * v 25 + v 2 * v 7 * v 15 * v 25 + v 2 * v 5 * v 35 + v 2 * v 5 * v 7 * v 35 + v 2 * v 25 * v 35 + v 2 * v 7 * v 25 * v 35 + v 2 * v 15 * v 40 + v 2 * v 7 * v 15 * v 40 + v 2 * v 25 * v 40 + v 2 * v 7 * v 25 * v 40 + v 2 * v 35 * v 40 + v 2 * v 7 * v 35 * v 40 + v 2 * v 46 + v 2 * v 7 * v 46 + v 2 * v 15 * v 46 + v 2 * v 7 * v 15 * v 46 + v 2 * v 25 * v 46 + v 2 * v 7 * v 25 * v 46 + v 2 * v 35 * v 46 + v 2 * v 7 * v 35 * v 46 + v 46 * v 54 + v 7 * v 46 * v 54 + v 2 * v 57 + v 2 * v 7 * v 57 + v 41 * v 59 + v 7 * v 41 * v 59,
    -- quotient-13
    v 1 + v 2 * v 5 + v 2 * v 15 + v 2 * v 5 * v 15 + v 2 * v 5 * v 25 + v 2 * v 15 * v 25 + v 2 * v 5 * v 35 + v 2 * v 25 * v 35 + v 40 + v 1 * v 40 + v 2 * v 15 * v 40 + v 2 * v 25 * v 40 + v 2 * v 35 * v 40 + v 2 * v 46 + v 2 * v 15 * v 46 + v 2 * v 25 * v 46 + v 2 * v 35 * v 46 + v 47 * v 53 + v 46 * v 54 + v 2 * v 57 + v 58 + v 1 * v 58,
    -- quotient-14
    v 7 * v 15 * v 23 + v 3 * v 7 * v 25 + v 7 * v 13 * v 25 + v 3 * v 7 * v 15 * v 25 + v 7 * v 13 * v 15 * v 25 + v 7 * v 23 * v 25 + v 3 * v 7 * v 35 + v 3 * v 7 * v 15 * v 35 + v 7 * v 23 * v 35 + v 7 * v 13 * v 25 * v 35 + v 3 * v 7 * v 15 * v 40 + v 5 * v 7 * v 13 * v 15 * v 40 + v 7 * v 15 * v 23 * v 40 + v 3 * v 7 * v 25 * v 40 + v 7 * v 13 * v 25 * v 40 + v 5 * v 7 * v 13 * v 25 * v 40 + v 7 * v 13 * v 15 * v 25 * v 40 + v 7 * v 23 * v 25 * v 40 + v 3 * v 7 * v 35 * v 40 + v 5 * v 7 * v 13 * v 35 * v 40 + v 7 * v 23 * v 35 * v 40 + v 7 * v 13 * v 25 * v 35 * v 40 + v 3 * v 7 * v 15 * v 44 + v 5 * v 7 * v 13 * v 15 * v 44 + v 7 * v 15 * v 23 * v 44 + v 3 * v 7 * v 25 * v 44 + v 7 * v 13 * v 25 * v 44 + v 5 * v 7 * v 13 * v 25 * v 44 + v 7 * v 13 * v 15 * v 25 * v 44 + v 7 * v 23 * v 25 * v 44 + v 3 * v 7 * v 35 * v 44 + v 5 * v 7 * v 13 * v 35 * v 44 + v 7 * v 23 * v 35 * v 44 + v 7 * v 13 * v 25 * v 35 * v 44 + v 3 * v 7 * v 13 * v 15 * v 46 + v 5 * v 7 * v 13 * v 15 * v 46 + v 7 * v 13 * v 15 * v 23 * v 46 + v 7 * v 13 * v 25 * v 46 + v 3 * v 7 * v 13 * v 25 * v 46 + v 5 * v 7 * v 13 * v 25 * v 46 + v 7 * v 13 * v 15 * v 25 * v 46 + v 7 * v 13 * v 23 * v 25 * v 46 + v 3 * v 7 * v 13 * v 35 * v 46 + v 5 * v 7 * v 13 * v 35 * v 46 + v 7 * v 13 * v 23 * v 35 * v 46 + v 7 * v 13 * v 25 * v 35 * v 46 + v 7 * v 15 * v 53 + v 7 * v 25 * v 53 + v 7 * v 35 * v 53 + v 7 * v 15 * v 46 * v 55 + v 7 * v 25 * v 46 * v 55 + v 7 * v 35 * v 46 * v 55 + v 7 * v 15 * v 44 * v 57 + v 7 * v 25 * v 44 * v 57 + v 7 * v 35 * v 44 * v 57 + v 7 * v 15 * v 59 + v 1 * v 7 * v 15 * v 59 + v 7 * v 25 * v 59 + v 1 * v 7 * v 25 * v 59 + v 7 * v 35 * v 59 + v 1 * v 7 * v 35 * v 59,
    -- quotient-20
    v 2 * v 7 * v 15 + v 7 * v 15 * v 23 + v 2 * v 7 * v 25 + v 3 * v 7 * v 25 + v 7 * v 13 * v 25 + v 3 * v 7 * v 15 * v 25 + v 7 * v 13 * v 15 * v 25 + v 7 * v 23 * v 25 + v 2 * v 7 * v 35 + v 3 * v 7 * v 35 + v 3 * v 7 * v 15 * v 35 + v 7 * v 23 * v 35 + v 7 * v 13 * v 25 * v 35 + v 2 * v 7 * v 15 * v 40 + v 3 * v 7 * v 15 * v 40 + v 5 * v 7 * v 13 * v 15 * v 40 + v 7 * v 15 * v 23 * v 40 + v 2 * v 7 * v 25 * v 40 + v 3 * v 7 * v 25 * v 40 + v 7 * v 13 * v 25 * v 40 + v 5 * v 7 * v 13 * v 25 * v 40 + v 7 * v 13 * v 15 * v 25 * v 40 + v 7 * v 23 * v 25 * v 40 + v 2 * v 7 * v 35 * v 40 + v 3 * v 7 * v 35 * v 40 + v 5 * v 7 * v 13 * v 35 * v 40 + v 7 * v 23 * v 35 * v 40 + v 7 * v 13 * v 25 * v 35 * v 40 + v 3 * v 7 * v 15 * v 44 + v 5 * v 7 * v 13 * v 15 * v 44 + v 7 * v 15 * v 23 * v 44 + v 3 * v 7 * v 25 * v 44 + v 7 * v 13 * v 25 * v 44 + v 5 * v 7 * v 13 * v 25 * v 44 + v 7 * v 13 * v 15 * v 25 * v 44 + v 7 * v 23 * v 25 * v 44 + v 3 * v 7 * v 35 * v 44 + v 5 * v 7 * v 13 * v 35 * v 44 + v 7 * v 23 * v 35 * v 44 + v 7 * v 13 * v 25 * v 35 * v 44 + v 3 * v 7 * v 13 * v 15 * v 46 + v 5 * v 7 * v 13 * v 15 * v 46 + v 7 * v 13 * v 15 * v 23 * v 46 + v 7 * v 13 * v 25 * v 46 + v 3 * v 7 * v 13 * v 25 * v 46 + v 5 * v 7 * v 13 * v 25 * v 46 + v 7 * v 13 * v 15 * v 25 * v 46 + v 7 * v 13 * v 23 * v 25 * v 46 + v 3 * v 7 * v 13 * v 35 * v 46 + v 5 * v 7 * v 13 * v 35 * v 46 + v 7 * v 13 * v 23 * v 35 * v 46 + v 7 * v 13 * v 25 * v 35 * v 46 + v 7 * v 15 * v 47 * v 54 + v 7 * v 25 * v 47 * v 54 + v 7 * v 35 * v 47 * v 54 + v 7 * v 15 * v 46 * v 55 + v 7 * v 25 * v 46 * v 55 + v 7 * v 35 * v 46 * v 55 + v 7 * v 15 * v 44 * v 57 + v 7 * v 25 * v 44 * v 57 + v 7 * v 35 * v 44 * v 57 + v 2 * v 7 * v 15 * v 58 + v 2 * v 7 * v 25 * v 58 + v 2 * v 7 * v 35 * v 58,
    -- quotient-36
    v 2 * v 5 * v 7 + v 2 * v 7 * v 15 + v 2 * v 5 * v 7 * v 15 + v 2 * v 5 * v 7 * v 25 + v 2 * v 7 * v 15 * v 25 + v 2 * v 5 * v 7 * v 35 + v 2 * v 7 * v 25 * v 35 + v 2 * v 7 * v 15 * v 40 + v 2 * v 7 * v 25 * v 40 + v 2 * v 7 * v 35 * v 40 + v 2 * v 7 * v 46 + v 2 * v 7 * v 15 * v 46 + v 2 * v 7 * v 25 * v 46 + v 2 * v 7 * v 35 * v 46 + v 2 * v 7 * v 57 + v 2 * v 46 * v 59,
    -- quotient-39
    v 2 * v 7 * v 15 + v 2 * v 7 * v 25 + v 2 * v 7 * v 35 + v 2 * v 7 * v 15 * v 40 + v 2 * v 7 * v 25 * v 40 + v 2 * v 7 * v 35 * v 40 + v 2 * v 7 * v 15 * v 58 + v 2 * v 7 * v 25 * v 58 + v 2 * v 7 * v 35 * v 58 + v 2 * v 15 * v 47 * v 59 + v 2 * v 25 * v 47 * v 59 + v 2 * v 35 * v 47 * v 59
  ]

private def oneOneAlignedCorrectionOneReducedCombination (v : Fin 71 → F₂) : F₂ :=
  oneOneAlignedCorrectionOneReducedMultiplier v 0 * oneOneAlignedCorrectionOneReducedConstraint v 0 +
  oneOneAlignedCorrectionOneReducedMultiplier v 1 * oneOneAlignedCorrectionOneReducedConstraint v 1 +
  oneOneAlignedCorrectionOneReducedMultiplier v 2 * oneOneAlignedCorrectionOneReducedConstraint v 2 +
  oneOneAlignedCorrectionOneReducedMultiplier v 3 * oneOneAlignedCorrectionOneReducedConstraint v 3 +
  oneOneAlignedCorrectionOneReducedMultiplier v 4 * oneOneAlignedCorrectionOneReducedConstraint v 4 +
  oneOneAlignedCorrectionOneReducedMultiplier v 5 * oneOneAlignedCorrectionOneReducedConstraint v 5 +
  oneOneAlignedCorrectionOneReducedMultiplier v 6 * oneOneAlignedCorrectionOneReducedConstraint v 6 +
  oneOneAlignedCorrectionOneReducedMultiplier v 7 * oneOneAlignedCorrectionOneReducedConstraint v 7 +
  oneOneAlignedCorrectionOneReducedMultiplier v 8 * oneOneAlignedCorrectionOneReducedConstraint v 8 +
  oneOneAlignedCorrectionOneReducedMultiplier v 9 * oneOneAlignedCorrectionOneReducedConstraint v 9 +
  oneOneAlignedCorrectionOneReducedMultiplier v 10 * oneOneAlignedCorrectionOneReducedConstraint v 10 +
  oneOneAlignedCorrectionOneReducedMultiplier v 11 * oneOneAlignedCorrectionOneReducedConstraint v 11 +
  oneOneAlignedCorrectionOneReducedMultiplier v 12 * oneOneAlignedCorrectionOneReducedConstraint v 12

private theorem f2_mul_self (x : F₂) : x * x = x := by
  rcases f2_eq_zero_or_one x with h | h <;> simp [h]

private theorem f2_two_eq_zero : (2 : F₂) = 0 :=
  CharTwo.two_eq_zero

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_0 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 0 * oneOneAlignedCorrectionOneReducedConstraint v 0 =
      oneOneAlignedCorrectionOneReducedProduct v 0 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_1 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 1 * oneOneAlignedCorrectionOneReducedConstraint v 1 =
      oneOneAlignedCorrectionOneReducedProduct v 1 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_2 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 2 * oneOneAlignedCorrectionOneReducedConstraint v 2 =
      oneOneAlignedCorrectionOneReducedProduct v 2 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_3 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 3 * oneOneAlignedCorrectionOneReducedConstraint v 3 =
      oneOneAlignedCorrectionOneReducedProduct v 3 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_4 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 4 * oneOneAlignedCorrectionOneReducedConstraint v 4 =
      oneOneAlignedCorrectionOneReducedProduct v 4 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_5 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 5 * oneOneAlignedCorrectionOneReducedConstraint v 5 =
      oneOneAlignedCorrectionOneReducedProduct v 5 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_6 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 6 * oneOneAlignedCorrectionOneReducedConstraint v 6 =
      oneOneAlignedCorrectionOneReducedProduct v 6 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_7 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 7 * oneOneAlignedCorrectionOneReducedConstraint v 7 =
      oneOneAlignedCorrectionOneReducedProduct v 7 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_8 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 8 * oneOneAlignedCorrectionOneReducedConstraint v 8 =
      oneOneAlignedCorrectionOneReducedProduct v 8 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_9 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 9 * oneOneAlignedCorrectionOneReducedConstraint v 9 =
      oneOneAlignedCorrectionOneReducedProduct v 9 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_10 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 10 * oneOneAlignedCorrectionOneReducedConstraint v 10 =
      oneOneAlignedCorrectionOneReducedProduct v 10 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_11 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 11 * oneOneAlignedCorrectionOneReducedConstraint v 11 =
      oneOneAlignedCorrectionOneReducedProduct v 11 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 1000000 in
private theorem oneOneAlignedCorrectionOneReduced_product_12 (v : Fin 71 → F₂) :
    oneOneAlignedCorrectionOneReducedMultiplier v 12 * oneOneAlignedCorrectionOneReducedConstraint v 12 =
      oneOneAlignedCorrectionOneReducedProduct v 12 := by
  simp [oneOneAlignedCorrectionOneReducedMultiplier, oneOneAlignedCorrectionOneReducedConstraint,
    oneOneAlignedCorrectionOneReducedProduct, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, f2_mul_self]
  all_goals (try rw [f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem oneOneAlignedCorrectionOneReduced_certificate (v : Fin 71 → F₂) :
    (1 : F₂) = oneOneAlignedCorrectionOneReducedCombination v := by
  unfold oneOneAlignedCorrectionOneReducedCombination
  rw [oneOneAlignedCorrectionOneReduced_product_0, oneOneAlignedCorrectionOneReduced_product_1, oneOneAlignedCorrectionOneReduced_product_2, oneOneAlignedCorrectionOneReduced_product_3, oneOneAlignedCorrectionOneReduced_product_4, oneOneAlignedCorrectionOneReduced_product_5, oneOneAlignedCorrectionOneReduced_product_6, oneOneAlignedCorrectionOneReduced_product_7, oneOneAlignedCorrectionOneReduced_product_8, oneOneAlignedCorrectionOneReduced_product_9, oneOneAlignedCorrectionOneReduced_product_10, oneOneAlignedCorrectionOneReduced_product_11, oneOneAlignedCorrectionOneReduced_product_12]
  simp [oneOneAlignedCorrectionOneReducedProduct]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]
  all_goals ring

/-- The selected reduced equations generate the unit ideal. -/
theorem oneOne_aligned_correctionOne_reduced_inconsistent
    (v : Fin 71 → F₂)
    (hzero : ∀ i : Fin 13, oneOneAlignedCorrectionOneReducedConstraint v i = 0) :
    False := by
  have hone : (1 : F₂) = 0 := by
    rw [oneOneAlignedCorrectionOneReduced_certificate v]
    simp [oneOneAlignedCorrectionOneReducedCombination, hzero]
  exact one_ne_zero hone

end
end UnrestrictedBooleanMul.N5
