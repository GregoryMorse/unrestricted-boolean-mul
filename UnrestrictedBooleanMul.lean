import UnrestrictedBooleanMul.N3TruthTable
import UnrestrictedBooleanMul.N4.Main
import UnrestrictedBooleanMul.N5.Statement
import UnrestrictedBooleanMul.N5.DisplacementBound

/-!
# Unrestricted Boolean multiplicative complexity

This root module exports the exact results through `n = 4`, the explicit
thirteen-gate upper circuit for `n = 5`, and the canonical statement plus
quadratic quotient, relation map, rank-two Hankel support, and local
Klein-quadric layers, including the exact classification and count of the 43
effective quadratic fibers and the full strong mixed-place exclusion, for the
in-progress `n = 5` lower-bound formalization.  It also exports the canonical
defect-capacity construction, its exact displacement/relation-gift ledger,
and the choice-independent represented-place profile of its displacement.
The profile is evaluated numerically as the weighted count of represented
closed places.  For defect dimension at most three, its relation kernel and
relation-gift range are reduced algebraically to Fano line and quadrilateral
supports.
The `N3`, `N4`, and `N5` module names describe theorem scope rather than an
internal research workflow.
-/
