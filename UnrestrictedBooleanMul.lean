import UnrestrictedBooleanMul.N3TruthTable
import UnrestrictedBooleanMul.N4.Main
import UnrestrictedBooleanMul.N5.Statement
import UnrestrictedBooleanMul.N5.DisplacementBound
import UnrestrictedBooleanMul.N5.ThreePlaceDegreeTwo
import UnrestrictedBooleanMul.N5.RationalPlaceSymmetry
import UnrestrictedBooleanMul.N5.TwoRationalDegreeTwoProfile
import UnrestrictedBooleanMul.N5.TwoPlaceProfile
import UnrestrictedBooleanMul.N5.DefectTwoCapacity
import UnrestrictedBooleanMul.N5.DefectThreeWitness
import UnrestrictedBooleanMul.N5.SecantPfaffian
import UnrestrictedBooleanMul.N5.LocalSecantPivots
import UnrestrictedBooleanMul.N5.DegreeTwoSecantQ2
import UnrestrictedBooleanMul.N5.DegreeTwoSecantPivots
import UnrestrictedBooleanMul.N5.LineSecantGifts
import UnrestrictedBooleanMul.N5.FanoLineIncidencePivots
import UnrestrictedBooleanMul.N5.PointedFanoRelations
import UnrestrictedBooleanMul.N5.RationalSecantSymmetry
import UnrestrictedBooleanMul.N5.AllRationalPointedPivots
import UnrestrictedBooleanMul.N5.StrongDegreeTwoPointedPivots
import UnrestrictedBooleanMul.N5.Capacity
import UnrestrictedBooleanMul.N5.QuadraticFlattening
import UnrestrictedBooleanMul.N5.PrefixState
import UnrestrictedBooleanMul.N5.SuffixBudget
import UnrestrictedBooleanMul.N5.FirstOrderEnvelope
import UnrestrictedBooleanMul.N5.MissingCoset
import UnrestrictedBooleanMul.N5.MissingCosetQuadratic
import UnrestrictedBooleanMul.N5.RankOneTargetClean
import UnrestrictedBooleanMul.N5.TargetClean
import UnrestrictedBooleanMul.N5.TargetCleanMatrix
import UnrestrictedBooleanMul.N5.EnvelopeKernel
import UnrestrictedBooleanMul.N5.ShadowRecovery
import UnrestrictedBooleanMul.N5.LocalShadow
import UnrestrictedBooleanMul.N5.LowProductShadow
import UnrestrictedBooleanMul.N5.RankOneShadow
import UnrestrictedBooleanMul.N5.IndependentShadow
import UnrestrictedBooleanMul.N5.EnvelopeShadow
import UnrestrictedBooleanMul.N5.ColourBirth
import UnrestrictedBooleanMul.N5.ColourNormalization
import UnrestrictedBooleanMul.N5.ThreeColour

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
supports.  The representative degree-two-plus-two-rational obstruction is
equipped with explicit translation and reversal actions on input forms,
local Klein charts, canonical lifts, and the nine-dimensional Hankel target;
all three rational-pair profiles have empty triple fibers, zero relation gift,
and target capacity seven.  In defect dimension at most two, mixed-place
exclusion also gives the sharp universal capacity bound six, attained by an
explicit rational-plus-degree-two defect line.
The `N3`, `N4`, and `N5` module names describe theorem scope rather than an
internal research workflow.
-/
