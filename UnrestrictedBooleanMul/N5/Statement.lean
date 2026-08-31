import UnrestrictedBooleanMul.N5.Upper

/-!
# Canonical statement for the five-term result

The definition below deliberately separates the statement from the future
lower-bound proof.  The explicit thirteen-gate upper circuit is already in
`N5.Upper`, but the paper theorem will be represented by a proof of
`MainStatement` only after the closed-place and feedback modules in `n5/` have
been implemented.
-/

namespace UnrestrictedBooleanMul
namespace N5

/-- The exact theorem proved informally in the associated manuscript. -/
abbrev MainStatement : Prop := MC(Mul 5) = 13

end N5
end UnrestrictedBooleanMul
