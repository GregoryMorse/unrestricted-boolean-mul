import UnrestrictedBooleanMul.N5.Target

/-!
# Canonical statement for the five-term result

The definition below deliberately separates the statement from the future
proof.  It is not a theorem and does not claim that the `n = 5` formalization
is complete.  The paper theorem will be represented by a proof of
`MainStatement` once the closed-place and feedback modules in `n5/` have been
implemented.
-/

namespace UnrestrictedBooleanMul
namespace N5

/-- The exact theorem proved informally in the associated manuscript. -/
abbrev MainStatement : Prop := MC(Mul 5) = 13

end N5
end UnrestrictedBooleanMul
