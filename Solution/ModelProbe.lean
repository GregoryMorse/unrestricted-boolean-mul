module

public import UnrestrictedBooleanMul.Mul

@[expose] public section

namespace UnrestrictedBooleanMul

/-- The independent proof-side model, without importing the admitted Challenge. -/
theorem comparator_model_probe (n : Nat) : MC(Mul n) = MC(Mul n) := rfl

end UnrestrictedBooleanMul
