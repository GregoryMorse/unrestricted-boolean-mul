module

public import Challenge

@[expose] public section

namespace UnrestrictedBooleanMul

/-- CI checks the entire statement-model dependency closure before the large proof build. -/
theorem comparator_model_probe (n : Nat) : MC(Mul n) = MC(Mul n) := rfl

end UnrestrictedBooleanMul
