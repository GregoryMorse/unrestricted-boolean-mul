import UnrestrictedBooleanMul.CircuitPadding
import UnrestrictedBooleanMul.N5.Statement

/-!
# Final interface for the five-term theorem

The remaining structural work has one endpoint: exclusion of exactly twelve
gates.  Circuit padding turns that endpoint into the uniform lower bound;
the already checked explicit upper circuit then gives the exact complexity.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem mul_five_lower_of_no_twelve
    (hno : ¬ HasCircuit (Mul 5) 12)
    (r : Nat) (hCircuit : HasCircuit (Mul 5) r) : 13 ≤ r := by
  by_contra hnot
  have hr : r ≤ 12 := by omega
  exact hno (hCircuit.pad hr)

/-- Once the structural lower theorem excludes twelve gates, no further
mathematical input is needed for the exact `MC` statement. -/
theorem mc_mul_five_of_no_twelve
    (hno : ¬ HasCircuit (Mul 5) 12) : MainStatement :=
  mc_eq_of_lower_upper mul_five_upper (mul_five_lower_of_no_twelve hno)

end
end N5
end UnrestrictedBooleanMul
