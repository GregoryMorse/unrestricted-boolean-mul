module

public import UnrestrictedBooleanMul.N3.Basis

@[expose] public section

namespace UnrestrictedBooleanMul
open N3Certificate
noncomputable section

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_g0 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 4}) +
      (rationalRep a * rationalRep b).coeff (Monomial.mk {0, 5}) = g0 a b := by
  solve_product_coeff


end

end UnrestrictedBooleanMul
