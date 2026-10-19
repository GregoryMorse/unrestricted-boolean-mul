module

public import UnrestrictedBooleanMul.N3.Basis

@[expose] public section

namespace UnrestrictedBooleanMul
open N3Certificate
noncomputable section

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem product_coeff_c34 (a b : Fin 10 → F₂) :
    (rationalRep a * rationalRep b).coeff (Monomial.mk {1, 5}) +
      (rationalRep a * rationalRep b).coeff (Monomial.mk {2, 4}) = c34 a b := by
  solve_product_coeff


end

end UnrestrictedBooleanMul
