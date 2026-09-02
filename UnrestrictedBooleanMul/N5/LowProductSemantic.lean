import UnrestrictedBooleanMul.N5.QuadraticCoordinates
import UnrestrictedBooleanMul.N4.BooleanIdentities

/-!
# Semantic data of a low--low Boolean product

The exterior-coordinate files normalize cubic overlap terms internally.  At
the circuit boundary the safest invariant is instead the literal class of an
ANF modulo all degree-at-most-two functions.  This module pairs that exact
high class with the exact quadratic shadow proved in
`N5.QuadraticCoordinates`.

This formulation automatically retains cubic terms caused by overlapping
quadratic monomials.  It therefore provides the sound interface from actual
circuit wires to the later normalized exterior calculations.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

abbrev HighQuotientTen :=
  ANF 10 ⧸ N4.quadraticANFSpace 10

def highProjectionTen : ANF 10 →ₗ[F₂] HighQuotientTen :=
  Submodule.mkQ (N4.quadraticANFSpace 10)

theorem highProjectionTen_eq_zero_of_quadratic {p : ANF 10}
    (hp : p ∈ N4.quadraticANFSpace 10) :
    highProjectionTen p = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).2 hp

theorem highProjectionTen_eq_zero_iff (p : ANF 10) :
    highProjectionTen p = 0 ↔ p ∈ N4.quadraticANFSpace 10 :=
  Submodule.Quotient.mk_eq_zero _

/-- The actual nonquadratic class of the zero-constant low product. -/
def lowProductHighClass
    (ell m : LinearForm) (q c : TwoForm) : HighQuotientTen :=
  highProjectionTen
    (quadraticCoordinateANF 0 ell q * quadraticCoordinateANF 0 m c)

/-- Exact circuit-facing data: high quotient class and quadratic shadow. -/
def lowProductSemanticData
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    HighQuotientTen × TwoForm :=
  (lowProductHighClass ell m q c,
    lowProductQuadraticShadow a b ell m q c)

private theorem constantPart_mul_quadratic_mem
    (a : F₂) {p : ANF 10} (hp : p ∈ N4.quadraticANFSpace 10) :
    (a • (1 : ANF 10)) * p ∈ N4.quadraticANFSpace 10 := by
  simpa [smul_mul_assoc] using (N4.quadraticANFSpace 10).smul_mem a hp

private theorem quadratic_mul_constantPart_mem
    {p : ANF 10} (hp : p ∈ N4.quadraticANFSpace 10) (a : F₂) :
    p * (a • (1 : ANF 10)) ∈ N4.quadraticANFSpace 10 := by
  rw [mul_comm]
  exact constantPart_mul_quadratic_mem a hp

/-- Constants do not affect the class of a low product above degree two. -/
theorem highProjectionTen_quadraticCoordinateANF_mul
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    highProjectionTen
        (quadraticCoordinateANF a ell q *
          quadraticCoordinateANF b m c) =
      lowProductHighClass ell m q c := by
  let x := quadraticCoordinateANF 0 ell q
  let y := quadraticCoordinateANF 0 m c
  have hx : x ∈ N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace 0 ell q
  have hy : y ∈ N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace 0 m c
  have hfullRight : quadraticCoordinateANF b m c ∈
      N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace b m c
  have hleft : quadraticCoordinateANF a ell q =
      a • (1 : ANF 10) + x := by
    simpa [x, quadraticCoordinateANF] using
      add_assoc (a • (1 : ANF 10)) (linearANFTen ell)
        (quadraticANFOfForm q)
  have hright : quadraticCoordinateANF b m c =
      b • (1 : ANF 10) + y := by
    simpa [y, quadraticCoordinateANF] using
      add_assoc (b • (1 : ANF 10)) (linearANFTen m)
        (quadraticANFOfForm c)
  rw [hleft, add_mul, map_add,
    highProjectionTen_eq_zero_of_quadratic
      (constantPart_mul_quadratic_mem a hfullRight), zero_add]
  rw [hright, mul_add, map_add,
    highProjectionTen_eq_zero_of_quadratic
      (quadratic_mul_constantPart_mem hx b), zero_add]
  rfl

/-- Both components of `lowProductSemanticData` are the literal semantic
projections of the corresponding Boolean product. -/
theorem quadraticCoordinateANF_mul_semanticData
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    (highProjectionTen
        (quadraticCoordinateANF a ell q *
          quadraticCoordinateANF b m c),
      quadraticProjection 10
        (quadraticCoordinateANF a ell q *
          quadraticCoordinateANF b m c)) =
      lowProductSemanticData a b ell m q c := by
  apply Prod.ext
  · exact highProjectionTen_quadraticCoordinateANF_mul a b ell m q c
  · exact quadraticProjection_quadraticCoordinateANF_mul a b ell m q c

theorem lowProductHighClass_swap
    (ell m : LinearForm) (q c : TwoForm) :
    lowProductHighClass ell m q c = lowProductHighClass m ell c q := by
  simp [lowProductHighClass, mul_comm]

private theorem quadraticCoordinateANF_zero_add
    (ell m : LinearForm) (q c : TwoForm) :
    quadraticCoordinateANF 0 (ell + m) (q + c) =
      quadraticCoordinateANF 0 ell q + quadraticCoordinateANF 0 m c := by
  have hqadd : quadraticANFOfForm (q + c) =
      quadraticANFOfForm q + quadraticANFOfForm c :=
    map_add quadraticANFOfFormLinear q c
  simp only [quadraticCoordinateANF, zero_smul, zero_add,
    linearANFTen_add, hqadd]
  ac_rfl

/-- Right factor rotation preserves the exact high quotient class.  The
proof is Boolean idempotence, so cubic overlap terms are included. -/
theorem lowProductHighClass_rotate_right
    (ell m : LinearForm) (q c : TwoForm) :
    lowProductHighClass ell (ell + m) q (q + c) =
      lowProductHighClass ell m q c := by
  let x := quadraticCoordinateANF 0 ell q
  let y := quadraticCoordinateANF 0 m c
  have hx : x ∈ N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace 0 ell q
  rw [lowProductHighClass, lowProductHighClass,
    quadraticCoordinateANF_zero_add]
  change highProjectionTen (x * (x + y)) = highProjectionTen (x * y)
  rw [mul_add, N4.anf_mul_self, map_add,
    highProjectionTen_eq_zero_of_quadratic hx, zero_add]

theorem lowProductHighClass_rotate_left
    (ell m : LinearForm) (q c : TwoForm) :
    lowProductHighClass (ell + m) m (q + c) c =
      lowProductHighClass ell m q c := by
  calc
    lowProductHighClass (ell + m) m (q + c) c =
        lowProductHighClass m (ell + m) c (q + c) :=
      lowProductHighClass_swap (ell + m) m (q + c) c
    _ = lowProductHighClass m ell c q := by
      simpa [add_comm] using lowProductHighClass_rotate_right m ell c q
    _ = lowProductHighClass ell m q c :=
      lowProductHighClass_swap m ell c q

/-- The exact high class and quadratic shadow transform together under a
right factor rotation. -/
theorem lowProductSemanticData_rotate_right
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    lowProductSemanticData a (a + b) ell (ell + m) q (q + c) =
      (lowProductHighClass ell m q c,
        q + lowProductQuadraticShadow a b ell m q c) := by
  apply Prod.ext
  · exact lowProductHighClass_rotate_right ell m q c
  · exact lowProductQuadraticShadow_rotate_right a b ell m q c

end
end N5
end UnrestrictedBooleanMul
