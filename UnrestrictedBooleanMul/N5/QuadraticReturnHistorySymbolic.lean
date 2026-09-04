import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryModel

/-!
# Support-restricted coefficient convolution

The semantic history bridge only needs selected cubic coefficients.  This
module records the algebraic fact that a product coefficient on support `t`
depends solely on factor monomials supported inside `t`.  It avoids expanding
the ambient ten-variable products or enumerating Boolean assignments.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

@[simp] theorem monomial_mk_mul {m : Nat} (s t : Finset (Fin m)) :
    (⟨s⟩ : Monomial m) * ⟨t⟩ = ⟨s ∪ t⟩ := rfl

/-- Monomials whose variables lie in a selected support. -/
def monomialPowerset (t : Finset (Fin 10)) : Finset (Monomial 10) :=
  t.powerset.image fun s => ⟨s⟩

theorem mem_monomialPowerset_iff (m : Monomial 10)
    (t : Finset (Fin 10)) :
    m ∈ monomialPowerset t ↔ m.vars ⊆ t := by
  constructor
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨s, hs, hsm⟩
    subst m
    exact Finset.mem_powerset.mp hs
  · intro hm
    apply Finset.mem_image.mpr
    exact ⟨m.vars, Finset.mem_powerset.mpr hm, by cases m; rfl⟩

/-- The finite antidiagonal of squarefree monomials whose union is `t`. -/
def monomialUnionPairs (t : Finset (Fin 10)) :
    Finset (Monomial 10 × Monomial 10) :=
  (monomialPowerset t ×ˢ monomialPowerset t).filter
    fun p => p.1 * p.2 = ⟨t⟩

/-- Coefficient convolution restricted to the selected support. -/
theorem coeff_mul_monomialUnionPairs {R : Type*} [CommSemiring R]
    (x y : MonoidAlgebra R (Monomial 10)) (t : Finset (Fin 10)) :
    (x * y).coeff ⟨t⟩ =
      ∑ p ∈ monomialUnionPairs t, x.coeff p.1 * y.coeff p.2 := by
  classical
  apply MonoidAlgebra.coeff_mul_antidiag
  intro p
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hp⟩
    apply Finset.mem_product.mpr
    constructor
    · rw [mem_monomialPowerset_iff]
      intro i hi
      have hi' : i ∈ (p.1 * p.2).vars := by simp [hi]
      rw [hp] at hi'
      exact hi'
    · rw [mem_monomialPowerset_iff]
      intro i hi
      have hi' : i ∈ (p.1 * p.2).vars := by simp [hi]
      rw [hp] at hi'
      exact hi'

end
end N5
end UnrestrictedBooleanMul
