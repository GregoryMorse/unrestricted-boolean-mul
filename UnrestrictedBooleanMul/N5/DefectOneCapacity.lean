import UnrestrictedBooleanMul.N5.DefectTwoCapacity
import UnrestrictedBooleanMul.N5.FirstOrderEnvelope
import UnrestrictedBooleanMul.N5.QuadraticPrefixExact

/-!
# Sharp capacity bound in defect dimension at most one

A one-dimensional binary defect contains only one nonzero quotient point.
The closed-place classification therefore permits at most one represented
place type, of weight at most two, and the additive relation map has zero
domain.  The exact capacity formula then gives `rho_1(5) <= 5`.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Two distinct represented place types supply two independent nonzero
vectors in the defect space, so they cannot occur in dimension at most one. -/
theorem not_two_distinct_represented_places_of_finrank_le_one
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 1)
    (i j : Fin 4)
    (hi : IsRepresentedPlace Q i)
    (hj : IsRepresentedPlace Q j)
    (hij : i ≠ j) : False := by
  let x := representedPopulatedPoint Q i hi
  let y := representedPopulatedPoint Q j hj
  have hx0 : x.1 ≠ 0 := by
    intro hx
    exact x.2.1 (congrArg Subtype.val hx)
  have hy0 : y.1 ≠ 0 := by
    intro hy
    exact y.2.1 (congrArg Subtype.val hy)
  have hxy : x.1 ≠ y.1 := by
    intro h
    exact representedPopulatedPoint_ne Q i j hi hj hij (Subtype.ext h)
  have hlin : LinearIndependent F₂ (![x.1, y.1] : Fin 2 → Q) := by
    rw [linearIndependent_fin2]
    constructor
    · simpa using hy0
    · intro a
      rcases f2_eq_zero_or_one a with rfl | rfl
      · simpa using hx0.symm
      · simpa using hxy.symm
  have hcard := hlin.fintype_card_le_finrank
  have : 2 ≤ Module.finrank F₂ Q := by simpa using hcard
  omega

/-- A defect space of dimension at most one represents closed places of total
weight at most two.  The degree-two place is the unique weight-two type. -/
theorem representedPlaceWeight_le_two_of_finrank_le_one
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 1) :
    representedPlaceWeight Q ≤ 2 := by
  by_contra hbound
  have hthree : 3 ≤ representedPlaceWeight Q := by omega
  rcases exists_two_distinct_represented_places_of_weight_ge_three
      Q hthree with ⟨i, j, hi, hj, hij⟩
  exact not_two_distinct_represented_places_of_finrank_le_one
    Q hQ i j hi hj hij

/-- Sharp first-order capacity bound: `rho_1(5) <= 5`. -/
theorem targetCapacity_le_five_of_finrank_le_one
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 1) :
    targetCapacity Q ≤ 5 := by
  rw [targetCapacity_eq_three_add_representedPlaceWeight_add_gifts,
    relationGiftRank_eq_zero_of_finrank_le_one Q hQ]
  have hweight := representedPlaceWeight_le_two_of_finrank_le_one Q hQ
  omega

/-- At zero defect only the three rational rank-one directions remain, so the
target capacity is exactly bounded by three. -/
theorem targetCapacity_le_three_of_finrank_eq_zero
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q = 0) :
    targetCapacity Q ≤ 3 := by
  have hnone : ∀ i : Fin 4, ¬ IsRepresentedPlace Q i := by
    intro i hi
    let x := representedPopulatedPoint Q i hi
    letI : Subsingleton Q := Module.finrank_zero_iff.mp hQ
    have hxzero : x.1 = 0 := Subsingleton.elim _ _
    exact x.2.1 (congrArg Subtype.val hxzero)
  rw [targetCapacity_eq_three_add_representedPlaceWeight_add_gifts,
    representedPlaceWeight_eq_zero_of_no_represented_places Q hnone,
    relationGiftRank_eq_zero_of_finrank_le_one Q (by omega)]

/-- Circuit-facing sharp capacity bound for an all-quadratic prefix of defect
at most one. -/
theorem allQuadraticPrefix_targetRank_le_five_of_flagDefect_le_one
    {r j : Nat} (C : Circuit 10 r) (hj : j ≤ r)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10)
    (hdef : N4.flagDefectRank
      (N4.circuitFlag C j) (mulTarget 5) ≤ 1) :
    N4.flagTargetRank (N4.circuitFlag C j) (mulTarget 5) ≤ 5 := by
  let hflat := quadraticPrefixFlattening_of_all_quadratic C hj hall
  have hQ : Module.finrank F₂ (presentationDefect hflat.generator) ≤ 1 := by
    rw [quadraticPrefixFlattening_defect_eq_flagDefect C hflat hall]
    exact hdef
  exact (flattenedPrefix_targetRank_le_capacity C hflat).trans
    (targetCapacity_le_five_of_finrank_le_one _ hQ)

/-- Circuit-facing zero-defect specialization. -/
theorem allQuadraticPrefix_targetRank_le_three_of_flagDefect_eq_zero
    {r j : Nat} (C : Circuit 10 r) (hj : j ≤ r)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10)
    (hdef : N4.flagDefectRank
      (N4.circuitFlag C j) (mulTarget 5) = 0) :
    N4.flagTargetRank (N4.circuitFlag C j) (mulTarget 5) ≤ 3 := by
  let hflat := quadraticPrefixFlattening_of_all_quadratic C hj hall
  have hQ : Module.finrank F₂ (presentationDefect hflat.generator) = 0 := by
    rw [quadraticPrefixFlattening_defect_eq_flagDefect C hflat hall]
    exact hdef
  exact (flattenedPrefix_targetRank_le_capacity C hflat).trans
    (targetCapacity_le_three_of_finrank_eq_zero _ hQ)

end
end N5
end UnrestrictedBooleanMul
