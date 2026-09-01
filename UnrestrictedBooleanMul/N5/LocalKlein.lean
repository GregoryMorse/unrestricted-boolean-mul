import UnrestrictedBooleanMul.N5.HankelSupport

/-!
# Local Klein-quadric calculations

The local four-dimensional exterior space has six Pluecker coordinates
`(a,b,c,d,e,f)`.  Both closed-place calculations below are substitutions in
the Klein equation `a*f + b*e + c*d = 0`.  The only finite reductions have two
binary variables; the eleven and ten counts are then taken over the four
canonical quotient coordinates.  No externally generated table is imported.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Six Pluecker coordinates on `Lambda^2(F_2^4)`. -/
abbrev LocalKleinCoord := Fin 6 → F₂

/-- Four canonical coordinates on a quotient by a local target plane. -/
abbrev LocalKleinParam := Fin 4 → F₂

/-- The two coefficients of a point in a local target plane. -/
abbrev LocalTargetParam := Fin 2 → F₂

/-- The Klein equation in characteristic two. -/
def SatisfiesKlein (p : LocalKleinCoord) : Prop :=
  p 0 * p 5 + p 1 * p 4 + p 2 * p 3 = 0

instance satisfiesKleinDecidable (p : LocalKleinCoord) :
    Decidable (SatisfiesKlein p) := by
  unfold SatisfiesKlein
  infer_instance

private theorem add_eq_zero_iff_right_eq (x y : F₂) :
    x + y = 0 ↔ y = x := by
  rw [← CharTwo.sub_eq_add, sub_eq_zero, eq_comm]

/-- A canonical rational-double-point quotient representative, translated by
`alpha * b + beta * (c+d)`.  The quotient coordinates are `(a,g,e,f)`. -/
def rationalLocalPoint (q : LocalKleinParam) (z : LocalTargetParam) :
    LocalKleinCoord :=
  ![q 0, z 0, q 1 + z 1, z 1, q 2, q 3]

/-- A canonical degree-two quotient representative, translated by
`alpha * (b+e) + beta * (c+d+e)`.  The quotient coordinates are `(a,g,h,f)`. -/
def degreeTwoLocalPoint (q : LocalKleinParam) (z : LocalTargetParam) :
    LocalKleinCoord :=
  ![q 0, z 0, z 1, q 1 + z 1, q 2 + z 0 + z 1, q 3]

/-- Substitution of the doubled-rational local plane into the Klein equation.
This is the algebraic calculation underlying the first table in Lemma 5.2. -/
theorem rationalLocalPoint_klein_iff (q : LocalKleinParam)
    (z : LocalTargetParam) :
    SatisfiesKlein (rationalLocalPoint q z) ↔
      q 2 * z 0 + (q 1 + 1) * z 1 = q 0 * q 3 := by
  change q 0 * q 3 + z 0 * q 2 + (q 1 + z 1) * z 1 = 0 ↔ _
  have hz := N3Certificate.mul_self_f2 (z 1)
  have hpoly :
      q 0 * q 3 + z 0 * q 2 + (q 1 + z 1) * z 1 =
        q 0 * q 3 + (q 2 * z 0 + (q 1 + 1) * z 1) := by
    rw [add_mul, hz]
    ring
  rw [hpoly]
  exact add_eq_zero_iff_right_eq _ _

/-- Substitution of the degree-two local plane into the Klein equation. -/
theorem degreeTwoLocalPoint_klein_iff (q : LocalKleinParam)
    (z : LocalTargetParam) :
    SatisfiesKlein (degreeTwoLocalPoint q z) ↔
      z 0 * z 1 + (q 2 + 1) * z 0 + (q 1 + 1) * z 1 =
        q 0 * q 3 := by
  change q 0 * q 3 + z 0 * (q 2 + z 0 + z 1) +
      z 1 * (q 1 + z 1) = 0 ↔ _
  have h0 := N3Certificate.mul_self_f2 (z 0)
  have h1 := N3Certificate.mul_self_f2 (z 1)
  have hpoly :
      q 0 * q 3 + z 0 * (q 2 + z 0 + z 1) +
          z 1 * (q 1 + z 1) =
        q 0 * q 3 +
          (z 0 * z 1 + (q 2 + 1) * z 0 + (q 1 + 1) * z 1) := by
    calc
      _ = q 0 * q 3 + (z 0 * q 2 + z 0 * z 0 + z 0 * z 1) +
          (z 1 * q 1 + z 1 * z 1) := by ring
      _ = _ := by rw [h0, h1]; ring
  rw [hpoly]
  exact add_eq_zero_iff_right_eq _ _

private def binaryLinearFiber (A B C : F₂) : Finset LocalTargetParam :=
  Finset.univ.filter fun z => A * z 0 + B * z 1 = C

private def binaryQuadraticFiber (A B C : F₂) : Finset LocalTargetParam :=
  Finset.univ.filter fun z => z 0 * z 1 + A * z 0 + B * z 1 = C

/-- A binary linear equation has four solutions in the zero equation, none in
the inconsistent constant equation, and two otherwise. -/
private theorem binaryLinearFiber_card (A B C : F₂) :
    (binaryLinearFiber A B C).card =
      if A = 0 ∧ B = 0 then (if C = 0 then 4 else 0) else 2 := by
  rcases f2_eq_zero_or_one A with rfl | rfl <;>
    rcases f2_eq_zero_or_one B with rfl | rfl <;>
      rcases f2_eq_zero_or_one C with rfl | rfl <;> decide

/-- The affine binary Klein equation has three solutions exactly when its
constant is `A*B`, and one solution otherwise. -/
private theorem binaryQuadraticFiber_card (A B C : F₂) :
    (binaryQuadraticFiber A B C).card =
      if C = A * B then 3 else 1 := by
  rcases f2_eq_zero_or_one A with rfl | rfl <;>
    rcases f2_eq_zero_or_one B with rfl | rfl <;>
      rcases f2_eq_zero_or_one C with rfl | rfl <;> decide

/-- The decomposable points in a doubled-rational local quotient fiber. -/
def rationalKleinFiber (q : LocalKleinParam) : Finset LocalTargetParam :=
  Finset.univ.filter fun z => SatisfiesKlein (rationalLocalPoint q z)

/-- The decomposable points in a degree-two local quotient fiber. -/
def degreeTwoKleinFiber (q : LocalKleinParam) : Finset LocalTargetParam :=
  Finset.univ.filter fun z => SatisfiesKlein (degreeTwoLocalPoint q z)

/-- Exact doubled-rational fiber size after eliminating the local target
coordinates. -/
theorem rationalKleinFiber_card (q : LocalKleinParam) :
    (rationalKleinFiber q).card =
      if q 2 = 0 ∧ q 1 + 1 = 0 then
        (if q 0 * q 3 = 0 then 4 else 0)
      else 2 := by
  have hfiber : rationalKleinFiber q =
      binaryLinearFiber (q 2) (q 1 + 1) (q 0 * q 3) := by
    ext z
    simp only [rationalKleinFiber, binaryLinearFiber, Finset.mem_filter,
      Finset.mem_univ, true_and, rationalLocalPoint_klein_iff]
  rw [hfiber, binaryLinearFiber_card]

/-- Exact degree-two fiber size after eliminating the local target
coordinates. -/
theorem degreeTwoKleinFiber_card (q : LocalKleinParam) :
    (degreeTwoKleinFiber q).card =
      if q 0 * q 3 = (q 2 + 1) * (q 1 + 1) then 3 else 1 := by
  have hfiber : degreeTwoKleinFiber q =
      binaryQuadraticFiber (q 2 + 1) (q 1 + 1) (q 0 * q 3) := by
    ext z
    simp only [degreeTwoKleinFiber, binaryQuadraticFiber,
      Finset.mem_filter, Finset.mem_univ, true_and,
      degreeTwoLocalPoint_klein_iff]
  rw [hfiber, binaryQuadraticFiber_card]

/-- Symbolic criterion for a doubled-rational quotient fiber to contain a
pair whose difference has a nonzero first-jet component. -/
def RationalLocalEffective (q : LocalKleinParam) : Prop :=
  q 2 = 1 ∨ (q 2 = 0 ∧ q 1 = 1 ∧ q 0 * q 3 = 0)

/-- Symbolic criterion for a degree-two quotient fiber to be nonsingleton. -/
def DegreeTwoLocalEffective (q : LocalKleinParam) : Prop :=
  q 0 * q 3 = (q 2 + 1) * (q 1 + 1)

/-- A rational local fiber contains two decomposable points separated in the
first-jet coordinate of its target plane. -/
def RationalHasJetDifference (q : LocalKleinParam) : Prop :=
  ∃ z ∈ rationalKleinFiber q, ∃ w ∈ rationalKleinFiber q, z 1 ≠ w 1

instance rationalLocalEffectiveDecidable (q : LocalKleinParam) :
    Decidable (RationalLocalEffective q) := by
  unfold RationalLocalEffective
  infer_instance

instance degreeTwoLocalEffectiveDecidable (q : LocalKleinParam) :
    Decidable (DegreeTwoLocalEffective q) := by
  unfold DegreeTwoLocalEffective
  infer_instance

instance rationalHasJetDifferenceDecidable (q : LocalKleinParam) :
    Decidable (RationalHasJetDifference q) := by
  unfold RationalHasJetDifference
  infer_instance

/-- Effectiveness at a doubled rational point is exactly separation by the
first-jet direction; this removes the ineffective two-point fibers from the
raw size table. -/
theorem rationalHasJetDifference_iff (q : LocalKleinParam) :
    RationalHasJetDifference q ↔ RationalLocalEffective q := by
  rcases f2_eq_zero_or_one (q 0) with h0 | h0 <;>
    rcases f2_eq_zero_or_one (q 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (q 2) with h2 | h2 <;>
        rcases f2_eq_zero_or_one (q 3) with h3 | h3 <;>
          simp [RationalHasJetDifference, rationalKleinFiber,
            rationalLocalPoint_klein_iff, RationalLocalEffective,
            h0, h1, h2, h3] <;> decide

/-- At the degree-two place every nonsingleton local Klein fiber is effective. -/
theorem degreeTwoLocalEffective_iff_card (q : LocalKleinParam) :
    DegreeTwoLocalEffective q ↔ (degreeTwoKleinFiber q).card = 3 := by
  rw [degreeTwoKleinFiber_card]
  unfold DegreeTwoLocalEffective
  split <;> simp_all

def rationalEffectiveParams : Finset LocalKleinParam :=
  Finset.univ.filter RationalLocalEffective

def degreeTwoEffectiveParams : Finset LocalKleinParam :=
  Finset.univ.filter DegreeTwoLocalEffective

/-- Lemma 5.2, doubled-rational local Klein count.  Reduction ranges over the
four canonical quotient bits, after the preceding symbolic elimination of the
two target-plane bits. -/
theorem rationalEffectiveParams_card : rationalEffectiveParams.card = 11 := by
  decide

/-- Lemma 5.2, degree-two local Klein count. -/
theorem degreeTwoEffectiveParams_card : degreeTwoEffectiveParams.card = 10 := by
  decide

/-- The four place-local counts, with the first three entries identified by
the rational-place coordinate symmetry. -/
def localKleinCounts : Fin 4 → Nat :=
  ![rationalEffectiveParams.card, rationalEffectiveParams.card,
    rationalEffectiveParams.card, degreeTwoEffectiveParams.card]

/-- Manuscript Lemma 5.2: the local counts are `11,11,11,10`. -/
theorem localKlein_counts : localKleinCounts = ![11, 11, 11, 10] := by
  funext i
  fin_cases i <;>
    simp [localKleinCounts, rationalEffectiveParams_card,
      degreeTwoEffectiveParams_card]

end

end N5
end UnrestrictedBooleanMul
