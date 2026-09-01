import UnrestrictedBooleanMul.N5.LocalSecantPivots
import UnrestrictedBooleanMul.N5.SparseAnchorGifts

/-!
# Fano line gifts as rank-four secants

For a populated Fano line, moving one chosen lift across the target-valued
sum leaves the sum of the other two decomposable lifts.  Thus every line gift
through a selected point satisfies the local rank-four secant equations at
that point.  This is the incidence bridge between sparse relation gifts and
the Pfaffian pivots.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Removing one point from a three-point Fano support leaves a named pair. -/
theorem fanoLine_exists_complementary_points
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support) :
    ∃ y z : PopulatedPoint Q,
      y ∈ r.support ∧ z ∈ r.support ∧ y ≠ z ∧
      x ≠ y ∧ x ≠ z ∧
      ∀ w, w ∈ r.support ↔ w = x ∨ w = y ∨ w = z := by
  classical
  have hcard : (r.support.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx, r.card_support]
  rcases Finset.card_eq_two.mp hcard with ⟨y, z, hyz, herase⟩
  have hyErase : y ∈ r.support.erase x := by rw [herase]; simp
  have hzErase : z ∈ r.support.erase x := by rw [herase]; simp
  have hy : y ∈ r.support := (Finset.mem_erase.mp hyErase).2
  have hz : z ∈ r.support := (Finset.mem_erase.mp hzErase).2
  have hxy : x ≠ y := (Finset.mem_erase.mp hyErase).1.symm
  have hxz : x ≠ z := (Finset.mem_erase.mp hzErase).1.symm
  refine ⟨y, z, hy, hz, hyz, hxy, hxz, fun w ↦ ?_⟩
  constructor
  · intro hw
    by_cases hwx : w = x
    · exact Or.inl hwx
    have hwErase : w ∈ r.support.erase x :=
      Finset.mem_erase.mpr ⟨hwx, hw⟩
    rw [herase] at hwErase
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwErase
    exact Or.inr hwErase
  · intro hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz

/-- The coefficient gift of a populated Fano line is a rank-four secant
correction at any chosen point of that line. -/
theorem fanoLine_gift_secant_eq
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support) :
    ∃ y z : PopulatedPoint Q,
      y ∈ r.support ∧ z ∈ r.support ∧ y ≠ z ∧
      populatedLift x + targetTwo (sparseRelationGiftCoeff Q r.1) =
        populatedLift y + populatedLift z := by
  classical
  rcases fanoLine_exists_complementary_points Q r x hx with
    ⟨y, z, hy, hz, hyz, hxy, hxz, hsupportMem⟩
  refine ⟨y, z, hy, hz, hyz, ?_⟩
  have hsupport : r.support = {x, y, z} := by
    ext w
    simpa using hsupportMem w
  have htarget := targetTwo_sparseRelationGiftCoeff Q r.1
  rw [sparseLiftSum, hsupport] at htarget
  have hxNot : x ∉ ({y, z} : Finset (PopulatedPoint Q)) := by
    simp [hxy, hxz]
  have hyNot : y ∉ ({z} : Finset (PopulatedPoint Q)) := by
    simpa using hyz
  rw [Finset.sum_insert hxNot, Finset.sum_insert hyNot,
    Finset.sum_singleton] at htarget
  rw [htarget]
  funext s
  simp only [Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Bundled two-wedge presentation of the preceding line secant. -/
theorem fanoLine_gift_has_two_wedge_secant
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support) :
    ∃ u v y z : LinearForm,
      populatedLift x + targetTwo (sparseRelationGiftCoeff Q r.1) =
        squarefreeWedge u v + squarefreeWedge y z := by
  rcases fanoLine_gift_secant_eq Q r x hx with
    ⟨p, q, _hp, _hq, _hpq, hsecant⟩
  rcases (populatedLift_mem_fiber p).1 with ⟨u, v, huv⟩
  rcases (populatedLift_mem_fiber q).1 with ⟨y, z, hyz⟩
  exact ⟨u, v, y, z, by simpa [huv, hyz] using hsecant⟩

/-- A populated Fano-line gift through an effective point of the zero
rational chart satisfies the three rational secant pivots.  The chosen
populated lift need not be the canonical local lift: its target correction
and the correction after adding the line gift both satisfy the normalized
pivot, so their difference is the gift itself. -/
theorem fanoLine_rationalZero_gift_mem
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support)
    (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint 0 q) :
    sparseRelationGiftCoeff Q r.1 ∈ rationalZeroSecantCoeffSpace := by
  let g := sparseRelationGiftCoeff Q r.1
  have hxProjection : quadraticQuotientProjection (populatedLift x) =
      closedPlaceQuotientPoint 0 q :=
    (populatedLift_projection x).trans hxPoint
  rcases exists_closedPlaceLift_add_target_of_projection_eq
      0 q (populatedLift x) hxProjection with ⟨a, ha⟩
  have haSecant : ∃ u v y z : LinearForm,
      closedPlaceLift 0 q + targetTwo a =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases (populatedLift_mem_fiber x).1 with ⟨u, v, huv⟩
    refine ⟨u, v, 0, 0, ?_⟩
    rw [← ha, huv]
    simp
  have haMem : a ∈ rationalZeroSecantCoeffSpace :=
    rationalZero_normalizedLocalSecant_mem q hq a haSecant
  have hagSecant : ∃ u v y z : LinearForm,
      closedPlaceLift 0 q + targetTwo (a + g) =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases fanoLine_gift_has_two_wedge_secant Q r x hx with
      ⟨u, v, y, z, hline⟩
    refine ⟨u, v, y, z, ?_⟩
    change closedPlaceLift 0 q + targetTwoLinear (a + g) = _
    rw [targetTwoLinear.map_add, ← add_assoc]
    change populatedLift x =
      closedPlaceLift 0 q + targetTwoLinear a at ha
    rw [← ha]
    change populatedLift x +
      targetTwoLinear (sparseRelationGiftCoeff Q r.1) = _ at hline
    simpa only [g] using hline
  have hagMem : a + g ∈ rationalZeroSecantCoeffSpace :=
    rationalZero_normalizedLocalSecant_mem q hq (a + g) hagSecant
  have hsum := rationalZeroSecantCoeffSpace.add_mem hagMem haMem
  have hcancel : (a + g) + a = g := by
    funext i
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  rw [hcancel] at hsum
  exact hsum

/-- A populated Fano-line gift through the effective degree-two place
satisfies the three norm-block secant pivots.  As in the rational case, this
is independent of the choice of populated lift. -/
theorem fanoLine_degreeTwo_gift_mem
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support)
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint 3 q) :
    sparseRelationGiftCoeff Q r.1 ∈ degreeTwoSecantCoeffSpace := by
  let g := sparseRelationGiftCoeff Q r.1
  have hxProjection : quadraticQuotientProjection (populatedLift x) =
      closedPlaceQuotientPoint 3 q :=
    (populatedLift_projection x).trans hxPoint
  rcases exists_closedPlaceLift_add_target_of_projection_eq
      3 q (populatedLift x) hxProjection with ⟨a, ha⟩
  have haSecant : ∃ u v y z : LinearForm,
      closedPlaceLift 3 q + targetTwo a =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases (populatedLift_mem_fiber x).1 with ⟨u, v, huv⟩
    refine ⟨u, v, 0, 0, ?_⟩
    rw [← ha, huv]
    simp
  have haMem : a ∈ degreeTwoSecantCoeffSpace :=
    degreeTwo_normalizedLocalSecant_mem q hq a haSecant
  have hagSecant : ∃ u v y z : LinearForm,
      closedPlaceLift 3 q + targetTwo (a + g) =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases fanoLine_gift_has_two_wedge_secant Q r x hx with
      ⟨u, v, y, z, hline⟩
    refine ⟨u, v, y, z, ?_⟩
    change closedPlaceLift 3 q + targetTwoLinear (a + g) = _
    rw [targetTwoLinear.map_add, ← add_assoc]
    change populatedLift x =
      closedPlaceLift 3 q + targetTwoLinear a at ha
    rw [← ha]
    change populatedLift x +
      targetTwoLinear (sparseRelationGiftCoeff Q r.1) = _ at hline
    simpa only [g] using hline
  have hagMem : a + g ∈ degreeTwoSecantCoeffSpace :=
    degreeTwo_normalizedLocalSecant_mem q hq (a + g) hagSecant
  have hsum := degreeTwoSecantCoeffSpace.add_mem hagMem haMem
  have hcancel : (a + g) + a = g := by
    funext i
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  rw [hcancel] at hsum
  exact hsum

end

end N5
end UnrestrictedBooleanMul
