import UnrestrictedBooleanMul.N5.EnvelopeBasisChange

/-!
# Coordinate assembly for the first-order n=5 envelope

This module connects ambient low-product data to the sparse Plücker-kernel
classification already proved in `EnvelopeKernel`.  It only chooses
coordinates in the fixed eight-dimensional envelope and evaluates one
symbolic exterior block; it performs no finite circuit or assignment search.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Linear coordinate realization of the exact first-order envelope inside
the ambient quadratic space. -/
def exactFirstOrderTwoMap : (Fin 8 → F₂) →ₗ[F₂] TwoForm :=
  targetTwoLinear.comp
    (Fintype.linearCombination F₂ exactFirstOrderDirections)

@[simp] theorem exactFirstOrderTwoMap_apply (x : Fin 8 → F₂) :
    exactFirstOrderTwoMap x =
      targetTwo (exactFirstOrderCombination x) := by
  simp [exactFirstOrderTwoMap, exactFirstOrderCombination,
    Fintype.linearCombination_apply, targetTwo]

theorem exactFirstOrderTwoMap_injective :
    Function.Injective exactFirstOrderTwoMap :=
  targetTwoLinear_injective.comp
    exactFirstOrderDirections_linearIndependent.fintypeLinearCombination_injective

/-- Index of the unordered pair in the fixed lexicographic pair table.
Diagonal entries are arbitrary and are never used. -/
private def firstOrderPairIndex (i j : Fin 8) : Fin 28 :=
  ![![0, 0, 1, 2, 3, 4, 5, 6],
    ![0, 0, 7, 8, 9, 10, 11, 12],
    ![1, 7, 0, 13, 14, 15, 16, 17],
    ![2, 8, 13, 0, 18, 19, 20, 21],
    ![3, 9, 14, 18, 0, 22, 23, 24],
    ![4, 10, 15, 19, 22, 0, 25, 26],
    ![5, 11, 16, 20, 23, 25, 0, 27],
    ![6, 12, 17, 21, 24, 26, 27, 0]] i j

/-- Every distinct pair of exact first-order basis indices occurs, in one
of its two orientations, in the fixed lexicographic pair table. -/
private theorem exists_firstOrderPair_of_ne
    (i j : Fin 8) (hij : i ≠ j) :
    ∃ k : Fin 28,
      (firstOrderPairLeft k = i ∧ firstOrderPairRight k = j) ∨
      (firstOrderPairLeft k = j ∧ firstOrderPairRight k = i) := by
  refine ⟨firstOrderPairIndex i j, ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [firstOrderPairIndex, firstOrderPairLeft,
      firstOrderPairRight]

/-- Equality of the lexicographically ordered Pluecker coordinates is
exactly equality of the corresponding squarefree exterior two-forms. -/
theorem squarefreeWedge_eq_of_firstOrderPlaneCoeff_eq
    (x y z w : Fin 8 → F₂)
    (h : firstOrderPlaneCoeff x y = firstOrderPlaneCoeff z w) :
    squarefreeWedge x y = squarefreeWedge z w := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  rcases exists_firstOrderPair_of_ne i j hij with
    ⟨k, ⟨hki, hkj⟩ | ⟨hkj, hki⟩⟩
  · have hk := congrFun h k
    simpa [squarefreeWedge_pair, firstOrderPlaneCoeff, hki, hkj] using hk
  · have hk := congrFun h k
    simpa [squarefreeWedge_pair, firstOrderPlaneCoeff, hki, hkj,
      add_comm] using hk

/-- The manuscript stores a quadratic plane as `[c,q]`; swapping its two
independent generators preserves linear independence. -/
private theorem orderedQuadraticPair_linearIndependent
    (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    LinearIndependent F₂ ![q, c] := by
  rcases quadraticPlaneDirections_independent_nonzero_ne q c hind with
    ⟨hq, hc, hqc⟩
  rw [linearIndependent_fin2]
  change c ≠ 0 ∧ ∀ a : F₂, a • c ≠ q
  refine ⟨hc, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hq
  · simpa using Ne.symm hqc

/-- Independent quadratic factors in the exact envelope have independent
coordinates because the coordinate realization is injective. -/
theorem exactFirstOrderCoordinates_linearIndependent
    (q c : TwoForm) (x y : Fin 8 → F₂)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    LinearIndependent F₂ ![x, y] := by
  rcases quadraticPlaneDirections_independent_nonzero_ne q c hind with
    ⟨hq, hc, hqc⟩
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hq
    calc
      q = exactFirstOrderTwoMap x := hx
      _ = exactFirstOrderTwoMap 0 := congrArg exactFirstOrderTwoMap hx0
      _ = 0 := exactFirstOrderTwoMap.map_zero
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hc
    calc
      c = exactFirstOrderTwoMap y := hy
      _ = exactFirstOrderTwoMap 0 := congrArg exactFirstOrderTwoMap hy0
      _ = 0 := exactFirstOrderTwoMap.map_zero
  have hxy : x ≠ y := by
    intro hxy
    apply hqc
    rw [hx, hy, hxy]
  rw [linearIndependent_fin2]
  change y ≠ 0 ∧ ∀ a : F₂, a • y ≠ x
  refine ⟨hy0, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hx0
  · simpa using Ne.symm hxy

/-- In characteristic two, a zero sum of the two Pluecker vectors forces
equality of the coefficient planes. -/
theorem firstOrderCoordinate_span_eq_of_planeCoeff_add_eq_zero
    (x y z w : Fin 8 → F₂)
    (hxy : LinearIndependent F₂ ![x, y])
    (hzw : LinearIndependent F₂ ![z, w])
    (hzero : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff z w = 0) :
    Submodule.span F₂ (Set.range ![x, y]) =
      Submodule.span F₂ (Set.range ![z, w]) := by
  have hcoeff : firstOrderPlaneCoeff x y =
      firstOrderPlaneCoeff z w := by
    funext k
    exact CharTwo.add_eq_zero.mp (congrFun hzero k)
  have hwedge := squarefreeWedge_eq_of_firstOrderPlaneCoeff_eq
    x y z w hcoeff
  have hsupport := congrArg quadraticSupport hwedge
  rw [quadraticSupport_squarefreeWedge x y hxy,
    quadraticSupport_squarefreeWedge z w hzw] at hsupport
  exact hsupport

private theorem range_finTwo_eq_pair {V : Type*} (u v : V) :
    Set.range ![u, v] = ({u, v} : Set V) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- Equality of coefficient spans lifts through the exact first-order
coordinate map to equality of the represented quadratic planes. -/
theorem quadraticPlane_span_eq_of_firstOrderCoordinate_span_eq
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hspan : Submodule.span F₂ (Set.range ![x, y]) =
      Submodule.span F₂ (Set.range ![z, w])) :
    Submodule.span F₂ ({q, c} : Set TwoForm) =
      Submodule.span F₂ ({q', c'} : Set TwoForm) := by
  rw [range_finTwo_eq_pair, range_finTwo_eq_pair] at hspan
  have hmap := congrArg
    (fun P : Submodule F₂ (Fin 8 → F₂) =>
      P.map exactFirstOrderTwoMap) hspan
  simpa only [Submodule.map_span, Set.image_insert_eq,
    Set.image_singleton, ← hx, ← hy, ← hz, ← hw] using hmap

/-- The zero local-kernel branch of the Pluecker comparison is exactly the
equal-plane case, hence differs by one of the six ordered basis changes. -/
theorem exists_planeBasisChange_of_firstOrderPlaneCoeff_add_eq_zero
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂)
    (hx : q = targetTwo (exactFirstOrderCombination x))
    (hy : c = targetTwo (exactFirstOrderCombination y))
    (hz : q' = targetTwo (exactFirstOrderCombination z))
    (hw : c' = targetTwo (exactFirstOrderCombination w))
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hzero : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff z w = 0) :
    ∃ g : PlaneBasisChange,
      q' = (g.basisPair q c).1 ∧ c' = (g.basisPair q c).2 := by
  have hxMap : q = exactFirstOrderTwoMap x := by simpa using hx
  have hyMap : c = exactFirstOrderTwoMap y := by simpa using hy
  have hzMap : q' = exactFirstOrderTwoMap z := by simpa using hz
  have hwMap : c' = exactFirstOrderTwoMap w := by simpa using hw
  have hxy := exactFirstOrderCoordinates_linearIndependent
    q c x y hxMap hyMap hind
  have hzw := exactFirstOrderCoordinates_linearIndependent
    q' c' z w hzMap hwMap hind'
  have hcoeffSpan :=
    firstOrderCoordinate_span_eq_of_planeCoeff_add_eq_zero
      x y z w hxy hzw hzero
  have hplaneSpan :=
    quadraticPlane_span_eq_of_firstOrderCoordinate_span_eq
      q c q' c' x y z w hxMap hyMap hzMap hwMap hcoeffSpan
  exact exists_planeBasisChange_of_span_eq q c q' c' hind' hplaneSpan.symm

/-- Every two-form in the first-order envelope has coordinates in the exact
eight-direction basis. -/
theorem exists_exactFirstOrderTwoCombination
    (q : TwoForm) (hq : q ∈ firstOrderEnvelopeTwoSpace) :
    ∃ x : Fin 8 → F₂, q = targetTwo (exactFirstOrderCombination x) := by
  rcases hq with ⟨d, hd, hdq⟩
  rcases exists_exactFirstOrderCombination d hd with ⟨x, hxd⟩
  refine ⟨x, ?_⟩
  rw [hxd]
  exact hdq.symm

/-- The `2A,2B` coordinate block of the ambient exterior product of two
target forms is exactly `targetCrossWedge`. -/
theorem ambientWedgeTwo_targetTwo_cross
    (d e : TargetCoeff) (i k j l : Fin 5) :
    ambientWedgeTwo (targetTwo d) (targetTwo e)
        (aCoord i) (aCoord k) (bCoord j) (bCoord l) =
      targetCrossWedge d e i k j l := by
  have haa (t : TargetCoeff) (r s : Fin 5) :
      ambientTwoCoeff (targetTwo t) (aCoord r) (aCoord s) = 0 := by
    by_cases hrs : r = s
    · subst s
      simp
    · simp [ambientTwoCoeff, hrs]
  have hbb (t : TargetCoeff) (r s : Fin 5) :
      ambientTwoCoeff (targetTwo t) (bCoord r) (bCoord s) = 0 := by
    by_cases hrs : r = s
    · subst s
      simp
    · simp [ambientTwoCoeff, hrs]
  simp [ambientWedgeTwo, targetCrossWedge, crossWedge, hankelMatrix,
    haa, hbb]

/-- Ambient quartic equality between target forms implies equality in the
cross-wedge coordinate model used by the envelope kernel theorem. -/
theorem targetCrossWedge_eq_of_ambientWedgeTwo_eq
    (d e d' e' : TargetCoeff)
    (hfour : ambientWedgeTwo (targetTwo d) (targetTwo e) =
      ambientWedgeTwo (targetTwo d') (targetTwo e')) :
    targetCrossWedge d e = targetCrossWedge d' e' := by
  funext i k j l
  rw [← ambientWedgeTwo_targetTwo_cross,
    ← ambientWedgeTwo_targetTwo_cross]
  exact congrFun (congrFun (congrFun (congrFun hfour (aCoord i))
    (aCoord k)) (bCoord j)) (bCoord l)

/-- Coordinate realization of four quadratic factors in the first-order
envelope, together with the three sparse possibilities for their Plücker
difference. -/
theorem firstOrderPlaneCoeff_classification_of_ambientWedge_eq
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hfour : ambientWedgeTwo q c = ambientWedgeTwo q' c') :
    ∃ x y z w : Fin 8 → F₂,
      q = targetTwo (exactFirstOrderCombination x) ∧
      c = targetTwo (exactFirstOrderCombination y) ∧
      q' = targetTwo (exactFirstOrderCombination z) ∧
      c' = targetTwo (exactFirstOrderCombination w) ∧
      (firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w = 0 ∨
        (∃ i : Fin 3, firstOrderPlaneCoeff x y +
          firstOrderPlaneCoeff z w = firstOrderLocalKernelDirections i) ∨
        ∃ i j : Fin 3, i ≠ j ∧
          firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
            firstOrderLocalKernelDirections i +
              firstOrderLocalKernelDirections j) := by
  rcases exists_exactFirstOrderTwoCombination q hq with ⟨x, hx⟩
  rcases exists_exactFirstOrderTwoCombination c hc with ⟨y, hy⟩
  rcases exists_exactFirstOrderTwoCombination q' hq' with ⟨z, hz⟩
  rcases exists_exactFirstOrderTwoCombination c' hc' with ⟨w, hw⟩
  refine ⟨x, y, z, w, hx, hy, hz, hw, ?_⟩
  apply firstOrderPlaneCoeff_difference_classification x y z w
  apply targetCrossWedge_eq_of_ambientWedgeTwo_eq
  simpa only [← hx, ← hy, ← hz, ← hw] using hfour

/-- Refined ambient quartic classification for two independent quadratic
planes.  The zero Pluecker difference has already been converted to an
actual basis change; only the one- and two-local-rotation branches remain. -/
theorem independentFirstOrderPlane_classification_of_ambientWedge_eq
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hfour : ambientWedgeTwo q c = ambientWedgeTwo q' c') :
    (∃ g : PlaneBasisChange,
      q' = (g.basisPair q c).1 ∧ c' = (g.basisPair q c).2) ∨
    ∃ x y z w : Fin 8 → F₂,
      q = targetTwo (exactFirstOrderCombination x) ∧
      c = targetTwo (exactFirstOrderCombination y) ∧
      q' = targetTwo (exactFirstOrderCombination z) ∧
      c' = targetTwo (exactFirstOrderCombination w) ∧
      ((∃ i : Fin 3, firstOrderPlaneCoeff x y +
          firstOrderPlaneCoeff z w = firstOrderLocalKernelDirections i) ∨
        ∃ i j : Fin 3, i ≠ j ∧
          firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
            firstOrderLocalKernelDirections i +
              firstOrderLocalKernelDirections j) := by
  rcases firstOrderPlaneCoeff_classification_of_ambientWedge_eq
      q c q' c' hq hc hq' hc' hfour with
    ⟨x, y, z, w, hx, hy, hz, hw, hzero | hone | htwo⟩
  · exact Or.inl
      (exists_planeBasisChange_of_firstOrderPlaneCoeff_add_eq_zero
        q c q' c' x y z w hx hy hz hw hind hind' hzero)
  · exact Or.inr ⟨x, y, z, w, hx, hy, hz, hw, Or.inl hone⟩
  · exact Or.inr ⟨x, y, z, w, hx, hy, hz, hw, Or.inr htwo⟩

end

end N5
end UnrestrictedBooleanMul
