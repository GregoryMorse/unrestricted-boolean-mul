import UnrestrictedBooleanMul.N5.EnvelopeRotationShadow

/-!
# The two-rotation chain in the first-order envelope

This module develops the algebraic incidence statement behind the weight-two
branch of manuscript Lemma 11.2.  No circuit or assignment space is searched:
the argument uses the rank-four support of the sum of two distinct rational
value--jet planes and the three relevant Pluecker relations.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The four coordinate directions belonging to two ordered rational
value--jet planes. -/
def twoLocalCoordinateFrame (i j : Fin 3) : Fin 4 → (Fin 8 → F₂) :=
  ![firstOrderLocalValueCoordinates i,
    firstOrderLocalJetCoordinates i,
    firstOrderLocalValueCoordinates j,
    firstOrderLocalJetCoordinates j]

/-- Distinct rational value--jet coordinate planes have a four-dimensional
direct-sum frame. -/
theorem twoLocalCoordinateFrame_linearIndependent
    (i j : Fin 3) (hij : i ≠ j) :
    LinearIndependent F₂ (twoLocalCoordinateFrame i j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h0 := congrFun hg (0 : Fin 8)
  have h1 := congrFun hg (1 : Fin 8)
  have h2 := congrFun hg (2 : Fin 8)
  have h3 := congrFun hg (3 : Fin 8)
  have h4 := congrFun hg (4 : Fin 8)
  have h5 := congrFun hg (5 : Fin 8)
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [twoLocalCoordinateFrame, firstOrderLocalValueCoordinates,
      firstOrderLocalJetCoordinates, Fin.sum_univ_succ, Pi.basisFun]

def firstOrderLocalValueIndex : Fin 3 → Fin 8 := ![0, 1, 2]

def firstOrderLocalJetIndex : Fin 3 → Fin 8 := ![3, 4, 5]

/-- Projection to the two coordinate slots of one rational value--jet
plane. -/
def firstOrderLocalProjection (i : Fin 3) :
    (Fin 8 → F₂) →ₗ[F₂] (Fin 2 → F₂) where
  toFun x := ![x (firstOrderLocalValueIndex i),
    x (firstOrderLocalJetIndex i)]
  map_add' x y := by
    funext k
    fin_cases k <;> rfl
  map_smul' a x := by
    funext k
    fin_cases k <;> rfl

/-- The distinguished Pluecker coordinate of each rational local plane. -/
def firstOrderLocalPlueckerIndex : Fin 3 → Fin 28 := ![2, 9, 15]

theorem firstOrderLocalProjection_det
    (i : Fin 3) (x y : Fin 8 → F₂) :
    firstOrderLocalProjection i x 0 * firstOrderLocalProjection i y 1 +
        firstOrderLocalProjection i x 1 * firstOrderLocalProjection i y 0 =
      firstOrderPlaneCoeff x y (firstOrderLocalPlueckerIndex i) := by
  fin_cases i <;>
    simp [firstOrderLocalProjection, firstOrderLocalPlueckerIndex,
      firstOrderLocalValueIndex, firstOrderLocalJetIndex,
      firstOrderPlaneCoeff, firstOrderPairLeft, firstOrderPairRight]

/-- A singular two-by-two matrix over `F₂` has zero, zero, or equal rows. -/
theorem finTwo_det_zero_cases (u v : Fin 2 → F₂)
    (hdet : u 0 * v 1 + u 1 * v 0 = 0) :
    u = 0 ∨ v = 0 ∨ u = v := by
  rcases f2_eq_zero_or_one (u 0) with hu0 | hu0 <;>
    rcases f2_eq_zero_or_one (u 1) with hu1 | hu1 <;>
      rcases f2_eq_zero_or_one (v 0) with hv0 | hv0 <;>
        rcases f2_eq_zero_or_one (v 1) with hv1 | hv1
  all_goals
    simp_all [funext_iff]

/-- Inside the direct sum of two local coordinate planes, vanishing of the
first projection places a vector in the second plane. -/
theorem mem_secondLocalSpan_of_mem_twoLocalSpan_of_projection_zero
    (i j : Fin 3) (hij : i ≠ j) (p : Fin 8 → F₂)
    (hp : p ∈ Submodule.span F₂ (Set.range (twoLocalCoordinateFrame i j)))
    (hproj : firstOrderLocalProjection i p = 0) :
    p ∈ Submodule.span F₂
      ({firstOrderLocalValueCoordinates j,
        firstOrderLocalJetCoordinates j} : Set (Fin 8 → F₂)) := by
  rcases (Submodule.mem_span_range_iff_exists_fun F₂).mp hp with ⟨a, ha⟩
  apply Submodule.mem_span_pair.mpr
  refine ⟨a 2, a 3, ?_⟩
  have h0 := congrFun hproj 0
  have h1 := congrFun hproj 1
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    funext k
    have hak := congrFun ha k
    fin_cases k <;>
      simp [twoLocalCoordinateFrame, firstOrderLocalProjection,
        firstOrderLocalValueIndex, firstOrderLocalJetIndex,
        firstOrderLocalValueCoordinates, firstOrderLocalJetCoordinates,
        Fin.sum_univ_succ, Pi.basisFun] at hak h0 h1 ⊢ <;>
      simp_all

/-- Symmetric form: vanishing of the second projection places the vector in
the first local plane. -/
theorem mem_firstLocalSpan_of_mem_twoLocalSpan_of_projection_zero
    (i j : Fin 3) (hij : i ≠ j) (p : Fin 8 → F₂)
    (hp : p ∈ Submodule.span F₂ (Set.range (twoLocalCoordinateFrame i j)))
    (hproj : firstOrderLocalProjection j p = 0) :
    p ∈ Submodule.span F₂
      ({firstOrderLocalValueCoordinates i,
        firstOrderLocalJetCoordinates i} : Set (Fin 8 → F₂)) := by
  have hji : j ≠ i := Ne.symm hij
  have hframe : Set.range (twoLocalCoordinateFrame i j) =
      Set.range (twoLocalCoordinateFrame j i) := by
    ext p
    simp only [Set.mem_range, twoLocalCoordinateFrame]
    constructor <;> rintro ⟨k, rfl⟩ <;> fin_cases k
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  apply mem_secondLocalSpan_of_mem_twoLocalSpan_of_projection_zero
    j i hji p
  · rwa [← hframe]
  · exact hproj

/-- A weight-two local-kernel difference has rank-four support.  Consequently
all four endpoints lie in, and form a basis of, the direct sum of the two
local coordinate planes. -/
theorem twoLocalKernelDifference_span_eq
    (x y z w : Fin 8 → F₂) (i j : Fin 3) (hij : i ≠ j)
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections i +
        firstOrderLocalKernelDirections j) :
    LinearIndependent F₂ ![x, y, z, w] ∧
      Submodule.span F₂ (Set.range ![x, y, z, w]) =
        Submodule.span F₂ (Set.range (twoLocalCoordinateFrame i j)) := by
  let vi := firstOrderLocalValueCoordinates i
  let ti := firstOrderLocalJetCoordinates i
  let vj := firstOrderLocalValueCoordinates j
  let tj := firstOrderLocalJetCoordinates j
  have hcoeff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderPlaneCoeff vi ti + firstOrderPlaneCoeff vj tj := by
    rw [firstOrderPlaneCoeff_localCoordinates,
      firstOrderPlaneCoeff_localCoordinates]
    exact hdiff
  have hwedge : squarefreeWedge x y + squarefreeWedge z w =
      squarefreeWedge vi ti + squarefreeWedge vj tj :=
    squarefreeWedge_add_eq_add_of_firstOrderPlaneCoeff_add_eq_add
      x y z w vi ti vj tj hcoeff
  have hlocal : LinearIndependent F₂ ![vi, ti, vj, tj] := by
    simpa [vi, ti, vj, tj, twoLocalCoordinateFrame] using
      twoLocalCoordinateFrame_linearIndependent i j hij
  have hrankLocal : Module.finrank F₂
      (quadraticSupport
        (squarefreeWedge vi ti + squarefreeWedge vj tj)) = 4 := by
    rw [quadraticSupport_two_wedges vi ti vj tj hlocal]
    simpa using finrank_span_eq_card hlocal
  have hrank : Module.finrank F₂
      (quadraticSupport
        (squarefreeWedge x y + squarefreeWedge z w)) = 4 := by
    rw [hwedge]
    exact hrankLocal
  have hfour : LinearIndependent F₂ ![x, y, z, w] :=
    linearIndependent_of_two_wedge_support_finrank_four x y z w hrank
  refine ⟨hfour, ?_⟩
  calc
    Submodule.span F₂ (Set.range ![x, y, z, w]) =
        quadraticSupport
          (squarefreeWedge x y + squarefreeWedge z w) :=
      (quadraticSupport_two_wedges x y z w hfour).symm
    _ = quadraticSupport
          (squarefreeWedge vi ti + squarefreeWedge vj tj) :=
      congrArg quadraticSupport hwedge
    _ = Submodule.span F₂ (Set.range ![vi, ti, vj, tj]) :=
      quadraticSupport_two_wedges vi ti vj tj hlocal
    _ = Submodule.span F₂
          (Set.range (twoLocalCoordinateFrame i j)) := by
      rfl

/-- The two local Pluecker coordinates of the first endpoint have opposite
values.  This is the single four-coordinate Pluecker relation which selects
the intermediate plane in the two-rotation chain. -/
theorem twoLocalKernelDifference_pluecker_sum_eq_one
    (x y z w : Fin 8 → F₂) (i j : Fin 3) (hij : i ≠ j)
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections i +
        firstOrderLocalKernelDirections j) :
    firstOrderPlaneCoeff x y (firstOrderLocalPlueckerIndex i) +
        firstOrderPlaneCoeff x y (firstOrderLocalPlueckerIndex j) = 1 := by
  have hbeta : firstOrderPlaneCoeff z w =
      firstOrderPlaneCoeff x y +
        (firstOrderLocalKernelDirections i +
          firstOrderLocalKernelDirections j) := by
    funext k
    have hk := congrFun hdiff k
    calc
      firstOrderPlaneCoeff z w k =
          firstOrderPlaneCoeff z w k + 0 := (add_zero _).symm
      _ = firstOrderPlaneCoeff z w k +
          (firstOrderPlaneCoeff x y k +
            firstOrderPlaneCoeff x y k) := by
        rw [CharTwo.add_self_eq_zero]
      _ = firstOrderPlaneCoeff x y k +
          (firstOrderPlaneCoeff x y k +
            firstOrderPlaneCoeff z w k) := by ac_rfl
      _ = firstOrderPlaneCoeff x y k +
          (firstOrderPlaneCoeff x y +
            firstOrderPlaneCoeff z w) k := by
        simp only [Pi.add_apply]
      _ = firstOrderPlaneCoeff x y k +
          (firstOrderLocalKernelDirections i +
            firstOrderLocalKernelDirections j) k := by rw [hk]
      _ = _ := by simp only [Pi.add_apply]
  have hab0 := firstOrderPlaneCoeff_plucker_0134 x y
  have hab1 := firstOrderPlaneCoeff_plucker_0134 z w
  have hac0 := firstOrderPlaneCoeff_plucker_0235 x y
  have hac1 := firstOrderPlaneCoeff_plucker_0235 z w
  have hbc0 := firstOrderPlaneCoeff_plucker_1245 x y
  have hbc1 := firstOrderPlaneCoeff_plucker_1245 z w
  rw [hbeta] at hab1 hac1 hbc1
  fin_cases i <;> fin_cases j <;> try contradiction
  · simp [firstOrderLocalKernelDirections, firstOrderLocalPlueckerIndex,
      Pi.basisFun] at hab1 ⊢
    ring_nf at hab0 hab1 ⊢
    have h0 : firstOrderPlaneCoeff x y 2 *
        firstOrderPlaneCoeff x y 9 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h1 : firstOrderPlaneCoeff x y 0 *
        firstOrderPlaneCoeff x y 18 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h2 : firstOrderPlaneCoeff x y 3 *
        firstOrderPlaneCoeff x y 8 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have hres : -(2 : F₂) +
        firstOrderPlaneCoeff x y 3 * firstOrderPlaneCoeff x y 8 * 2 = 0 := by
      simp [N3Certificate.two_eq_zero_f2]
    linear_combination hab0 + hab1 - h0 - h1 - h2 + hres
  · simp [firstOrderLocalKernelDirections, firstOrderLocalPlueckerIndex,
      Pi.basisFun] at hac1 ⊢
    ring_nf at hac0 hac1 ⊢
    have h0 : firstOrderPlaneCoeff x y 2 *
        firstOrderPlaneCoeff x y 15 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h1 : firstOrderPlaneCoeff x y 1 *
        firstOrderPlaneCoeff x y 19 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h2 : firstOrderPlaneCoeff x y 4 *
        firstOrderPlaneCoeff x y 13 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have hres : -(2 : F₂) +
        firstOrderPlaneCoeff x y 4 * firstOrderPlaneCoeff x y 13 * 2 = 0 := by
      simp [N3Certificate.two_eq_zero_f2]
    linear_combination hac0 + hac1 - h0 - h1 - h2 + hres
  · simp [firstOrderLocalKernelDirections, firstOrderLocalPlueckerIndex,
      Pi.basisFun] at hab1 ⊢
    ring_nf at hab0 hab1 ⊢
    have h0 : firstOrderPlaneCoeff x y 2 *
        firstOrderPlaneCoeff x y 9 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h1 : firstOrderPlaneCoeff x y 0 *
        firstOrderPlaneCoeff x y 18 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h2 : firstOrderPlaneCoeff x y 3 *
        firstOrderPlaneCoeff x y 8 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have hres : -(2 : F₂) +
        firstOrderPlaneCoeff x y 3 * firstOrderPlaneCoeff x y 8 * 2 = 0 := by
      simp [N3Certificate.two_eq_zero_f2]
    linear_combination hab0 + hab1 - h0 - h1 - h2 + hres
  · simp [firstOrderLocalKernelDirections, firstOrderLocalPlueckerIndex,
      Pi.basisFun] at hbc1 ⊢
    ring_nf at hbc0 hbc1 ⊢
    have h0 : firstOrderPlaneCoeff x y 9 *
        firstOrderPlaneCoeff x y 15 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h1 : firstOrderPlaneCoeff x y 7 *
        firstOrderPlaneCoeff x y 22 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h2 : firstOrderPlaneCoeff x y 10 *
        firstOrderPlaneCoeff x y 14 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have hres : -(2 : F₂) +
        firstOrderPlaneCoeff x y 10 * firstOrderPlaneCoeff x y 14 * 2 = 0 := by
      simp [N3Certificate.two_eq_zero_f2]
    linear_combination hbc0 + hbc1 - h0 - h1 - h2 + hres
  · simp [firstOrderLocalKernelDirections, firstOrderLocalPlueckerIndex,
      Pi.basisFun] at hac1 ⊢
    ring_nf at hac0 hac1 ⊢
    have h0 : firstOrderPlaneCoeff x y 2 *
        firstOrderPlaneCoeff x y 15 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h1 : firstOrderPlaneCoeff x y 1 *
        firstOrderPlaneCoeff x y 19 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h2 : firstOrderPlaneCoeff x y 4 *
        firstOrderPlaneCoeff x y 13 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have hres : -(2 : F₂) +
        firstOrderPlaneCoeff x y 4 * firstOrderPlaneCoeff x y 13 * 2 = 0 := by
      simp [N3Certificate.two_eq_zero_f2]
    linear_combination hac0 + hac1 - h0 - h1 - h2 + hres
  · simp [firstOrderLocalKernelDirections, firstOrderLocalPlueckerIndex,
      Pi.basisFun] at hbc1 ⊢
    ring_nf at hbc0 hbc1 ⊢
    have h0 : firstOrderPlaneCoeff x y 9 *
        firstOrderPlaneCoeff x y 15 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h1 : firstOrderPlaneCoeff x y 7 *
        firstOrderPlaneCoeff x y 22 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have h2 : firstOrderPlaneCoeff x y 10 *
        firstOrderPlaneCoeff x y 14 * 2 = 0 := by
      rw [N3Certificate.two_eq_zero_f2, mul_zero]
    have hres : -(2 : F₂) +
        firstOrderPlaneCoeff x y 10 * firstOrderPlaneCoeff x y 14 * 2 = 0 := by
      simp [N3Certificate.two_eq_zero_f2]
    linear_combination hbc0 + hbc1 - h0 - h1 - h2 + hres

/-- The Pluecker vector is invariant under each of the six ordered basis
changes of a binary plane. -/
theorem firstOrderPlaneCoeff_basisPair
    (g : PlaneBasisChange) (x y : Fin 8 → F₂) :
    firstOrderPlaneCoeff (g.basisPair x y).1 (g.basisPair x y).2 =
      firstOrderPlaneCoeff x y := by
  cases g <;>
    funext k <;>
      simp [PlaneBasisChange.basisPair, firstOrderPlaneCoeff] <;>
        ring_nf <;>
          simp [N3Certificate.two_eq_zero_f2]

theorem firstOrderPlaneCoeff_add_right
    (x y z : Fin 8 → F₂) :
    firstOrderPlaneCoeff x (y + z) =
      firstOrderPlaneCoeff x y + firstOrderPlaneCoeff x z := by
  funext k
  simp only [firstOrderPlaneCoeff, Pi.add_apply]
  ring

@[simp] theorem firstOrderPlaneCoeff_self (x : Fin 8 → F₂) :
    firstOrderPlaneCoeff x x = 0 := by
  funext k
  simp [firstOrderPlaneCoeff, mul_comm]

/-- A nonzero Pluecker vector represents an actual two-dimensional plane. -/
theorem linearIndependent_of_firstOrderPlaneCoeff_ne_zero
    (x y : Fin 8 → F₂) (hne : firstOrderPlaneCoeff x y ≠ 0) :
    LinearIndependent F₂ ![x, y] := by
  have hx0 : x ≠ 0 := by
    intro hx
    apply hne
    funext k
    simp [firstOrderPlaneCoeff, hx]
  have hy0 : y ≠ 0 := by
    intro hy
    apply hne
    funext k
    simp [firstOrderPlaneCoeff, hy]
  rw [linearIndependent_fin2]
  change y ≠ 0 ∧ ∀ a : F₂, a • y ≠ x
  refine ⟨hy0, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hx0
  · intro hyx
    apply hne
    have hyx' : y = x := by simpa using hyx
    rw [hyx']
    exact firstOrderPlaneCoeff_self x

/-- Incidence with one local plane either says that the endpoint already is
that local plane, or produces the nonzero decomposable midpoint obtained by
adding the corresponding local Pluecker vector. -/
theorem intermediatePlane_of_common_local_line
    (x y p : Fin 8 → F₂) (i : Fin 3)
    (hp0 : p ≠ 0)
    (hpA : p ∈ Submodule.span F₂
      ({x, y} : Set (Fin 8 → F₂)))
    (hpLocal : p ∈ Submodule.span F₂
      ({firstOrderLocalValueCoordinates i,
        firstOrderLocalJetCoordinates i} : Set (Fin 8 → F₂))) :
    firstOrderPlaneCoeff x y = firstOrderLocalKernelDirections i ∨
      ∃ r s : Fin 8 → F₂,
        LinearIndependent F₂ ![r, s] ∧
        firstOrderPlaneCoeff x y + firstOrderPlaneCoeff r s =
          firstOrderLocalKernelDirections i := by
  rcases exists_basisChange_first_eq_of_mem_span x y p hp0 hpA with
    ⟨g, hg⟩
  rcases exists_basisChange_first_eq_of_mem_span
      (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i) p hp0 hpLocal with
    ⟨h, hh⟩
  let q := (g.basisPair x y).2
  let t := (h.basisPair (firstOrderLocalValueCoordinates i)
    (firstOrderLocalJetCoordinates i)).2
  have hgPair : g.basisPair x y = (p, q) := Prod.ext hg rfl
  have hhPair : h.basisPair
      (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i) = (p, t) := Prod.ext hh rfl
  have hpq : firstOrderPlaneCoeff p q = firstOrderPlaneCoeff x y := by
    have hchange := firstOrderPlaneCoeff_basisPair g x y
    rwa [hgPair] at hchange
  have hpt : firstOrderPlaneCoeff p t =
      firstOrderLocalKernelDirections i := by
    have hchange := firstOrderPlaneCoeff_basisPair h
      (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i)
    rw [hhPair] at hchange
    exact hchange.trans (firstOrderPlaneCoeff_localCoordinates i)
  have hmid : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff p (q + t) =
        firstOrderLocalKernelDirections i := by
    rw [firstOrderPlaneCoeff_add_right, hpq, hpt]
    funext k
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  by_cases hzero : firstOrderPlaneCoeff p (q + t) = 0
  · left
    rwa [hzero, add_zero] at hmid
  · right
    exact ⟨p, q + t,
      linearIndependent_of_firstOrderPlaneCoeff_ne_zero p (q + t) hzero,
      hmid⟩

theorem second_difference_of_total_and_first
    (α β γ κ μ : FirstOrderPairCoeff)
    (htotal : α + β = κ + μ) (hfirst : α + γ = κ) :
    γ + β = μ := by
  funext k
  have htotalK := congrFun htotal k
  have hfirstK := congrFun hfirst k
  simp only [Pi.add_apply] at htotalK hfirstK ⊢
  calc
    γ k + β k = 0 + (γ k + β k) := (zero_add _).symm
    _ = (α k + α k) + (γ k + β k) := by
      rw [CharTwo.add_self_eq_zero]
    _ = (α k + γ k) + (α k + β k) := by ac_rfl
    _ = κ k + (κ k + μ k) := by rw [hfirstK, htotalK]
    _ = μ k := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- A weight-two local-kernel displacement forces the first factor plane to
meet one of the two rational local planes in a nonzero line.  The proof is
purely linear algebra: the four endpoint directions span the direct sum of
the two local planes, while the complementary local Pluecker coordinates
make one of the two coordinate projections singular. -/
theorem twoLocalKernelDifference_common_line
    (x y z w : Fin 8 → F₂) (i j : Fin 3) (hij : i ≠ j)
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections i +
        firstOrderLocalKernelDirections j) :
    (∃ p : Fin 8 → F₂,
      p ≠ 0 ∧
      p ∈ Submodule.span F₂ ({x, y} : Set (Fin 8 → F₂)) ∧
      p ∈ Submodule.span F₂
        ({firstOrderLocalValueCoordinates i,
          firstOrderLocalJetCoordinates i} : Set (Fin 8 → F₂))) ∨
    (∃ p : Fin 8 → F₂,
      p ≠ 0 ∧
      p ∈ Submodule.span F₂ ({x, y} : Set (Fin 8 → F₂)) ∧
      p ∈ Submodule.span F₂
        ({firstOrderLocalValueCoordinates j,
          firstOrderLocalJetCoordinates j} : Set (Fin 8 → F₂))) := by
  rcases twoLocalKernelDifference_span_eq x y z w i j hij hdiff with
    ⟨hfour, hspan⟩
  have hx0 : x ≠ 0 := hfour.ne_zero 0
  have hy0 : y ≠ 0 := hfour.ne_zero 1
  have hxy : x ≠ y := by
    intro h
    have h01 : (0 : Fin 4) = 1 := hfour.injective (by simpa using h)
    exact Fin.zero_ne_one h01
  have hxA : x ∈ Submodule.span F₂
      ({x, y} : Set (Fin 8 → F₂)) :=
    Submodule.subset_span (by simp)
  have hyA : y ∈ Submodule.span F₂
      ({x, y} : Set (Fin 8 → F₂)) :=
    Submodule.subset_span (by simp)
  have hxFrame : x ∈ Submodule.span F₂
      (Set.range (twoLocalCoordinateFrame i j)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨0, by simp⟩
  have hyFrame : y ∈ Submodule.span F₂
      (Set.range (twoLocalCoordinateFrame i j)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨1, by simp⟩
  have hsum := twoLocalKernelDifference_pluecker_sum_eq_one
    x y z w i j hij hdiff
  rcases f2_eq_zero_or_one
      (firstOrderPlaneCoeff x y (firstOrderLocalPlueckerIndex i)) with
    hi0 | hi1
  · have hdet :
        firstOrderLocalProjection i x 0 *
              firstOrderLocalProjection i y 1 +
            firstOrderLocalProjection i x 1 *
              firstOrderLocalProjection i y 0 = 0 := by
      rw [firstOrderLocalProjection_det, hi0]
    rcases finTwo_det_zero_cases
        (firstOrderLocalProjection i x)
        (firstOrderLocalProjection i y) hdet with
      hxproj | hyproj | hprojEq
    · right
      exact ⟨x, hx0, hxA,
        mem_secondLocalSpan_of_mem_twoLocalSpan_of_projection_zero
          i j hij x hxFrame hxproj⟩
    · right
      exact ⟨y, hy0, hyA,
        mem_secondLocalSpan_of_mem_twoLocalSpan_of_projection_zero
          i j hij y hyFrame hyproj⟩
    · have hsum0 : x + y ≠ 0 := by
        intro hzero
        apply hxy
        funext k
        exact CharTwo.add_eq_zero.mp (congrFun hzero k)
      have hsumA : x + y ∈ Submodule.span F₂
          ({x, y} : Set (Fin 8 → F₂)) :=
        Submodule.add_mem _ hxA hyA
      have hsumFrame : x + y ∈ Submodule.span F₂
          (Set.range (twoLocalCoordinateFrame i j)) :=
        Submodule.add_mem _ hxFrame hyFrame
      have hsumProj : firstOrderLocalProjection i (x + y) = 0 := by
        rw [map_add]
        funext k
        rw [hprojEq]
        exact CharTwo.add_self_eq_zero _
      right
      exact ⟨x + y, hsum0, hsumA,
        mem_secondLocalSpan_of_mem_twoLocalSpan_of_projection_zero
          i j hij (x + y) hsumFrame hsumProj⟩
  · have hj0 :
        firstOrderPlaneCoeff x y (firstOrderLocalPlueckerIndex j) = 0 := by
      rw [hi1] at hsum
      have hcancel := congrArg (fun t : F₂ => 1 + t) hsum
      simpa [add_assoc, CharTwo.add_self_eq_zero] using hcancel
    have hdet :
        firstOrderLocalProjection j x 0 *
              firstOrderLocalProjection j y 1 +
            firstOrderLocalProjection j x 1 *
              firstOrderLocalProjection j y 0 = 0 := by
      rw [firstOrderLocalProjection_det, hj0]
    rcases finTwo_det_zero_cases
        (firstOrderLocalProjection j x)
        (firstOrderLocalProjection j y) hdet with
      hxproj | hyproj | hprojEq
    · left
      exact ⟨x, hx0, hxA,
        mem_firstLocalSpan_of_mem_twoLocalSpan_of_projection_zero
          i j hij x hxFrame hxproj⟩
    · left
      exact ⟨y, hy0, hyA,
        mem_firstLocalSpan_of_mem_twoLocalSpan_of_projection_zero
          i j hij y hyFrame hyproj⟩
    · have hsum0 : x + y ≠ 0 := by
        intro hzero
        apply hxy
        funext k
        exact CharTwo.add_eq_zero.mp (congrFun hzero k)
      have hsumA : x + y ∈ Submodule.span F₂
          ({x, y} : Set (Fin 8 → F₂)) :=
        Submodule.add_mem _ hxA hyA
      have hsumFrame : x + y ∈ Submodule.span F₂
          (Set.range (twoLocalCoordinateFrame i j)) :=
        Submodule.add_mem _ hxFrame hyFrame
      have hsumProj : firstOrderLocalProjection j (x + y) = 0 := by
        rw [map_add]
        funext k
        rw [hprojEq]
        exact CharTwo.add_self_eq_zero _
      left
      exact ⟨x + y, hsum0, hsumA,
        mem_firstLocalSpan_of_mem_twoLocalSpan_of_projection_zero
          i j hij (x + y) hsumFrame hsumProj⟩

/-- Complete algebraic chain for a weight-two local displacement.  Either
the first endpoint is already one of the two rational local planes, or there
is an independent intermediate plane whose two consecutive differences are
the two local rotations (in one of the two possible orders). -/
theorem twoLocalKernelDifference_chain
    (x y z w : Fin 8 → F₂) (i j : Fin 3) (hij : i ≠ j)
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections i +
        firstOrderLocalKernelDirections j) :
    firstOrderPlaneCoeff x y = firstOrderLocalKernelDirections i ∨
      firstOrderPlaneCoeff x y = firstOrderLocalKernelDirections j ∨
      ∃ r s : Fin 8 → F₂,
        LinearIndependent F₂ ![r, s] ∧
        ((firstOrderPlaneCoeff x y + firstOrderPlaneCoeff r s =
              firstOrderLocalKernelDirections i ∧
            firstOrderPlaneCoeff r s + firstOrderPlaneCoeff z w =
              firstOrderLocalKernelDirections j) ∨
          (firstOrderPlaneCoeff x y + firstOrderPlaneCoeff r s =
              firstOrderLocalKernelDirections j ∧
            firstOrderPlaneCoeff r s + firstOrderPlaneCoeff z w =
              firstOrderLocalKernelDirections i)) := by
  rcases twoLocalKernelDifference_common_line x y z w i j hij hdiff with
    ⟨p, hp0, hpA, hpLocal⟩ | ⟨p, hp0, hpA, hpLocal⟩
  · rcases intermediatePlane_of_common_local_line
      x y p i hp0 hpA hpLocal with hi | ⟨r, s, hrs, hfirst⟩
    · exact Or.inl hi
    · refine Or.inr (Or.inr ⟨r, s, hrs, Or.inl ⟨hfirst, ?_⟩⟩)
      exact second_difference_of_total_and_first
        (firstOrderPlaneCoeff x y) (firstOrderPlaneCoeff z w)
        (firstOrderPlaneCoeff r s)
        (firstOrderLocalKernelDirections i)
        (firstOrderLocalKernelDirections j) hdiff hfirst
  · rcases intermediatePlane_of_common_local_line
      x y p j hp0 hpA hpLocal with hj | ⟨r, s, hrs, hfirst⟩
    · exact Or.inr (Or.inl hj)
    · refine Or.inr (Or.inr ⟨r, s, hrs, Or.inr ⟨hfirst, ?_⟩⟩)
      exact second_difference_of_total_and_first
        (firstOrderPlaneCoeff x y) (firstOrderPlaneCoeff z w)
        (firstOrderPlaneCoeff r s)
        (firstOrderLocalKernelDirections j)
        (firstOrderLocalKernelDirections i) (by simpa [add_comm] using hdiff)
        hfirst

end

end N5
end UnrestrictedBooleanMul
