import UnrestrictedBooleanMul.N5.QuadraticLift
import UnrestrictedBooleanMul.N5.LowProductShadow

/-!
# Exact coordinates for ten-variable quadratic ANFs

Every Boolean ANF of degree at most two has unique constant, linear, and
squarefree-quadratic coordinates.  This module gives the reconstruction map
and identifies the degree-two part of the product of two reconstructed ANFs
with `lowProductQuadraticShadow`.

The product calculation is algebraic.  In particular, it does not enumerate
Boolean assignments or quadratic states.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The linear ANF with coefficient vector `ell`. -/
def linearANFTen (ell : LinearForm) : ANF 10 :=
  ∑ i : Fin 10, ell i • X i

/-- Reconstruct a degree-at-most-two ANF from its three coordinate layers. -/
def quadraticCoordinateANF (a : F₂) (ell : LinearForm) (q : TwoForm) :
    ANF 10 :=
  a • (1 : ANF 10) + linearANFTen ell + quadraticANFOfForm q

def coordinateLinearTen (i : Fin 10) : LinearForm :=
  fun j => if j = i then 1 else 0

@[simp] theorem linearANFTen_zero : linearANFTen (0 : LinearForm) = 0 := by
  simp [linearANFTen]

theorem linearANFTen_add (ell m : LinearForm) :
    linearANFTen (ell + m) = linearANFTen ell + linearANFTen m := by
  simp only [linearANFTen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- The coordinate reconstruction is additive in all three layers. -/
theorem quadraticCoordinateANF_add
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    quadraticCoordinateANF a ell q + quadraticCoordinateANF b m c =
      quadraticCoordinateANF (a + b) (ell + m) (q + c) := by
  rw [quadraticCoordinateANF, quadraticCoordinateANF, quadraticCoordinateANF,
    add_smul, linearANFTen_add]
  change
    (a • (1 : ANF 10) + linearANFTen ell + quadraticANFOfFormLinear q) +
        (b • (1 : ANF 10) + linearANFTen m + quadraticANFOfFormLinear c) =
      (a • (1 : ANF 10) + b • 1) +
        (linearANFTen ell + linearANFTen m) +
          quadraticANFOfFormLinear (q + c)
  rw [map_add]
  module

theorem linearANFTen_smul (a : F₂) (ell : LinearForm) :
    linearANFTen (a • ell) = a • linearANFTen ell := by
  simp only [linearANFTen, Pi.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul]

@[simp] theorem linearANFTen_coordinate (i : Fin 10) :
    linearANFTen (coordinateLinearTen i) = X i := by
  fin_cases i <;>
    simp [linearANFTen, coordinateLinearTen]

@[simp] theorem linearProjection_linearANFTen (ell : LinearForm) :
    linearProjection 10 (linearANFTen ell) = ell := by
  classical
  ext i
  simp [linearANFTen, linearProjection_X]

@[simp] theorem quadraticProjection_linearANFTen (ell : LinearForm) :
    quadraticProjection 10 (linearANFTen ell) = 0 := by
  rw [linearANFTen]
  simp

@[simp] theorem linearProjection_quadraticANFOfForm (q : TwoForm) :
    linearProjection 10 (quadraticANFOfForm q) = 0 := by
  classical
  ext i
  change (quadraticANFOfForm q).coeff ⟨{i}⟩ = 0
  rw [quadraticANFOfForm, MonoidAlgebra.coeff_sum]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro s _hs
  change q s * (monomial s.1 : ANF 10).coeff ⟨{i}⟩ = 0
  rw [coeff_monomial]
  split
  · rename_i h
    have hc := congrArg Finset.card h
    simp at hc
  · simp

@[simp] theorem linearProjection_quadraticCoordinateANF
    (a : F₂) (ell : LinearForm) (q : TwoForm) :
    linearProjection 10 (quadraticCoordinateANF a ell q) = ell := by
  simp [quadraticCoordinateANF]

@[simp] theorem quadraticProjection_quadraticCoordinateANF
    (a : F₂) (ell : LinearForm) (q : TwoForm) :
    quadraticProjection 10 (quadraticCoordinateANF a ell q) = q := by
  simp [quadraticCoordinateANF]

theorem linearANFTen_mem_affine (ell : LinearForm) :
    linearANFTen ell ∈ affine 10 := by
  rw [linearANFTen]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (X_mem_affine i)

theorem quadraticCoordinateANF_mem_quadraticANFSpace
    (a : F₂) (ell : LinearForm) (q : TwoForm) :
    quadraticCoordinateANF a ell q ∈ N4.quadraticANFSpace 10 := by
  rw [quadraticCoordinateANF]
  exact (N4.quadraticANFSpace 10).add_mem
    ((N4.quadraticANFSpace 10).add_mem
      (N4.affine_le_quadraticANFSpace
        (Submodule.smul_mem _ _ (one_mem_affine 10)))
      (N4.affine_le_quadraticANFSpace (linearANFTen_mem_affine ell)))
    (pureQuadraticANFSpace_le_quadraticANFSpace ⟨q, rfl⟩)

theorem exists_linearCoordinates_of_mem_affine {p : ANF 10}
    (hp : p ∈ affine 10) :
    ∃ (a : F₂) (ell : LinearForm),
      p = a • (1 : ANF 10) + linearANFTen ell := by
  refine Submodule.span_induction
    (p := fun p _ => ∃ (a : F₂) (ell : LinearForm),
      p = a • (1 : ANF 10) + linearANFTen ell) ?_ ?_ ?_ ?_ hp
  · intro x hx
    rcases hx with hx | hx
    · have hxone : x = 1 := by
        simpa only [Set.mem_singleton_iff] using hx
      subst x
      exact ⟨1, 0, by simp⟩
    · rcases hx with ⟨i, rfl⟩
      exact ⟨0, coordinateLinearTen i, by simp⟩
  · exact ⟨0, 0, by simp⟩
  · rintro x y _ _ ⟨a, ell, rfl⟩ ⟨b, m, rfl⟩
    refine ⟨a + b, ell + m, ?_⟩
    rw [linearANFTen_add, add_smul]
    module
  · rintro a x _ ⟨b, ell, rfl⟩
    refine ⟨a * b, a • ell, ?_⟩
    rw [linearANFTen_smul]
    simp [smul_add, smul_smul]

/-- Exact existence of constant, linear, and quadratic coordinates. -/
theorem exists_quadraticCoordinates {p : ANF 10}
    (hp : p ∈ N4.quadraticANFSpace 10) :
    ∃ (a : F₂) (ell : LinearForm) (q : TwoForm),
      p = quadraticCoordinateANF a ell q := by
  rw [quadraticANFSpace_eq_affine_sup_pure] at hp
  rcases Submodule.mem_sup.mp hp with ⟨u, hu, v, hv, rfl⟩
  rcases exists_linearCoordinates_of_mem_affine hu with ⟨a, ell, rfl⟩
  rcases hv with ⟨q, rfl⟩
  exact ⟨a, ell, q, rfl⟩

private theorem quadraticProjection_X_mul_quadraticMonomial
    (i : Fin 10) (s : QuadraticIndex 10) :
    quadraticProjection 10 (X i * monomial s.1) =
      if i ∈ s.1 then (fun t => if s = t then 1 else 0) else 0 := by
  classical
  ext t
  rw [X, monomial_mul]
  change (monomial ({i} ∪ s.1) : ANF 10).coeff ⟨t.1⟩ = _
  rw [coeff_monomial]
  by_cases hi : i ∈ s.1
  · have hunion : {i} ∪ s.1 = s.1 := by simp [hi]
    rw [if_pos hi, hunion]
    by_cases hst : s = t
    · subst t
      simp
    · have hsets : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
      simp [hst, hsets]
  · rw [if_neg hi]
    have hcard : ({i} ∪ s.1).card = 3 := by
      rw [Finset.card_union_of_disjoint]
      · simp
      · simpa [Finset.disjoint_left] using hi
    have hne : {i} ∪ s.1 ≠ t.1 := by
      intro h
      have hc := congrArg Finset.card h
      rw [hcard, t.2] at hc
      omega
    rw [if_neg hne]
    rfl

private theorem quadraticProjection_quadraticMonomial_mul_quadraticMonomial
    (s t : QuadraticIndex 10) :
    quadraticProjection 10 (monomial s.1 * monomial t.1) =
      if s = t then (fun u => if s = u then 1 else 0) else 0 := by
  classical
  ext u
  rw [monomial_mul]
  change (monomial (s.1 ∪ t.1) : ANF 10).coeff ⟨u.1⟩ = _
  rw [coeff_monomial]
  by_cases hst : s = t
  · subst t
    by_cases hsu : s = u
    · subst u
      simp
    · have hsets : s.1 ≠ u.1 := fun h => hsu (Subtype.ext h)
      simp [hsu, hsets]
  · rw [if_neg hst]
    have hcard : 3 ≤ (s.1 ∪ t.1).card := by
      by_contra hnot
      have hle : (s.1 ∪ t.1).card ≤ 2 := by omega
      have hsEq : s.1 = s.1 ∪ t.1 :=
        Finset.eq_of_subset_of_card_le Finset.subset_union_left (by
          simpa [s.2] using hle)
      have htEq : t.1 = s.1 ∪ t.1 :=
        Finset.eq_of_subset_of_card_le Finset.subset_union_right (by
          simpa [t.2] using hle)
      exact hst (Subtype.ext (hsEq.trans htEq.symm))
    have hne : s.1 ∪ t.1 ≠ u.1 := by
      intro h
      have hc := congrArg Finset.card h
      rw [u.2] at hc
      omega
    rw [if_neg hne]
    rfl

theorem quadraticProjection_linearANFTen_mul_linearANFTen
    (ell m : LinearForm) :
    quadraticProjection 10 (linearANFTen ell * linearANFTen m) =
      squarefreeWedge ell m := by
  have hp : linearANFTen ell ∈ affine 10 := linearANFTen_mem_affine ell
  have hq : linearANFTen m ∈ affine 10 := linearANFTen_mem_affine m
  have hresult :
      quadraticProjection 10 (linearANFTen ell * linearANFTen m) =
        squarefreeWedge (linearProjection 10 (linearANFTen ell))
          (linearProjection 10 (linearANFTen m)) := by
    refine Submodule.span_induction
      (p := fun p _ => ∀ q, q ∈ affine 10 →
        quadraticProjection 10 (p * q) =
          squarefreeWedge (linearProjection 10 p) (linearProjection 10 q))
      ?_ ?_ ?_ ?_ hp (linearANFTen m) hq
    · intro x hx q hq
      rcases hx with hx | hx
      · simp only [Set.mem_singleton_iff] at hx
        subst x
        rw [one_mul, quadraticProjection_kills_affine 10 hq,
          linearProjection_one]
        exact (squarefreeWedge_zero_left _).symm
      · rcases hx with ⟨i, rfl⟩
        refine Submodule.span_induction
          (p := fun q _ => quadraticProjection 10 (X i * q) =
            squarefreeWedge (linearProjection 10 (X i))
              (linearProjection 10 q)) ?_ ?_ ?_ ?_ hq
        · intro y hy
          rcases hy with hy | hy
          · simp only [Set.mem_singleton_iff] at hy
            subst y
            rw [mul_one, quadraticProjection_X, linearProjection_one]
            exact (squarefreeWedge_zero_right _).symm
          · rcases hy with ⟨j, rfl⟩
            exact quadraticProjection_X_mul_X' i j
        · simp
        · intro y z _ _ hy hz
          rw [mul_add, map_add, map_add, squarefreeWedge_add_right, hy, hz]
        · intro a y _ hy
          rw [mul_smul_comm, map_smul, map_smul,
            squarefreeWedge_smul_right, hy]
    · simp
    · intro x y _ _ hx hy q hq
      rw [add_mul, map_add, map_add, squarefreeWedge_add_left,
        hx q hq, hy q hq]
    · intro a x _ hx q hq
      rw [smul_mul_assoc, map_smul, map_smul,
        squarefreeWedge_smul_left, hx q hq]
  simpa using hresult

theorem quadraticProjection_linearANFTen_mul_quadraticANFOfForm
    (ell : LinearForm) (c : TwoForm) :
    quadraticProjection 10 (linearANFTen ell * quadraticANFOfForm c) =
      ambientBooleanContraction ell c := by
  classical
  rw [linearANFTen, quadraticANFOfForm]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul,
    quadraticProjection_X_mul_quadraticMonomial]
  ext t
  simp [ambientBooleanContraction, Finset.mul_sum, Finset.sum_mul]
  ring_nf

theorem quadraticProjection_quadraticANFOfForm_mul_linearANFTen
    (q : TwoForm) (m : LinearForm) :
    quadraticProjection 10 (quadraticANFOfForm q * linearANFTen m) =
      ambientBooleanContraction m q := by
  rw [mul_comm]
  exact quadraticProjection_linearANFTen_mul_quadraticANFOfForm m q

theorem quadraticProjection_quadraticANFOfForm_mul_quadraticANFOfForm
    (q c : TwoForm) :
    quadraticProjection 10
        (quadraticANFOfForm q * quadraticANFOfForm c) =
      ambientTwoHadamard q c := by
  classical
  rw [quadraticANFOfForm, quadraticANFOfForm]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul,
    quadraticProjection_quadraticMonomial_mul_quadraticMonomial]
  ext u
  simp [ambientTwoHadamard]
  ring_nf

/-- The exact Boolean degree-two product formula used by the suffix proof. -/
theorem quadraticProjection_quadraticCoordinateANF_mul
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    quadraticProjection 10
        (quadraticCoordinateANF a ell q *
          quadraticCoordinateANF b m c) =
      lowProductQuadraticShadow a b ell m q c := by
  simp only [quadraticCoordinateANF, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, map_add, map_smul,
    quadraticProjection_one, quadraticProjection_linearANFTen,
    quadraticProjection_quadraticANFOfForm,
    quadraticProjection_linearANFTen_mul_linearANFTen,
    quadraticProjection_linearANFTen_mul_quadraticANFOfForm,
    quadraticProjection_quadraticANFOfForm_mul_linearANFTen,
    quadraticProjection_quadraticANFOfForm_mul_quadraticANFOfForm,
    smul_zero, zero_add]
  rw [lowProductQuadraticShadow]
  module

end
end N5
end UnrestrictedBooleanMul
