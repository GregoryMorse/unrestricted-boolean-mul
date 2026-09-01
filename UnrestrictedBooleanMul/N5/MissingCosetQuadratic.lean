import UnrestrictedBooleanMul.N5.MissingCoset

/-!
# The degree-two missing-coset kernel

This module begins the degree-two half of manuscript equation (11.2).  The
essential characteristic-two calculation is separated from the later change
of basis: exterior multiplication by the canonical rank-three alternating
form has precisely its own line as kernel on squarefree two-forms.

The proof uses three fixed exterior pivots.  It does not enumerate quadratic
forms or invoke a finite-state decision procedure.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

abbrev AmbientFourForm :=
  Fin 10 → Fin 10 → Fin 10 → Fin 10 → F₂

/-- Exterior multiplication of two squarefree ambient two-forms. -/
def ambientWedgeTwo (p q : TwoForm) : AmbientFourForm :=
  fun i j k l =>
    ambientTwoCoeff p i j * ambientTwoCoeff q k l +
    ambientTwoCoeff p i k * ambientTwoCoeff q j l +
    ambientTwoCoeff p i l * ambientTwoCoeff q j k +
    ambientTwoCoeff q i j * ambientTwoCoeff p k l +
    ambientTwoCoeff q i k * ambientTwoCoeff p j l +
    ambientTwoCoeff q i l * ambientTwoCoeff p j k

/-- Three disjoint hyperbolic pairs in the ambient ten-dimensional space. -/
def canonicalRankThreeTwo : TwoForm :=
  fun s => if s.1 = ({0, 1} : Finset (Fin 10)) ∨
      s.1 = ({2, 3} : Finset (Fin 10)) ∨
      s.1 = ({4, 5} : Finset (Fin 10)) then 1 else 0

abbrev IsCanonicalRankThreePair (i j : Fin 10) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
  (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
  (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4)

@[simp] theorem ambientTwoCoeff_canonicalRankThreeTwo (i j : Fin 10) :
    ambientTwoCoeff canonicalRankThreeTwo i j =
      if IsCanonicalRankThreePair i j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem ambientWedgeTwo_self (p : TwoForm) :
    ambientWedgeTwo p p = 0 := by
  funext i j k l
  simp only [ambientWedgeTwo, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem ambientWedgeTwo_smul_right (p q : TwoForm) (a : F₂) :
    ambientWedgeTwo p (a • q) = a • ambientWedgeTwo p q := by
  funext i j k l
  simp only [ambientWedgeTwo, Pi.smul_apply, smul_eq_mul]
  have coeff_smul (r s : Fin 10) :
      ambientTwoCoeff (a • q) r s = a * ambientTwoCoeff q r s := by
    by_cases hrs : r = s
    · simp [ambientTwoCoeff, hrs]
    · simp [ambientTwoCoeff, hrs]
  rw [coeff_smul, coeff_smul, coeff_smul,
    coeff_smul, coeff_smul, coeff_smul]
  ring

/-- Exterior multiplication by a fixed two-form, as a linear map. -/
def ambientWedgeTwoMap (p : TwoForm) :
    TwoForm →ₗ[F₂] AmbientFourForm where
  toFun q := ambientWedgeTwo p q
  map_add' q r := by
    funext i j k l
    simp only [ambientWedgeTwo, ambientTwoCoeff_add, Pi.add_apply]
    ring
  map_smul' a q := ambientWedgeTwo_smul_right p q a

theorem ambientTwoCoeff_smul (a : F₂) (q : TwoForm) (i j : Fin 10) :
    ambientTwoCoeff (a • q) i j = a * ambientTwoCoeff q i j := by
  by_cases hij : i = j
  · simp [ambientTwoCoeff, hij]
  · simp [ambientTwoCoeff, hij]

theorem ambientTwoCoeff_injective {p q : TwoForm}
    (h : ∀ i j, ambientTwoCoeff p i j = ambientTwoCoeff q i j) :
    p = q := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simpa [ambientTwoCoeff, hij] using h i j

theorem ambientTwoCoeff_comm (q : TwoForm) (i j : Fin 10) :
    ambientTwoCoeff q i j = ambientTwoCoeff q j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · rw [ambientTwoCoeff, dif_neg hij, ambientTwoCoeff,
      dif_neg (Ne.symm hij), quadraticPair_swap hij]

@[simp] private theorem f2_add_eq_zero_iff_eq (x y : F₂) :
    x + y = 0 ↔ x = y := by
  rw [← CharTwo.sub_eq_add, sub_eq_zero]

private theorem canonicalKernel_row0 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 0 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 0 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 0) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 0) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 0) j
  fin_cases j
  · simp
  · simp [IsCanonicalRankThreePair]
  all_goals simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row1 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 1 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 1 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 1) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 1) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 1) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row2 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 2 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 2 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 2) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 2) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 2) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row3 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 3 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 3 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 3) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 3) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 3) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row4 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 4 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 4 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 4) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 4) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 4) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row5 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 5 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 5 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 5) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 5) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 5) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row6 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 6 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 6 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 6) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 6) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 6) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row7 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 7 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 7 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 7) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 7) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 7) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row8 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 8 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 8 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 8) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 8) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 8) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

private theorem canonicalKernel_row9 (q : TwoForm)
    (h : ambientWedgeTwo canonicalRankThreeTwo q = 0) (j : Fin 10) :
    ambientTwoCoeff q 9 j =
      ambientTwoCoeff q 0 1 * ambientTwoCoeff canonicalRankThreeTwo 9 j := by
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 9) j
  have h23 := congrFun (congrFun (congrFun (congrFun h 2) 3) 9) j
  have h45 := congrFun (congrFun (congrFun (congrFun h 4) 5) 9) j
  fin_cases j <;> simp_all [ambientWedgeTwo, IsCanonicalRankThreePair,
    ambientTwoCoeff_comm]

/-- Canonical rank-three case of manuscript equation (11.2). -/
theorem canonicalRankThree_wedge_eq_zero_iff (q : TwoForm) :
    ambientWedgeTwo canonicalRankThreeTwo q = 0 ↔
      ∃ a : F₂, q = a • canonicalRankThreeTwo := by
  constructor
  · intro h
    let a := ambientTwoCoeff q 0 1
    refine ⟨a, ?_⟩
    apply ambientTwoCoeff_injective
    intro i j
    rw [ambientTwoCoeff_smul]
    fin_cases i
    · exact canonicalKernel_row0 q h j
    · exact canonicalKernel_row1 q h j
    · exact canonicalKernel_row2 q h j
    · exact canonicalKernel_row3 q h j
    · exact canonicalKernel_row4 q h j
    · exact canonicalKernel_row5 q h j
    · exact canonicalKernel_row6 q h j
    · exact canonicalKernel_row7 q h j
    · exact canonicalKernel_row8 q h j
    · exact canonicalKernel_row9 q h j
  · rintro ⟨a, rfl⟩
    rw [ambientWedgeTwo_smul_right, ambientWedgeTwo_self, smul_zero]

/-- Linear-map form of the canonical degree-two kernel calculation. -/
theorem canonicalRankThree_wedge_ker_eq_span :
    LinearMap.ker (ambientWedgeTwoMap canonicalRankThreeTwo) =
      Submodule.span F₂ ({canonicalRankThreeTwo} : Set TwoForm) := by
  ext q
  constructor
  · intro hq
    rw [LinearMap.mem_ker] at hq
    rcases (canonicalRankThree_wedge_eq_zero_iff q).1 hq with ⟨a, rfl⟩
    exact Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self canonicalRankThreeTwo)
  · intro hq
    rcases Submodule.mem_span_singleton.mp hq with ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    exact (canonicalRankThree_wedge_eq_zero_iff _).2 ⟨a, rfl⟩

/-- Degree-one companion to the canonical degree-two kernel. -/
theorem canonicalRankThree_vectorWedge_ker_eq_bot :
    LinearMap.ker (ambientVectorWedgeMap canonicalRankThreeTwo) = ⊥ := by
  apply le_antisymm
  · intro u hu
    rw [LinearMap.mem_ker] at hu
    change ambientVectorWedgeTwo u canonicalRankThreeTwo = 0 at hu
    have h01 (k : Fin 10) := congrFun (congrFun (congrFun hu 0) 1) k
    have h23 (k : Fin 10) := congrFun (congrFun (congrFun hu 2) 3) k
    have h45 (k : Fin 10) := congrFun (congrFun (congrFun hu 4) 5) k
    rw [Submodule.mem_bot]
    funext k
    have h01k := h01 k
    have h23k := h23 k
    have h45k := h45 k
    fin_cases k <;>
      simp_all [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
        IsCanonicalRankThreePair]
  · exact bot_le

/-- Canonical homogeneous contradiction used in the rank-one colour branch
of manuscript Theorem 12.3. -/
theorem canonicalRankOne_lower_parts_zero
    (C : TwoForm) (ell : LinearForm)
    (hfour : ambientWedgeTwo canonicalRankThreeTwo C = 0)
    (hnotTarget : C ≠ canonicalRankThreeTwo)
    (hthree : ambientVectorWedgeTwo ell canonicalRankThreeTwo = 0) :
    C = 0 ∧ ell = 0 := by
  constructor
  · rcases (canonicalRankThree_wedge_eq_zero_iff C).1 hfour with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with rfl | rfl
    · simp
    · exact (hnotTarget (by simp)).elim
  · have hell : ell ∈ LinearMap.ker
        (ambientVectorWedgeMap canonicalRankThreeTwo) :=
      (LinearMap.mem_ker).2 hthree
    rw [canonicalRankThree_vectorWedge_ker_eq_bot] at hell
    simpa using hell

/-! ## A basis-free hyperbolic pivot

The canonical calculation above is useful as a small certificate.  For the
actual missing coset, however, it is cleaner not to choose an entire
symplectic basis.  A single nonzero coefficient splits off one decomposable
hyperbolic plane.  The following definitions record that split. -/

/-- The coefficient row of an ambient squarefree two-form. -/
def ambientPivotRow (p : TwoForm) (i : Fin 10) : LinearForm :=
  fun k => ambientTwoCoeff p i k

/-- The decomposable plane split off by the pivot `(i,j)`. -/
def ambientPivotPlane (p : TwoForm) (i j : Fin 10) : TwoForm :=
  squarefreeWedge (ambientPivotRow p i) (ambientPivotRow p j)

/-- The residual two-form after splitting off the pivot plane. -/
def ambientPivotResidual (p : TwoForm) (i j : Fin 10) : TwoForm :=
  p + ambientPivotPlane p i j

@[simp] theorem ambientPivotRow_same (p : TwoForm) (i : Fin 10) :
    ambientPivotRow p i i = 0 := by
  simp [ambientPivotRow]

theorem ambientPivotRow_comm (p : TwoForm) (i j : Fin 10) :
    ambientPivotRow p i j = ambientPivotRow p j i := by
  exact ambientTwoCoeff_comm p i j

theorem ambientTwoCoeff_ambientPivotPlane
    (p : TwoForm) (i j k l : Fin 10) :
    ambientTwoCoeff (ambientPivotPlane p i j) k l =
      ambientPivotRow p i k * ambientPivotRow p j l +
        ambientPivotRow p i l * ambientPivotRow p j k := by
  simp [ambientPivotPlane, ambientPivotRow,
    ambientTwoCoeff_squarefreeWedge]

/-- A unit pivot makes its residual vanish in the two pivot rows. -/
theorem ambientTwoCoeff_ambientPivotResidual_left
    (p : TwoForm) (i j k : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1) :
    ambientTwoCoeff (ambientPivotResidual p i j) i k = 0 := by
  rw [ambientPivotResidual, ambientTwoCoeff_add,
    ambientTwoCoeff_ambientPivotPlane]
  simp only [ambientPivotRow]
  rw [ambientTwoCoeff_same, zero_mul, zero_add,
    ambientTwoCoeff_comm p j i, hpivot, mul_one]
  exact CharTwo.add_self_eq_zero (R := F₂) _

theorem ambientTwoCoeff_ambientPivotResidual_right
    (p : TwoForm) (i j k : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1) :
    ambientTwoCoeff (ambientPivotResidual p i j) j k = 0 := by
  rw [ambientPivotResidual, ambientTwoCoeff_add,
    ambientTwoCoeff_ambientPivotPlane]
  simp only [ambientPivotRow]
  rw [ambientTwoCoeff_same, mul_zero, add_zero, hpivot, one_mul]
  exact CharTwo.add_self_eq_zero (R := F₂) _

/-- The coefficient of the annihilator on the pivot plane. -/
def ambientPivotScalar (q : TwoForm) (i j : Fin 10) : F₂ :=
  ambientTwoCoeff q i j

/-- First off-pivot row of a two-form, in pivot coordinates. -/
def ambientPivotX (p q : TwoForm) (i j : Fin 10) : LinearForm :=
  ambientPivotRow q j +
    ambientPivotScalar q i j • ambientPivotRow p j

/-- Second off-pivot row of a two-form, in pivot coordinates. -/
def ambientPivotY (p q : TwoForm) (i j : Fin 10) : LinearForm :=
  ambientPivotRow q i +
    ambientPivotScalar q i j • ambientPivotRow p i

/-- Part of `q` supported completely away from the pivot plane. -/
def ambientPivotRemainder (p q : TwoForm) (i j : Fin 10) : TwoForm :=
  q + ambientPivotScalar q i j • ambientPivotPlane p i j +
    squarefreeWedge (ambientPivotRow p i) (ambientPivotX p q i j) +
    squarefreeWedge (ambientPivotRow p j) (ambientPivotY p q i j)

@[simp] theorem ambientPivotX_left
    (p q : TwoForm) (i j : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1) :
    ambientPivotX p q i j i = 0 := by
  simp only [ambientPivotX, ambientPivotRow, ambientPivotScalar,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ambientTwoCoeff_comm q j i, ambientTwoCoeff_comm p j i,
    hpivot, mul_one]
  exact CharTwo.add_self_eq_zero _

@[simp] theorem ambientPivotX_right
    (p q : TwoForm) (i j : Fin 10) :
    ambientPivotX p q i j j = 0 := by
  simp [ambientPivotX, ambientPivotRow]

@[simp] theorem ambientPivotY_left
    (p q : TwoForm) (i j : Fin 10) :
    ambientPivotY p q i j i = 0 := by
  simp [ambientPivotY, ambientPivotRow]

@[simp] theorem ambientPivotY_right
    (p q : TwoForm) (i j : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1) :
    ambientPivotY p q i j j = 0 := by
  simp only [ambientPivotY, ambientPivotRow, ambientPivotScalar,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpivot, mul_one]
  exact CharTwo.add_self_eq_zero _

theorem ambientTwoCoeff_ambientPivotRemainder_left
    (p q : TwoForm) (i j k : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1) :
    ambientTwoCoeff (ambientPivotRemainder p q i j) i k = 0 := by
  simp only [ambientPivotRemainder, ambientTwoCoeff_add,
    ambientTwoCoeff_smul, ambientTwoCoeff_ambientPivotPlane,
    ambientTwoCoeff_squarefreeWedge, ambientTwoCoeff_same,
    ambientPivotX, ambientPivotY,
    zero_mul, zero_add, mul_zero, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ambientPivotRow, ambientPivotScalar]
  rw [ambientTwoCoeff_comm p j i, ambientTwoCoeff_comm q j i,
    hpivot, one_mul, mul_one]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]

theorem ambientTwoCoeff_ambientPivotRemainder_right
    (p q : TwoForm) (i j k : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1) :
    ambientTwoCoeff (ambientPivotRemainder p q i j) j k = 0 := by
  simp only [ambientPivotRemainder, ambientTwoCoeff_add,
    ambientTwoCoeff_smul, ambientTwoCoeff_ambientPivotPlane,
    ambientTwoCoeff_squarefreeWedge, ambientTwoCoeff_same,
    ambientPivotX, ambientPivotY,
    zero_mul, zero_add, mul_zero, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ambientPivotRow, ambientPivotScalar]
  rw [hpivot, one_mul, mul_one]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2]

theorem ambientPivot_decomposition
    (p q : TwoForm) (i j : Fin 10) :
    q = ambientPivotScalar q i j • ambientPivotPlane p i j +
        squarefreeWedge (ambientPivotRow p i) (ambientPivotX p q i j) +
        squarefreeWedge (ambientPivotRow p j) (ambientPivotY p q i j) +
        ambientPivotRemainder p q i j := by
  funext s
  simp only [ambientPivotRemainder, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- The four-form equation determines the completely off-pivot part of an
annihilator. -/
theorem ambientPivotRemainder_eq_smul_residual_of_wedge_zero
    (p q : TwoForm) (i j : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1)
    (hwedge : ambientWedgeTwo p q = 0) :
    ambientPivotRemainder p q i j =
      ambientPivotScalar q i j • ambientPivotResidual p i j := by
  apply ambientTwoCoeff_injective
  intro k l
  have hijkl :=
    congrFun (congrFun (congrFun (congrFun hwedge i) j) k) l
  simp only [ambientWedgeTwo, Pi.zero_apply] at hijkl
  rw [hpivot, one_mul] at hijkl
  simp only [ambientPivotRemainder, ambientPivotResidual,
    ambientTwoCoeff_add, ambientTwoCoeff_smul,
    ambientTwoCoeff_ambientPivotPlane,
    ambientTwoCoeff_squarefreeWedge, ambientPivotX, ambientPivotY,
    ambientPivotRow, ambientPivotScalar, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring_nf at hijkl ⊢
  have hA : ambientTwoCoeff p i k * ambientTwoCoeff q i j *
      ambientTwoCoeff p j l * 2 = 0 := by
    rw [N3Certificate.two_eq_zero_f2, mul_zero]
  have hB : ambientTwoCoeff q i j * ambientTwoCoeff p i l *
      ambientTwoCoeff p j k * 2 = 0 := by
    rw [N3Certificate.two_eq_zero_f2, mul_zero]
  have hC : ambientTwoCoeff q i j * ambientTwoCoeff p k l * 2 = 0 := by
    rw [N3Certificate.two_eq_zero_f2, mul_zero]
  linear_combination hijkl + hA + hB - hC

/-- Pivot normal form of a quadratic annihilator. -/
theorem ambientPivot_decomposition_of_wedge_zero
    (p q : TwoForm) (i j : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1)
    (hwedge : ambientWedgeTwo p q = 0) :
    q = ambientPivotScalar q i j • p +
        squarefreeWedge (ambientPivotRow p i) (ambientPivotX p q i j) +
        squarefreeWedge (ambientPivotRow p j) (ambientPivotY p q i j) := by
  calc
    q = ambientPivotScalar q i j • ambientPivotPlane p i j +
          squarefreeWedge (ambientPivotRow p i) (ambientPivotX p q i j) +
          squarefreeWedge (ambientPivotRow p j) (ambientPivotY p q i j) +
          ambientPivotRemainder p q i j :=
      ambientPivot_decomposition p q i j
    _ = _ := by
      rw [ambientPivotRemainder_eq_smul_residual_of_wedge_zero
        p q i j hpivot hwedge]
      funext s
      simp only [ambientPivotResidual, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]

theorem ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
    (p q : TwoForm) (i j k l : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1)
    (hwedge : ambientWedgeTwo p q = 0) :
    ambientTwoCoeff q k l =
      ambientPivotScalar q i j * ambientTwoCoeff p k l +
      ambientPivotRow p i k * ambientPivotX p q i j l +
      ambientPivotRow p i l * ambientPivotX p q i j k +
      ambientPivotRow p j k * ambientPivotY p q i j l +
      ambientPivotRow p j l * ambientPivotY p q i j k := by
  have h := congrArg (fun r => ambientTwoCoeff r k l)
    (ambientPivot_decomposition_of_wedge_zero p q i j hpivot hwedge)
  simpa only [ambientTwoCoeff_add, ambientTwoCoeff_smul,
    ambientTwoCoeff_squarefreeWedge, smul_eq_mul, add_assoc] using h

/-- The first off-pivot row annihilates the pivot residual. -/
theorem ambientPivotX_vectorWedge_residual_zero
    (p q : TwoForm) (i j : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1)
    (hwedge : ambientWedgeTwo p q = 0) :
    ambientVectorWedgeTwo (ambientPivotX p q i j)
      (ambientPivotResidual p i j) = 0 := by
  funext k l m
  have h := congrFun (congrFun (congrFun (congrFun hwedge j) k) l) m
  simp only [ambientWedgeTwo, Pi.zero_apply] at h
  rw [ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j l m hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j k m hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j k l hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j j k hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j j l hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j j m hpivot hwedge] at h
  simp only [ambientPivotRow, hpivot, ambientTwoCoeff_same,
    ambientPivotX_right, ambientPivotY_right p q i j hpivot,
    one_mul, zero_mul, mul_zero, add_zero] at h
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientPivotResidual, ambientTwoCoeff_add,
    ambientTwoCoeff_ambientPivotPlane, ambientPivotRow, Pi.zero_apply]
  ring_nf at h ⊢
  simp only [N3Certificate.two_eq_zero_f2, mul_zero, add_zero] at h ⊢
  linear_combination h

/-- The second off-pivot row annihilates the pivot residual. -/
theorem ambientPivotY_vectorWedge_residual_zero
    (p q : TwoForm) (i j : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1)
    (hwedge : ambientWedgeTwo p q = 0) :
    ambientVectorWedgeTwo (ambientPivotY p q i j)
      (ambientPivotResidual p i j) = 0 := by
  funext k l m
  have h := congrFun (congrFun (congrFun (congrFun hwedge i) k) l) m
  simp only [ambientWedgeTwo, Pi.zero_apply] at h
  rw [ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j l m hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j k m hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j k l hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j i k hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j i l hpivot hwedge,
      ambientTwoCoeff_eq_pivot_normal_of_wedge_zero
        p q i j i m hpivot hwedge] at h
  simp only [ambientPivotRow, hpivot, ambientTwoCoeff_same,
    ambientTwoCoeff_comm p j i, ambientPivotX_left p q i j hpivot,
    ambientPivotY_left, one_mul, zero_mul, mul_zero,
    add_zero] at h
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientPivotResidual, ambientTwoCoeff_add,
    ambientTwoCoeff_ambientPivotPlane, ambientPivotRow, Pi.zero_apply]
  ring_nf at h ⊢
  simp only [N3Certificate.two_eq_zero_f2, mul_zero, add_zero] at h ⊢
  linear_combination h

theorem ambientPivotPlane_add_residual
    (p : TwoForm) (i j : Fin 10) :
    ambientPivotPlane p i j + ambientPivotResidual p i j = p := by
  funext s
  simp only [ambientPivotResidual, Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- A one-coefficient hyperbolic pivot proves the degree-two kernel theorem
without constructing a full symplectic basis. -/
theorem ambientWedgeTwo_eq_zero_iff_smul_of_not_sum_two_decomposable
    (p q : TwoForm) (i j : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1)
    (hnotSecant : ¬ ∃ x y z w : LinearForm,
      p = squarefreeWedge x y + squarefreeWedge z w) :
    ambientWedgeTwo p q = 0 ↔ ∃ a : F₂, q = a • p := by
  constructor
  · intro hwedge
    have hresidual : ¬ IsDecomposableTwo (ambientPivotResidual p i j) := by
      rintro ⟨x, y, hxy⟩
      apply hnotSecant
      refine ⟨ambientPivotRow p i, ambientPivotRow p j, x, y, ?_⟩
      rw [← hxy]
      simpa only [ambientPivotPlane] using
        (ambientPivotPlane_add_residual p i j).symm
    have hX : ambientPivotX p q i j = 0 := by
      by_contra hXne
      rcases eq_squarefreeWedge_of_ambientVectorWedgeTwo_eq_zero
          (ambientPivotResidual p i j) (ambientPivotX p q i j) hXne
          (ambientPivotX_vectorWedge_residual_zero
            p q i j hpivot hwedge) with ⟨v, hv⟩
      exact hresidual ⟨ambientPivotX p q i j, v, hv⟩
    have hY : ambientPivotY p q i j = 0 := by
      by_contra hYne
      rcases eq_squarefreeWedge_of_ambientVectorWedgeTwo_eq_zero
          (ambientPivotResidual p i j) (ambientPivotY p q i j) hYne
          (ambientPivotY_vectorWedge_residual_zero
            p q i j hpivot hwedge) with ⟨v, hv⟩
      exact hresidual ⟨ambientPivotY p q i j, v, hv⟩
    refine ⟨ambientPivotScalar q i j, ?_⟩
    have hnormal :=
      ambientPivot_decomposition_of_wedge_zero p q i j hpivot hwedge
    rw [hX, hY] at hnormal
    simpa [squarefreeWedge] using hnormal
  · rintro ⟨a, rfl⟩
    exact ambientWedgeTwo_smul_right p p a |>.trans (by simp)

@[simp] theorem ambientTwoCoeff_targetTwo_cross
    (c : TargetCoeff) (r s : Fin 5) :
    ambientTwoCoeff (targetTwo c) (aCoord r) (bCoord s) =
      c (hankelIndex r s) := by
  simp [ambientTwoCoeff, aCoord_ne_bCoord]

private theorem one_of_four_eq_one {a b c d : F₂}
    (h : a + b + c + d = 1) :
    a = 1 ∨ b = 1 ∨ c = 1 ∨ d = 1 := by
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨ha, hb, hc, hd⟩
  have ha0 : a = 0 := (f2_eq_zero_or_one a).resolve_right ha
  have hb0 : b = 0 := (f2_eq_zero_or_one b).resolve_right hb
  have hc0 : c = 0 := (f2_eq_zero_or_one c).resolve_right hc
  have hd0 : d = 0 := (f2_eq_zero_or_one d).resolve_right hd
  simp [ha0, hb0, hc0, hd0] at h

/-- Every member of the missing affine coset has a unit coefficient among
the four coordinates detected by the missing functional. -/
theorem missingCoset_has_unit_pivot
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    ∃ i j : Fin 10,
      ambientTwoCoeff (targetTwo (firstOrderMissingCoeff + u)) i j = 1 := by
  let c := firstOrderMissingCoeff + u
  have hu0 : firstOrderMissingFunctional u = 0 :=
    (mem_firstOrderEnvelopeCoeffSpace u).1 hu
  have hc1 : firstOrderMissingFunctional c = 1 := by
    dsimp [c]
    rw [map_add, firstOrderMissingFunctional_missing, hu0, add_zero]
  change c 2 + c 3 + c 5 + c 6 = 1 at hc1
  rcases one_of_four_eq_one hc1 with h2 | h3 | h5 | h6
  · refine ⟨aCoord 0, bCoord 2, ?_⟩
    simpa [c, hankelIndex] using h2
  · refine ⟨aCoord 0, bCoord 3, ?_⟩
    simpa [c, hankelIndex] using h3
  · refine ⟨aCoord 2, bCoord 3, ?_⟩
    simpa [c, hankelIndex] using h5
  · refine ⟨aCoord 2, bCoord 4, ?_⟩
    simpa [c, hankelIndex] using h6

/-- Manuscript equation (11.2), degree-two part, for every member of the
missing target coset. -/
theorem missingCoset_wedge_eq_zero_iff
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (q : TwoForm) :
    ambientWedgeTwo (targetTwo (firstOrderMissingCoeff + u)) q = 0 ↔
      ∃ a : F₂, q = a • targetTwo (firstOrderMissingCoeff + u) := by
  rcases missingCoset_has_unit_pivot u hu with ⟨i, j, hpivot⟩
  exact ambientWedgeTwo_eq_zero_iff_smul_of_not_sum_two_decomposable
    (targetTwo (firstOrderMissingCoeff + u)) q i j hpivot
      (missingCoset_not_sum_two_decomposable u hu)

/-- Linear-map form of the full degree-two missing-coset kernel. -/
theorem missingCoset_wedge_ker_eq_span
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    LinearMap.ker
        (ambientWedgeTwoMap (targetTwo (firstOrderMissingCoeff + u))) =
      Submodule.span F₂
        ({targetTwo (firstOrderMissingCoeff + u)} : Set TwoForm) := by
  ext q
  constructor
  · intro hq
    rw [LinearMap.mem_ker] at hq
    rcases (missingCoset_wedge_eq_zero_iff u hu q).1 hq with ⟨a, rfl⟩
    exact Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self
        (targetTwo (firstOrderMissingCoeff + u)))
  · intro hq
    rcases Submodule.mem_span_singleton.mp hq with ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    exact (missingCoset_wedge_eq_zero_iff u hu _).2 ⟨a, rfl⟩

/-- The simultaneous quartic and cubic equations kill both lower parts in
the non-target branch of manuscript Theorem 12.3. -/
theorem missingCoset_lower_parts_zero
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (C : TwoForm) (ell : LinearForm)
    (hfour : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + u)) C = 0)
    (hnotTarget : C ≠ targetTwo (firstOrderMissingCoeff + u))
    (hthree : ambientVectorWedgeTwo ell
      (targetTwo (firstOrderMissingCoeff + u)) = 0) :
    C = 0 ∧ ell = 0 := by
  constructor
  · rcases (missingCoset_wedge_eq_zero_iff u hu C).1 hfour with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with rfl | rfl
    · simp
    · exact (hnotTarget (by simp)).elim
  · exact (missingCoset_vectorWedge_eq_zero_iff u hu ell).1 hthree

end
end N5
end UnrestrictedBooleanMul
