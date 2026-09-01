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

end
end N5
end UnrestrictedBooleanMul
