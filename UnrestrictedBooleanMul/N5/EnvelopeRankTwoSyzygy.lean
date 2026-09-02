import UnrestrictedBooleanMul.N5.EnvelopeComplete

/-!
# Rank-two consequence of an independent cubic syzygy

An independent pair of linear syzygy directions admits an explicit dual
pair.  Contracting the cubic identity against those dual directions writes
all three nonzero directions of the quadratic plane as sums of two
decomposable forms.  This is the algebraic bridge to the Hankel rank-two
classification; no circuits or Boolean assignments are enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem ambientLinearPair_basis_right (x : LinearForm) (i : Fin 10) :
    ambientLinearPair x ((Pi.basisFun F₂ (Fin 10)) i) = x i := by
  classical
  rw [ambientLinearPair, Fintype.sum_eq_single i]
  · simp [Pi.basisFun]
  · intro j hji
    simp [Pi.basisFun, hji]

private theorem ambientLinearPair_smul_right
    (x u : LinearForm) (a : F₂) :
    ambientLinearPair x (a • u) = a * ambientLinearPair x u := by
  simp only [ambientLinearPair, Pi.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem exists_ambient_dual_pair (x y : LinearForm)
    (hxy : LinearIndependent F₂ ![x, y]) :
    ∃ u v : LinearForm,
      ambientLinearPair x u = 1 ∧ ambientLinearPair y u = 0 ∧
      ambientLinearPair x v = 0 ∧ ambientLinearPair y v = 1 := by
  have hwedge : ∃ i j : Fin 10, x i * y j + x j * y i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    rcases N4.dependent_of_vectorWedge_zero x y hnone with hx | hy | hxyEq
    · exact (hxy.ne_zero 0) (by simpa using hx)
    · exact (hxy.ne_zero 1) (by simpa using hy)
    · have heq : (![x, y] : Fin 2 → LinearForm) 0 = ![x, y] 1 := by
        simpa using hxyEq
      exact Fin.zero_ne_one (hxy.injective heq)
  rcases hwedge with ⟨i, j, hij⟩
  have hij1 : x i * y j + x j * y i = 1 :=
    (f2_eq_zero_or_one _).resolve_left hij
  let ei : LinearForm := (Pi.basisFun F₂ (Fin 10)) i
  let ej : LinearForm := (Pi.basisFun F₂ (Fin 10)) j
  let u : LinearForm := y j • ei + y i • ej
  let v : LinearForm := x j • ei + x i • ej
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · simp only [u, ambientLinearPair_add_right,
      ambientLinearPair_smul_right, ei, ej, ambientLinearPair_basis_right]
    simpa [mul_comm, add_comm] using hij1
  · simp only [u, ambientLinearPair_add_right,
      ambientLinearPair_smul_right, ei, ej, ambientLinearPair_basis_right]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  · simp only [v, ambientLinearPair_add_right,
      ambientLinearPair_smul_right, ei, ej, ambientLinearPair_basis_right]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  · simp only [v, ambientLinearPair_add_right,
      ambientLinearPair_smul_right, ei, ej, ambientLinearPair_basis_right]
    simpa [mul_comm, add_comm] using hij1

def ambientTwoFirstContraction (u : LinearForm) (q : TwoForm) : LinearForm :=
  fun j => ∑ i : Fin 10, u i * ambientTwoCoeff q i j

private theorem sum_mul_mul_right_local
    (u x : LinearForm) (a : F₂) :
    (∑ i : Fin 10, u i * (x i * a)) =
      (∑ i : Fin 10, u i * x i) * a := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sum_mul_mul_left_local
    (u x : LinearForm) (a : F₂) :
    (∑ i : Fin 10, u i * (a * x i)) =
      a * (∑ i : Fin 10, u i * x i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem ambientCubicFirstContraction_add
    (u : LinearForm) (h k : AmbientThreeForm) :
    ambientCubicFirstContraction u (h + k) =
      ambientCubicFirstContraction u h + ambientCubicFirstContraction u k := by
  funext i j
  simp only [ambientCubicFirstContraction, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

private theorem ambientCubicFirstContraction_vectorWedgeTwo
    (u x : LinearForm) (q : TwoForm) :
    ambientCubicFirstContraction u (ambientVectorWedgeTwo x q) =
      fun j k =>
        ambientLinearPair x u * ambientTwoCoeff q j k +
          x j * ambientTwoFirstContraction u q k +
          x k * ambientTwoFirstContraction u q j := by
  funext j k
  simp only [ambientCubicFirstContraction, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, ambientLinearPair, ambientTwoFirstContraction,
    mul_add]
  repeat' rw [Finset.sum_add_distrib]
  rw [sum_mul_mul_right_local, sum_mul_mul_left_local,
    sum_mul_mul_left_local]

theorem ambientPlaneCombination_eq_sum_two_wedges_of_cubic
    (x y u : LinearForm) (q c : TwoForm)
    (hcubic : factorPlaneCubic x y q c = 0) :
    ambientLinearPair x u • c + ambientLinearPair y u • q =
      squarefreeWedge x (ambientTwoFirstContraction u c) +
      squarefreeWedge y (ambientTwoFirstContraction u q) := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨j, k, hjk, rfl⟩
  have hcontract :
      ambientCubicFirstContraction u (factorPlaneCubic x y q c) j k = 0 := by
    rw [hcubic]
    simp [ambientCubicFirstContraction]
  rw [factorPlaneCubic, ambientCubicFirstContraction_add,
    ambientCubicFirstContraction_vectorWedgeTwo,
    ambientCubicFirstContraction_vectorWedgeTwo] at hcontract
  simp only [Pi.add_apply, ambientTwoCoeff, dif_neg hjk] at hcontract
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    squarefreeWedge_pair]
  linear_combination
    (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2])) hcontract

private theorem targetPlane_right_rankTwo_of_dual
    (d e : TargetCoeff) (x y : LinearForm)
    (u : LinearForm) (hxu : ambientLinearPair x u = 1)
    (hyu : ambientLinearPair y u = 0)
    (hcubic : factorPlaneCubic x y (targetTwo d) (targetTwo e) = 0) :
    HankelRankLETwo e := by
  have heSecant : targetTwo e =
      squarefreeWedge x (ambientTwoFirstContraction u (targetTwo e)) +
        squarefreeWedge y (ambientTwoFirstContraction u (targetTwo d)) := by
    have h := ambientPlaneCombination_eq_sum_two_wedges_of_cubic
      x y u (targetTwo d) (targetTwo e) hcubic
    simpa only [hxu, hyu, one_smul, zero_smul, add_zero] using h
  exact target_sum_two_decomposable_rankTwo heSecant

private theorem targetPlane_left_rankTwo_of_dual
    (d e : TargetCoeff) (x y : LinearForm)
    (v : LinearForm) (hxv : ambientLinearPair x v = 0)
    (hyv : ambientLinearPair y v = 1)
    (hcubic : factorPlaneCubic x y (targetTwo d) (targetTwo e) = 0) :
    HankelRankLETwo d := by
  have hdSecant : targetTwo d =
      squarefreeWedge x (ambientTwoFirstContraction v (targetTwo e)) +
        squarefreeWedge y (ambientTwoFirstContraction v (targetTwo d)) := by
    have h := ambientPlaneCombination_eq_sum_two_wedges_of_cubic
      x y v (targetTwo d) (targetTwo e) hcubic
    simpa only [hxv, hyv, one_smul, zero_smul, zero_add] using h
  exact target_sum_two_decomposable_rankTwo hdSecant

private theorem targetPlane_sum_rankTwo_of_dual
    (d e : TargetCoeff) (x y : LinearForm)
    (u v : LinearForm)
    (hxu : ambientLinearPair x u = 1)
    (hyu : ambientLinearPair y u = 0)
    (hxv : ambientLinearPair x v = 0)
    (hyv : ambientLinearPair y v = 1)
    (hcubic : factorPlaneCubic x y (targetTwo d) (targetTwo e) = 0) :
    HankelRankLETwo (d + e) := by
  have huvX : ambientLinearPair x (u + v) = 1 := by
    rw [ambientLinearPair_add_right, hxu, hxv, add_zero]
  have huvY : ambientLinearPair y (u + v) = 1 := by
    rw [ambientLinearPair_add_right, hyu, hyv, zero_add]
  have hsumSecant : targetTwo (d + e) =
      squarefreeWedge x
          (ambientTwoFirstContraction (u + v) (targetTwo e)) +
        squarefreeWedge y
          (ambientTwoFirstContraction (u + v) (targetTwo d)) := by
    have h := ambientPlaneCombination_eq_sum_two_wedges_of_cubic
      x y (u + v) (targetTwo d) (targetTwo e) hcubic
    simp only [huvX, huvY, one_smul] at h
    change targetTwoLinear (d + e) = _
    rw [map_add, add_comm]
    exact h
  exact target_sum_two_decomposable_rankTwo hsumSecant

/-- An independent cubic syzygy makes every direction in its quadratic
plane a secant of the ambient Grassmannian. -/
theorem targetPlane_rankTwo_of_independent_cubic_syzygy
    (d e : TargetCoeff) (x y : LinearForm)
    (hxy : LinearIndependent F₂ ![x, y])
    (hcubic : factorPlaneCubic x y (targetTwo d) (targetTwo e) = 0) :
    HankelRankLETwo d ∧ HankelRankLETwo e ∧ HankelRankLETwo (d + e) := by
  rcases exists_ambient_dual_pair x y hxy with
    ⟨u, v, hxu, hyu, hxv, hyv⟩
  exact ⟨targetPlane_left_rankTwo_of_dual d e x y v hxv hyv hcubic,
    targetPlane_right_rankTwo_of_dual d e x y u hxu hyu hcubic,
    targetPlane_sum_rankTwo_of_dual d e x y u v hxu hyu hxv hyv hcubic⟩

end
end N5
end UnrestrictedBooleanMul
