import UnrestrictedBooleanMul.N5.QuadraticReturnSymmetry

/-!
# Algebraic exterior kernels for quadratic returns

This file reduces target annihilators of an unpopulated quadratic return to
the genuinely exceptional rational rank-one case.  The key rank-four lemma
is intrinsic: if a two-form has a unit pivot and a nonzero decomposable pivot
residual, then every exterior annihilator has a decomposable translate along
the original two-form.

The proof is a four-vector calculation over `F₂`; it does not enumerate
quadratic forms, target words, or circuits.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem ambientVectorWedgeTwo_cycle
    (x u v : LinearForm) :
    ambientVectorWedgeTwo x (squarefreeWedge u v) =
      ambientVectorWedgeTwo u (squarefreeWedge v x) := by
  funext i j k
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff_squarefreeWedge]
  ring

/-- The Pfaffian-zero four-vector normal form is decomposable.  Splitting on
the first available cross pivot gives four algebraic branches, independent
of the ambient dimension. -/
private theorem balancedFourVector_decomposable
    (e f u v : LinearForm) (a b c d : F₂) :
    IsDecomposableTwo
      ((a * d + b * c) • squarefreeWedge e f +
        squarefreeWedge e (a • u + b • v) +
        squarefreeWedge f (c • u + d • v) +
        (a * d + b * c) • squarefreeWedge u v) := by
  rcases f2_eq_zero_or_one a with rfl | rfl
  · rcases f2_eq_zero_or_one b with rfl | rfl
    · rcases f2_eq_zero_or_one c with rfl | rfl
      · refine ⟨d • v, f, ?_⟩
        funext s
        rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
        simp only [squarefreeWedge_pair, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        ring
      · refine ⟨u + d • v, f, ?_⟩
        funext s
        rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
        simp only [squarefreeWedge_pair, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        ring
    · refine ⟨v + c • f, e + d • f + c • u, ?_⟩
      funext s
      rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
      simp only [squarefreeWedge_pair, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring_nf
      simp [N3Certificate.pow_two_f2, N3Certificate.two_eq_zero_f2]
      ring
  · let delta : F₂ := d + b * c
    refine ⟨delta • f + u + b • v,
      e + c • f + delta • v, ?_⟩
    funext s
    rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
    simp only [squarefreeWedge_pair, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, delta]
    ring_nf
    simp only [N3Certificate.pow_two_f2]
    ring_nf
    rw [N3Certificate.two_eq_zero_f2]
    ring

/-- Rank-four pivot kernel lemma.  The returned form `dform` is decomposable
and differs from the annihilator `q` by a scalar multiple of `p`. -/
theorem exists_decomposable_translate_of_pivotResidual
    (p q : TwoForm) (i j : Fin 10)
    (hpivot : ambientTwoCoeff p i j = 1)
    (u v : LinearForm)
    (hresidual : ambientPivotResidual p i j = squarefreeWedge u v)
    (hresidualNe : ambientPivotResidual p i j ≠ 0)
    (hwedge : ambientWedgeTwo p q = 0) :
    ∃ dform : TwoForm, IsDecomposableTwo dform ∧
      ∃ scalar : F₂, q + dform = scalar • p := by
  have huv : LinearIndependent F₂ ![u, v] := by
    rw [linearIndependent_fin2]
    refine ⟨?_, ?_⟩
    · intro hv
      apply hresidualNe
      have hvZero : v = 0 := by simpa using hv
      rw [hresidual, hvZero]
      simp
    · intro scalar hscalar
      apply hresidualNe
      have hscalar' : scalar • v = u := by simpa using hscalar
      rw [hresidual, ← hscalar', squarefreeWedge_smul_left,
        squarefreeWedge_self_f2, smul_zero]
  have hXzero := ambientPivotX_vectorWedge_residual_zero
    p q i j hpivot hwedge
  have hYzero := ambientPivotY_vectorWedge_residual_zero
    p q i j hpivot hwedge
  rw [hresidual] at hXzero hYzero
  have hXcycle : ambientVectorWedgeTwo u
      (squarefreeWedge v (ambientPivotX p q i j)) = 0 := by
    rw [← ambientVectorWedgeTwo_cycle]
    exact hXzero
  have hYcycle : ambientVectorWedgeTwo u
      (squarefreeWedge v (ambientPivotY p q i j)) = 0 := by
    rw [← ambientVectorWedgeTwo_cycle]
    exact hYzero
  rcases linearCombination_of_independent_tripleWedge_zero
      u v (ambientPivotX p q i j) huv hXcycle with ⟨a, b, hX⟩
  rcases linearCombination_of_independent_tripleWedge_zero
      u v (ambientPivotY p q i j) huv hYcycle with ⟨c, d, hY⟩
  let alpha := ambientPivotScalar q i j
  let delta := a * d + b * c
  let dform := q + (alpha + delta) • p
  have hp : p =
      squarefreeWedge (ambientPivotRow p i) (ambientPivotRow p j) +
        squarefreeWedge u v := by
    calc
      p = ambientPivotPlane p i j + ambientPivotResidual p i j :=
        (ambientPivotPlane_add_residual p i j).symm
      _ = _ := by rw [hresidual]; rfl
  have hdformCore : dform =
      delta • p +
        squarefreeWedge (ambientPivotRow p i) (a • u + b • v) +
        squarefreeWedge (ambientPivotRow p j) (c • u + d • v) := by
    dsimp only [dform]
    rw [ambientPivot_decomposition_of_wedge_zero
      p q i j hpivot hwedge, hX, hY]
    simp only [alpha, delta]
    funext s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  have hdeltaP : delta • p =
      delta • squarefreeWedge (ambientPivotRow p i)
          (ambientPivotRow p j) +
        delta • squarefreeWedge u v := by
    calc
      delta • p = delta •
          (squarefreeWedge (ambientPivotRow p i) (ambientPivotRow p j) +
            squarefreeWedge u v) := congrArg (fun form : TwoForm =>
              delta • form) hp
      _ = _ := smul_add delta _ _
  have hdform : dform =
      delta • squarefreeWedge (ambientPivotRow p i)
          (ambientPivotRow p j) +
        squarefreeWedge (ambientPivotRow p i) (a • u + b • v) +
        squarefreeWedge (ambientPivotRow p j) (c • u + d • v) +
        delta • squarefreeWedge u v := by
    rw [hdformCore, hdeltaP]
    module
  refine ⟨dform, ?_, alpha + delta, ?_⟩
  · rw [hdform]
    exact balancedFourVector_decomposable
      (ambientPivotRow p i) (ambientPivotRow p j) u v a b c d
  · dsimp only [dform]
    funext s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]

end
end N5
end UnrestrictedBooleanMul
