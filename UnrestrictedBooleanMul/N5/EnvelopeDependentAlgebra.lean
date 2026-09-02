import UnrestrictedBooleanMul.N5.EnvelopeRankTwoSyzygy

/-!
# Algebra for two dependent low-product planes

The key input is a symmetric Koszul normal form for an independent cubic
syzygy.  It is obtained from the same dual-pair contractions used by the
rank-two Hankel argument.  The resulting Boolean contractions combine into
two decomposable quadratic forms; no finite state enumeration is used.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem ambientVectorWedgeTwo_zero_left_local (q : TwoForm) :
    ambientVectorWedgeTwo 0 q = 0 := by
  funext i j k
  simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]

/-- If `x,y` are independent and `x ∧ y ∧ z = 0`, then `z` is in their
linear span.  A nonzero two-by-two coordinate minor supplies the two
coefficients directly. -/
theorem linearCombination_of_independent_tripleWedge_zero
    (x y z : LinearForm) (hxy : LinearIndependent F₂ ![x, y])
    (hzero : ambientVectorWedgeTwo x (squarefreeWedge y z) = 0) :
    ∃ a b : F₂, z = a • x + b • y := by
  have hpivot : ∃ i j : Fin 10, x i * y j + x j * y i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    rcases N4.dependent_of_vectorWedge_zero x y hnone with hx | hy | hxyEq
    · exact (hxy.ne_zero 0) (by simpa using hx)
    · exact (hxy.ne_zero 1) (by simpa using hy)
    · have heq : (![x, y] : Fin 2 → LinearForm) 0 = ![x, y] 1 := by
        simpa using hxyEq
      exact Fin.zero_ne_one (hxy.injective heq)
  rcases hpivot with ⟨i, j, hij⟩
  have hij1 : x i * y j + x j * y i = 1 :=
    (f2_eq_zero_or_one _).resolve_left hij
  let a : F₂ := y i * z j + y j * z i
  let b : F₂ := x i * z j + x j * z i
  refine ⟨a, b, ?_⟩
  funext k
  have hk := congrFun (congrFun (congrFun hzero i) j) k
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff_squarefreeWedge, Pi.zero_apply] at hk
  simp only [a, b, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination
    (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
    hk + (z k) * hij1

/-- Symmetric Koszul normal form for an independent cubic syzygy:
`x∧d + y∧e = 0` implies
`d=x∧A+y∧B` and `e=x∧B+y∧D`. -/
theorem independentCubicSyzygy_symmetricNormalForm
    (x y : LinearForm) (d e : TwoForm)
    (hxy : LinearIndependent F₂ ![x, y])
    (hcubic : factorPlaneCubic x y e d = 0) :
    ∃ A B D : LinearForm,
      d = squarefreeWedge x A + squarefreeWedge y B ∧
      e = squarefreeWedge x B + squarefreeWedge y D := by
  rcases exists_ambient_dual_pair x y hxy with
    ⟨u, v, hxu, hyu, hxv, hyv⟩
  let A := ambientTwoFirstContraction u d
  let B := ambientTwoFirstContraction u e
  let C := ambientTwoFirstContraction v d
  let D := ambientTwoFirstContraction v e
  have hd : d = squarefreeWedge x A + squarefreeWedge y B := by
    have h := ambientPlaneCombination_eq_sum_two_wedges_of_cubic
      x y u e d hcubic
    simpa only [hxu, hyu, one_smul, zero_smul, add_zero, A, B] using h
  have he : e = squarefreeWedge x C + squarefreeWedge y D := by
    have h := ambientPlaneCombination_eq_sum_two_wedges_of_cubic
      x y v e d hcubic
    simpa only [hxv, hyv, zero_smul, one_smul, zero_add, C, D] using h
  have htriple : ambientVectorWedgeTwo x
      (squarefreeWedge y (B + C)) = 0 := by
    funext i j k
    have h := congrFun (congrFun (congrFun hcubic i) j) k
    rw [factorPlaneCubic, hd, he] at h
    simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
      Pi.add_apply, Pi.zero_apply] at h ⊢
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2])) h
  rcases linearCombination_of_independent_tripleWedge_zero
      x y (B + C) hxy htriple with ⟨a, b, hBC⟩
  have hC : C = B + a • x + b • y := by
    funext i
    have hi := congrFun hBC i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2])) hi
  let D' := D + b • x
  refine ⟨A, B, D', hd, ?_⟩
  calc
    e = squarefreeWedge x C + squarefreeWedge y D := he
    _ = squarefreeWedge x (B + a • x + b • y) +
        squarefreeWedge y D := by rw [hC]
    _ = squarefreeWedge x B + squarefreeWedge y D' := by
      simp only [squarefreeWedge_add_right, squarefreeWedge_smul_right,
        squarefreeWedge_self_f2, smul_zero, add_zero,
        D', squarefreeWedge_comm_f2]
      module

/-- The two cross Boolean contractions in a symmetric Koszul presentation
are themselves a sum of two decomposable forms. -/
theorem ambientBooleanContraction_crossKoszul
    (x y B : LinearForm) :
    ambientBooleanContraction x (squarefreeWedge y B) +
        ambientBooleanContraction y (squarefreeWedge x B) =
      squarefreeWedge x (ambientDiagonalProduct B y) +
        squarefreeWedge y (ambientDiagonalProduct B x) := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [Pi.add_apply]
  rw [ambientBooleanContraction_pair x (squarefreeWedge y B) i j hij,
    ambientBooleanContraction_pair y (squarefreeWedge x B) i j hij]
  simp only [squarefreeWedge_pair, ambientDiagonalProduct]
  linear_combination
    (norm := ring_nf)
    (x i * y i * B j + x j * y j * B i) *
      N3Certificate.two_eq_zero_f2

/-- Boolean contraction of a symmetric Koszul pair has two decomposable
summands, with the same leading factors `x` and `y`. -/
theorem ambientBooleanContraction_symmetricKoszul
    (x y A B D : LinearForm) :
    ambientBooleanContraction x
          (squarefreeWedge x A + squarefreeWedge y B) +
        ambientBooleanContraction y
          (squarefreeWedge x B + squarefreeWedge y D) =
      squarefreeWedge x
          (A + ambientDiagonalProduct x A + ambientDiagonalProduct B y) +
        squarefreeWedge y
          (D + ambientDiagonalProduct y D + ambientDiagonalProduct B x) := by
  rw [ambientBooleanContraction_add_right,
    ambientBooleanContraction_add_right]
  calc
    (ambientBooleanContraction x (squarefreeWedge x A) +
          ambientBooleanContraction x (squarefreeWedge y B)) +
        (ambientBooleanContraction y (squarefreeWedge x B) +
          ambientBooleanContraction y (squarefreeWedge y D)) =
      (ambientBooleanContraction x (squarefreeWedge x A) +
          ambientBooleanContraction y (squarefreeWedge y D)) +
        (ambientBooleanContraction x (squarefreeWedge y B) +
          ambientBooleanContraction y (squarefreeWedge x B)) := by module
    _ = (squarefreeWedge x A +
          squarefreeWedge x (ambientDiagonalProduct x A) +
        (squarefreeWedge y D +
          squarefreeWedge y (ambientDiagonalProduct y D))) +
        (squarefreeWedge x (ambientDiagonalProduct B y) +
          squarefreeWedge y (ambientDiagonalProduct B x)) := by
      rw [ambientBooleanContraction_squarefreeWedge_left,
        ambientBooleanContraction_squarefreeWedge_left,
        ambientBooleanContraction_crossKoszul]
    _ = squarefreeWedge x
          (A + ambientDiagonalProduct x A + ambientDiagonalProduct B y) +
        squarefreeWedge y
          (D + ambientDiagonalProduct y D + ambientDiagonalProduct B x) := by
      rw [squarefreeWedge_add_right, squarefreeWedge_add_right,
        squarefreeWedge_add_right, squarefreeWedge_add_right]
      module

/-- With independent exterior factors, equal cubic parts of two zero-left
rank-one products force their total quadratic shadow to be an old-envelope
term plus two decomposable forms. -/
theorem zeroLeftIndependentCubic_shadow_decomposition
    (W : Submodule F₂ TwoForm)
    (a b a' b' : F₂) (x m y n : LinearForm) (d e : TwoForm)
    (hd : d ∈ W) (he : e ∈ W)
    (hxy : LinearIndependent F₂ ![x, y])
    (hcubic : factorPlaneCubic x m 0 d =
      factorPlaneCubic y n 0 e) :
    ∃ r ∈ W, ∃ p q z w : LinearForm,
      lowProductQuadraticShadow a b x m 0 d +
          lowProductQuadraticShadow a' b' y n 0 e =
        r + squarefreeWedge p q + squarefreeWedge z w := by
  have hplane : factorPlaneCubic x y e d = 0 := by
    rw [factorPlaneCubic_zero_left, factorPlaneCubic_zero_left] at hcubic
    funext i j k
    have h := congrFun (congrFun (congrFun hcubic i) j) k
    simp only [factorPlaneCubic, Pi.add_apply, Pi.zero_apply] at h ⊢
    linear_combination
      (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2])) h
  rcases independentCubicSyzygy_symmetricNormalForm x y d e hxy hplane with
    ⟨A, B, D, hdForm, heForm⟩
  let X := A + ambientDiagonalProduct x A + ambientDiagonalProduct B y
  let Y := D + ambientDiagonalProduct y D + ambientDiagonalProduct B x
  have hcontraction : ambientBooleanContraction x d +
      ambientBooleanContraction y e =
        squarefreeWedge x X + squarefreeWedge y Y := by
    rw [hdForm, heForm]
    exact ambientBooleanContraction_symmetricKoszul x y A B D
  refine ⟨a • d + a' • e, W.add_mem (W.smul_mem _ hd) (W.smul_mem _ he),
    x, m + X, y, n + Y, ?_⟩
  simp only [lowProductQuadraticShadow, smul_zero,
    ambientBooleanContraction_zero_right, ambientTwoHadamard_zero_left,
    add_zero]
  calc
    (a • d + squarefreeWedge x m + ambientBooleanContraction x d) +
        (a' • e + squarefreeWedge y n + ambientBooleanContraction y e) =
      (a • d + a' • e) +
        (squarefreeWedge x m + squarefreeWedge y n) +
        (ambientBooleanContraction x d +
          ambientBooleanContraction y e) := by ac_rfl
    _ = (a • d + a' • e) +
        (squarefreeWedge x m + squarefreeWedge y n) +
        (squarefreeWedge x X + squarefreeWedge y Y) := by
      rw [hcontraction]
    _ = (a • d + a' • e) + squarefreeWedge x (m + X) +
        squarefreeWedge y (n + Y) := by
      simp only [X, Y, squarefreeWedge_add_right]
      ac_rfl

private theorem linearPair_dependent_cases
    (x y : LinearForm) (hdep : ¬ LinearIndependent F₂ ![x, y]) :
    x = 0 ∨ y = 0 ∨ x = y := by
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr (Or.inl hy)
  by_cases hxy : x = y
  · exact Or.inr (Or.inr hxy)
  exfalso
  apply hdep
  rw [linearIndependent_fin2]
  change y ≠ 0 ∧ ∀ a : F₂, a • y ≠ x
  refine ⟨hy, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hx
  · simpa using Ne.symm hxy

/-- Equal cubic parts of arbitrary zero-left rank-one products have a total
quadratic shadow equal to an old-envelope term plus two decomposable forms. -/
theorem zeroLeftCubic_shadow_decomposition
    (W : Submodule F₂ TwoForm)
    (a b a' b' : F₂) (x m y n : LinearForm) (d e : TwoForm)
    (hd : d ∈ W) (he : e ∈ W)
    (hcubic : factorPlaneCubic x m 0 d =
      factorPlaneCubic y n 0 e) :
    ∃ r ∈ W, ∃ p q z w : LinearForm,
      lowProductQuadraticShadow a b x m 0 d +
          lowProductQuadraticShadow a' b' y n 0 e =
        r + squarefreeWedge p q + squarefreeWedge z w := by
  by_cases hxy : LinearIndependent F₂ ![x, y]
  · exact zeroLeftIndependentCubic_shadow_decomposition
      W a b a' b' x m y n d e hd he hxy hcubic
  rcases linearPair_dependent_cases x y hxy with hx0 | hy0 | hxyEq
  · subst x
    have hzeroHigh : factorPlaneCubic 0 0 0 e =
        factorPlaneCubic y n 0 e := by
      simpa only [factorPlaneCubic_zero_left,
        ambientVectorWedgeTwo_zero_left_local] using hcubic
    rcases rankOneShadow_zero_left_decomposition W
        0 0 a' b' 0 0 y n e he hzeroHigh with
      ⟨r, hr, p, q, z, w, hdecomp⟩
    refine ⟨a • d + r, W.add_mem (W.smul_mem _ hd) hr,
      p, q, z, w, ?_⟩
    have hfirst : lowProductQuadraticShadow a b 0 m 0 d = a • d := by
      simp [lowProductQuadraticShadow]
    have hdecomp' :
        lowProductQuadraticShadow a' b' y n 0 e =
          r + squarefreeWedge p q + squarefreeWedge z w := by
      simpa [lowProductQuadraticShadow] using hdecomp
    rw [hfirst, hdecomp']
    ac_rfl
  · subst y
    have hzeroHigh : factorPlaneCubic x m 0 d =
        factorPlaneCubic 0 0 0 d := by
      simpa only [factorPlaneCubic_zero_left,
        ambientVectorWedgeTwo_zero_left_local] using hcubic
    rcases rankOneShadow_zero_left_decomposition W
        a b 0 0 x m 0 0 d hd hzeroHigh with
      ⟨r, hr, p, q, z, w, hdecomp⟩
    refine ⟨a' • e + r, W.add_mem (W.smul_mem _ he) hr,
      p, q, z, w, ?_⟩
    have hsecond : lowProductQuadraticShadow a' b' 0 n 0 e = a' • e := by
      simp [lowProductQuadraticShadow]
    have hdecomp' :
        lowProductQuadraticShadow a b x m 0 d =
          r + squarefreeWedge p q + squarefreeWedge z w := by
      simpa [lowProductQuadraticShadow] using hdecomp
    rw [hsecond, hdecomp']
    ac_rfl
  · subst y
    let f := d + e
    have hf : f ∈ W := W.add_mem hd he
    have hzeroHigh : factorPlaneCubic x (m + n) 0 f =
        factorPlaneCubic 0 0 0 f := by
      have hcubic' : ambientVectorWedgeTwo x d =
          ambientVectorWedgeTwo x e := by
        simpa only [factorPlaneCubic_zero_left] using hcubic
      funext i j k
      rw [factorPlaneCubic_zero_left, factorPlaneCubic_zero_left]
      have h := congrFun (congrFun (congrFun hcubic' i) j) k
      simp only [f, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
        ambientTwoCoeff_add, Pi.zero_apply] at h ⊢
      linear_combination
        (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2])) h
    rcases rankOneShadow_zero_left_decomposition W
        0 0 0 0 x (m + n) 0 0 f hf hzeroHigh with
      ⟨r, hr, p, q, z, w, hdecomp⟩
    refine ⟨a • d + a' • e + r,
      W.add_mem (W.add_mem (W.smul_mem _ hd) (W.smul_mem _ he)) hr,
      p, q, z, w, ?_⟩
    have hcombine :
        lowProductQuadraticShadow a b x m 0 d +
            lowProductQuadraticShadow a' b' x n 0 e =
          (a • d + a' • e) +
            lowProductQuadraticShadow 0 0 x (m + n) 0 f := by
      simp only [lowProductQuadraticShadow, smul_zero,
        ambientBooleanContraction_zero_right,
        ambientTwoHadamard_zero_left, add_zero,
        squarefreeWedge_add_right, f,
        ambientBooleanContraction_add_right, zero_smul]
      ac_rfl
    have hdecomp' :
        lowProductQuadraticShadow 0 0 x (m + n) 0 f =
          r + squarefreeWedge p q + squarefreeWedge z w := by
      simpa [lowProductQuadraticShadow] using hdecomp
    rw [hcombine, hdecomp']
    ac_rfl

end
end N5
end UnrestrictedBooleanMul
