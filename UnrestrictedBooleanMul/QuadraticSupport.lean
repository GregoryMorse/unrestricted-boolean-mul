import UnrestrictedBooleanMul.Quadratic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Supports of squarefree two-forms

This file supplies the dimension-polymorphic contraction argument needed by
the five-term secant lemma.  For four independent vectors, the support of the
sum of the two decomposable forms is exactly their four-dimensional span.
-/

namespace UnrestrictedBooleanMul

noncomputable section

/-- Symmetric zero-diagonal matrix coefficient of a squarefree two-form in
characteristic two. -/
def alternatingCoeff {m : Nat} (p : QuadraticForm m) (i j : Fin m) : F₂ :=
  if h : i = j then 0 else p (quadraticPair i j h)

@[simp] theorem alternatingCoeff_squarefreeWedge {m : Nat}
    (u v : Fin m → F₂) (i j : Fin m) :
    alternatingCoeff (squarefreeWedge u v) i j =
      u i * v j + u j * v i := by
  by_cases hij : i = j
  · subst j
    simp [alternatingCoeff, CharTwo.add_self_eq_zero]
  · simp [alternatingCoeff, hij, squarefreeWedge_pair]

theorem alternatingCoeff_add {m : Nat} (p q : QuadraticForm m)
    (i j : Fin m) :
    alternatingCoeff (p + q) i j =
      alternatingCoeff p i j + alternatingCoeff q i j := by
  by_cases hij : i = j <;> simp [alternatingCoeff, hij]

/-- Coordinate dot product on the standard finite function space. -/
def coordinateDot {m : Nat} (u v : Fin m → F₂) : F₂ :=
  ∑ i : Fin m, u i * v i

/-- Contraction by a squarefree two-form.  Its range is the support of the
form. -/
def quadraticContraction {m : Nat} (p : QuadraticForm m) :
    (Fin m → F₂) →ₗ[F₂] (Fin m → F₂) where
  toFun z i := ∑ j : Fin m, alternatingCoeff p i j * z j
  map_add' z w := by
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ j : Fin m, alternatingCoeff p i j * (a * z j)) =
          ∑ j : Fin m, a * (alternatingCoeff p i j * z j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = a * ∑ j : Fin m, alternatingCoeff p i j * z j := by
        rw [Finset.mul_sum]

theorem quadraticContraction_add {m : Nat} (p q : QuadraticForm m) :
    quadraticContraction (p + q) =
      quadraticContraction p + quadraticContraction q := by
  ext z i
  simp [quadraticContraction, alternatingCoeff_add, add_mul,
    Finset.sum_add_distrib]

/-- Contraction of a decomposable two-form. -/
theorem quadraticContraction_squarefreeWedge {m : Nat}
    (u v z : Fin m → F₂) :
    quadraticContraction (squarefreeWedge u v) z =
      coordinateDot v z • u + coordinateDot u z • v := by
  ext i
  simp only [quadraticContraction, alternatingCoeff_squarefreeWedge,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ j : Fin m, (u i * v j + u j * v i) * z j) =
        ∑ j : Fin m,
          (u i * (v j * z j) + v i * (u j * z j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = u i * (∑ j : Fin m, v j * z j) +
        v i * (∑ j : Fin m, u j * z j) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
      simp only [coordinateDot]
      ring

/-- The support of a two-form is the range of its contraction map. -/
def quadraticSupport {m : Nat} (p : QuadraticForm m) :
    Submodule F₂ (Fin m → F₂) :=
  LinearMap.range (quadraticContraction p)

/-- Every linear functional on the standard coordinate space is represented
by dot product with a coordinate vector. -/
private def standardDualVector {m : Nat}
    (g : (Fin m → F₂) →ₗ[F₂] F₂) : Fin m → F₂ :=
  fun i => g ((Pi.basisFun F₂ (Fin m)) i)

private theorem coordinateDot_standardDualVector {m : Nat}
    (g : (Fin m → F₂) →ₗ[F₂] F₂) (u : Fin m → F₂) :
    coordinateDot u (standardDualVector g) = g u := by
  let b := Pi.basisFun F₂ (Fin m)
  have hsum : ∑ i : Fin m, u i • b i = u := by
    simpa [b, Pi.basisFun_repr] using b.sum_repr u
  calc
    coordinateDot u (standardDualVector g) =
        ∑ i : Fin m, u i • g (b i) := by
      simp [coordinateDot, standardDualVector, b, smul_eq_mul]
    _ = g (∑ i : Fin m, u i • b i) := by simp
    _ = g u := by rw [hsum]

/-- Independent vectors have coordinate-dot dual vectors. -/
private theorem exists_coordinateDot_dual {m : Nat} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (w : ι → Fin m → F₂)
    (hw : LinearIndependent F₂ w) (i : ι) :
    ∃ z : Fin m → F₂, ∀ j,
      coordinateDot (w j) z = if j = i then 1 else 0 := by
  let S : Submodule F₂ (Fin m → F₂) :=
    Submodule.span F₂ (Set.range w)
  let coord : S →ₗ[F₂] F₂ :=
    (Finsupp.lapply i).comp hw.repr
  obtain ⟨g, hg⟩ := LinearMap.exists_extend coord
  refine ⟨standardDualVector g, ?_⟩
  intro j
  rw [coordinateDot_standardDualVector]
  let x : S := ⟨w j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hgj : g (w j) = coord x := by
    have h := LinearMap.congr_fun hg x
    exact h
  rw [hgj]
  have hrepr : hw.repr x = Finsupp.single j 1 :=
    hw.repr_eq_single j x rfl
  change (hw.repr x) i = _
  rw [hrepr]
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-- The support of a two-wedge secant is contained in the span of its four
factors, without any independence assumption. -/
theorem quadraticSupport_two_wedges_le_span {m : Nat}
    (u v x y : Fin m → F₂) :
    quadraticSupport (squarefreeWedge u v + squarefreeWedge x y) ≤
      Submodule.span F₂ (Set.range ![u, v, x, y]) := by
  let w : Fin 4 → Fin m → F₂ := ![u, v, x, y]
  rintro _ ⟨z, rfl⟩
  rw [quadraticContraction_add, LinearMap.add_apply,
    quadraticContraction_squarefreeWedge,
    quadraticContraction_squarefreeWedge]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨1, rfl⟩)
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨2, rfl⟩)
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨3, rfl⟩)

/-- Rank-four support forces the four factors of a two-wedge secant to be
linearly independent. -/
theorem linearIndependent_of_two_wedge_support_finrank_four {m : Nat}
    (u v x y : Fin m → F₂)
    (hrank : Module.finrank F₂
      (quadraticSupport (squarefreeWedge u v + squarefreeWedge x y)) = 4) :
    LinearIndependent F₂ ![u, v, x, y] := by
  have hmono := Submodule.finrank_mono
    (quadraticSupport_two_wedges_le_span u v x y)
  have hlower : 4 ≤ Module.finrank F₂
      (Submodule.span F₂ (Set.range ![u, v, x, y])) := by
    exact hrank ▸ hmono
  have hupper : Module.finrank F₂
      (Submodule.span F₂ (Set.range ![u, v, x, y])) ≤ 4 := by
    change Set.finrank F₂ (Set.range ![u, v, x, y]) ≤ 4
    simpa using (finrank_range_le_card (R := F₂) ![u, v, x, y])
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change 4 = Module.finrank F₂
    (Submodule.span F₂ (Set.range ![u, v, x, y]))
  exact Nat.le_antisymm hlower hupper

/-- The support of the sum of two decomposable forms on four independent
vectors is exactly their span. -/
theorem quadraticSupport_two_wedges {m : Nat}
    (u v x y : Fin m → F₂)
    (hlin : LinearIndependent F₂ ![u, v, x, y]) :
    quadraticSupport (squarefreeWedge u v + squarefreeWedge x y) =
      Submodule.span F₂ (Set.range ![u, v, x, y]) := by
  let w : Fin 4 → Fin m → F₂ := ![u, v, x, y]
  have hw : LinearIndependent F₂ w := hlin
  apply le_antisymm
  · exact quadraticSupport_two_wedges_le_span u v x y
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · obtain ⟨z, hz⟩ := exists_coordinateDot_dual w hw (1 : Fin 4)
      refine ⟨z, ?_⟩
      rw [quadraticContraction_add, LinearMap.add_apply,
        quadraticContraction_squarefreeWedge,
        quadraticContraction_squarefreeWedge]
      have hzu : coordinateDot u z = 0 := by simpa [w] using hz 0
      have hzv : coordinateDot v z = 1 := by simpa [w] using hz 1
      have hzx : coordinateDot x z = 0 := by simpa [w] using hz 2
      have hzy : coordinateDot y z = 0 := by simpa [w] using hz 3
      rw [hzu, hzv, hzx, hzy]
      simp
    · obtain ⟨z, hz⟩ := exists_coordinateDot_dual w hw (0 : Fin 4)
      refine ⟨z, ?_⟩
      rw [quadraticContraction_add, LinearMap.add_apply,
        quadraticContraction_squarefreeWedge,
        quadraticContraction_squarefreeWedge]
      have hzu : coordinateDot u z = 1 := by simpa [w] using hz 0
      have hzv : coordinateDot v z = 0 := by simpa [w] using hz 1
      have hzx : coordinateDot x z = 0 := by simpa [w] using hz 2
      have hzy : coordinateDot y z = 0 := by simpa [w] using hz 3
      rw [hzu, hzv, hzx, hzy]
      simp
    · obtain ⟨z, hz⟩ := exists_coordinateDot_dual w hw (3 : Fin 4)
      refine ⟨z, ?_⟩
      rw [quadraticContraction_add, LinearMap.add_apply,
        quadraticContraction_squarefreeWedge,
        quadraticContraction_squarefreeWedge]
      have hzu : coordinateDot u z = 0 := by simpa [w] using hz 0
      have hzv : coordinateDot v z = 0 := by simpa [w] using hz 1
      have hzx : coordinateDot x z = 0 := by simpa [w] using hz 2
      have hzy : coordinateDot y z = 1 := by simpa [w] using hz 3
      rw [hzu, hzv, hzx, hzy]
      simp
    · obtain ⟨z, hz⟩ := exists_coordinateDot_dual w hw (2 : Fin 4)
      refine ⟨z, ?_⟩
      rw [quadraticContraction_add, LinearMap.add_apply,
        quadraticContraction_squarefreeWedge,
        quadraticContraction_squarefreeWedge]
      have hzu : coordinateDot u z = 0 := by simpa [w] using hz 0
      have hzv : coordinateDot v z = 0 := by simpa [w] using hz 1
      have hzx : coordinateDot x z = 1 := by simpa [w] using hz 2
      have hzy : coordinateDot y z = 0 := by simpa [w] using hz 3
      rw [hzu, hzv, hzx, hzy]
      simp

/-- The second exterior power of a subspace, represented inside squarefree
quadratic coordinates. -/
def quadraticExterior {m : Nat} (K : Submodule F₂ (Fin m → F₂)) :
    Submodule F₂ (QuadraticForm m) :=
  Submodule.span F₂ {p | ∃ u ∈ K, ∃ v ∈ K, p = squarefreeWedge u v}

theorem squarefreeWedge_mem_quadraticExterior {m : Nat}
    (K : Submodule F₂ (Fin m → F₂)) {u v : Fin m → F₂}
    (hu : u ∈ K) (hv : v ∈ K) :
    squarefreeWedge u v ∈ quadraticExterior K :=
  Submodule.subset_span ⟨u, hu, v, hv, rfl⟩

/-- Algebraic secant-support theorem: if the support of a rank-four secant is
contained in `K`, then each endpoint belongs to `Lambda^2 K`. -/
theorem secant_mem_quadraticExterior {m : Nat}
    (K : Submodule F₂ (Fin m → F₂)) (u v x y : Fin m → F₂)
    (hlin : LinearIndependent F₂ ![u, v, x, y])
    (hsupport :
      quadraticSupport (squarefreeWedge u v + squarefreeWedge x y) ≤ K) :
    squarefreeWedge u v ∈ quadraticExterior K ∧
      squarefreeWedge x y ∈ quadraticExterior K := by
  have hspan : Submodule.span F₂ (Set.range ![u, v, x, y]) ≤ K := by
    rw [← quadraticSupport_two_wedges u v x y hlin]
    exact hsupport
  have hu : u ∈ K := hspan (Submodule.subset_span ⟨0, by simp⟩)
  have hv : v ∈ K := hspan (Submodule.subset_span ⟨1, by simp⟩)
  have hx : x ∈ K := hspan (Submodule.subset_span ⟨2, by simp⟩)
  have hy : y ∈ K := hspan (Submodule.subset_span ⟨3, by simp⟩)
  exact ⟨squarefreeWedge_mem_quadraticExterior K hu hv,
    squarefreeWedge_mem_quadraticExterior K hx hy⟩

end

end UnrestrictedBooleanMul
