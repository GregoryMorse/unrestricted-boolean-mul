import UnrestrictedBooleanMul.ANF
import Mathlib.Data.Set.PowersetCard

/-!
# Squarefree quadratic coordinates

This module is the dimension-polymorphic quadratic layer shared by the
five-term development and any later multiplication target.  A coordinate is
indexed by a two-element subset of the input variables, so the ambient space
has the correct binomial dimension by construction.  No matrix diagonal or
symmetry equations are carried as side conditions.
-/

namespace UnrestrictedBooleanMul

noncomputable section

/-- The squarefree degree-two monomials in `m` variables. -/
abbrev QuadraticIndex (m : Nat) := Set.powersetCard (Fin m) 2

/-- The coefficient space of squarefree quadratic ANFs in `m` variables. -/
abbrev QuadraticForm (m : Nat) := QuadraticIndex m → F₂

/-- Restrict an ANF to its linear coefficients. -/
def linearProjection (m : Nat) : ANF m →ₗ[F₂] (Fin m → F₂) where
  toFun p i := p.coeff ⟨{i}⟩
  map_add' p q := by ext i; simp
  map_smul' a p := by ext i; simp

/-- Restrict an ANF to its squarefree degree-two coefficients. -/
def quadraticProjection (m : Nat) : ANF m →ₗ[F₂] QuadraticForm m where
  toFun p s := p.coeff ⟨s.1⟩
  map_add' p q := by ext s; simp
  map_smul' a p := by ext s; simp

/-- A named two-element coordinate. -/
def quadraticPair {m : Nat} (i j : Fin m) (hij : i ≠ j) : QuadraticIndex m :=
  ⟨{i, j}, by simp [hij]⟩

/-- The squarefree coordinates of the exterior product of two linear forms.
The sum is intrinsic to the underlying two-element set and therefore carries
no choice of ordering. -/
def squarefreeWedge {m : Nat} (u v : Fin m → F₂) : QuadraticForm m :=
  fun s => ∑ i ∈ s.1, u i * ∑ j ∈ s.1.erase i, v j

@[simp] theorem squarefreeWedge_pair {m : Nat} (u v : Fin m → F₂)
    (i j : Fin m) (hij : i ≠ j) :
    squarefreeWedge u v (quadraticPair i j hij) =
      u i * v j + u j * v i := by
  simp [squarefreeWedge, quadraticPair, hij, Ne.symm hij]

/-- Every quadratic coordinate is represented by a distinct pair. -/
theorem QuadraticIndex.exists_pair {m : Nat} (s : QuadraticIndex m) :
    ∃ i j : Fin m, ∃ hij : i ≠ j, s = quadraticPair i j hij := by
  rcases Finset.card_eq_two.mp s.2 with ⟨i, j, hij, hs⟩
  refine ⟨i, j, hij, ?_⟩
  exact Subtype.ext hs

/-- The coordinate space has the expected binomial dimension. -/
theorem quadraticForm_finrank (m : Nat) :
    Module.finrank F₂ (QuadraticForm m) = m.choose 2 := by
  rw [Module.finrank_pi]
  simpa using (Set.powersetCard.card (α := Fin m) (n := 2))

@[simp] theorem linearProjection_one (m : Nat) :
    linearProjection m (1 : ANF m) = 0 := by
  ext i
  change (1 : ANF m).coeff ⟨{i}⟩ = 0
  rw [anf_one_coeff]
  split
  · rename_i h
    have hc := congrArg (fun t : Monomial m => t.vars.card) h
    simp at hc
  · rfl

@[simp] theorem linearProjection_X {m : Nat} (i j : Fin m) :
    linearProjection m (X i) j = if j = i then 1 else 0 := by
  simp [linearProjection, X, coeff_monomial, eq_comm]

@[simp] theorem quadraticProjection_one (m : Nat) :
    quadraticProjection m (1 : ANF m) = 0 := by
  ext s
  change (1 : ANF m).coeff ⟨s.1⟩ = 0
  rw [anf_one_coeff]
  split
  · rename_i h
    have hc := congrArg (fun t : Monomial m => t.vars.card) h
    simp at hc
  · rfl

@[simp] theorem quadraticProjection_X {m : Nat} (i : Fin m) :
    quadraticProjection m (X i) = 0 := by
  ext s
  change (X i).coeff ⟨s.1⟩ = 0
  rw [X, coeff_monomial]
  split
  · rename_i h
    have hc := congrArg Finset.card h
    simp at hc
  · rfl

/-- Squarefree quadratic projection kills every affine ANF. -/
theorem quadraticProjection_kills_affine (m : Nat) :
    affine m ≤ LinearMap.ker (quadraticProjection m) := by
  intro p hp
  refine Submodule.span_induction (p := fun p _ => quadraticProjection m p = 0)
    ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with hq | hq
    · simp only [Set.mem_singleton_iff] at hq
      subst q
      exact quadraticProjection_one m
    · rcases hq with ⟨i, rfl⟩
      exact quadraticProjection_X i
  · exact map_zero (quadraticProjection m)
  · intro p q _ _ hp hq
    rw [map_add, hp, hq, add_zero]
  · intro a p _ hp
    rw [map_smul, hp, smul_zero]

theorem squarefreeWedge_add_left {m : Nat} (u v w : Fin m → F₂) :
    squarefreeWedge (u + v) w = squarefreeWedge u w + squarefreeWedge v w := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair, Pi.add_apply]
  ring

theorem squarefreeWedge_add_right {m : Nat} (u v w : Fin m → F₂) :
    squarefreeWedge u (v + w) = squarefreeWedge u v + squarefreeWedge u w := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair, Pi.add_apply]
  ring

theorem squarefreeWedge_smul_left {m : Nat} (a : F₂)
    (u v : Fin m → F₂) :
    squarefreeWedge (a • u) v = a • squarefreeWedge u v := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair, Pi.smul_apply, smul_eq_mul]
  ring

theorem squarefreeWedge_smul_right {m : Nat} (a : F₂)
    (u v : Fin m → F₂) :
    squarefreeWedge u (a • v) = a • squarefreeWedge u v := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair, Pi.smul_apply, smul_eq_mul]
  ring

theorem squarefreeWedge_sum_left {m : Nat} {I : Type*}
    (s : Finset I) (u : I → Fin m → F₂) (v : Fin m → F₂) :
    squarefreeWedge (∑ i ∈ s, u i) v =
      ∑ i ∈ s, squarefreeWedge (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      ext q
      rcases QuadraticIndex.exists_pair q with ⟨i, j, hij, rfl⟩
      simp
  | @insert i s hi ih => simp [hi, ih, squarefreeWedge_add_left]

theorem squarefreeWedge_sum_right {m : Nat} {I : Type*}
    (u : Fin m → F₂) (s : Finset I) (v : I → Fin m → F₂) :
    squarefreeWedge u (∑ i ∈ s, v i) =
      ∑ i ∈ s, squarefreeWedge u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      ext q
      rcases QuadraticIndex.exists_pair q with ⟨i, j, hij, rfl⟩
      simp
  | @insert i s hi ih => simp [hi, ih, squarefreeWedge_add_right]

@[simp] theorem squarefreeWedge_zero_left {m : Nat} (v : Fin m → F₂) :
    squarefreeWedge 0 v = 0 := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp

@[simp] theorem squarefreeWedge_zero_right {m : Nat} (u : Fin m → F₂) :
    squarefreeWedge u 0 = 0 := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp

/-- The quadratic part of a product of two variables is their exterior
product.  The repeated-variable case vanishes because Boolean squaring lowers
degree. -/
theorem quadraticProjection_X_mul_X {m : Nat} (i j : Fin m) :
    quadraticProjection m (X i * X j) =
      squarefreeWedge
        (fun k => if k = i then 1 else 0)
        (fun k => if k = j then 1 else 0) := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨k, l, hkl, rfl⟩
  by_cases hij : i = j
  · subst j
    rw [X_mul_self, quadraticProjection_X]
    by_cases hki : k = i <;> by_cases hli : l = i <;>
      simp_all [CharTwo.add_self_eq_zero]
  · change (X i * X j).coeff ⟨{k, l}⟩ = _
    have hpair : ({i, j} : Finset (Fin m)) = {k, l} ↔
        (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
      constructor
      · intro h
        have hi : i = k ∨ i = l := by
          have : i ∈ ({k, l} : Finset (Fin m)) := by
            rw [← h]
            simp
          simpa using this
        rcases hi with hik | hil
        · left
          refine ⟨hik, ?_⟩
          have hj : j = k ∨ j = l := by
            have : j ∈ ({k, l} : Finset (Fin m)) := by
              rw [← h]
              simp
            simpa using this
          exact hj.resolve_left (fun hjk => hij (hik.trans hjk.symm))
        · right
          refine ⟨hil, ?_⟩
          have hj : j = k ∨ j = l := by
            have : j ∈ ({k, l} : Finset (Fin m)) := by
              rw [← h]
              simp
            simpa using this
          exact hj.resolve_right (fun hjl => hij (hil.trans hjl.symm))
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rfl
        · exact Finset.pair_comm _ _
    rw [show X i * X j = monomial {i, j} by simp [X], coeff_monomial]
    simp only [squarefreeWedge_pair]
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      by_cases hli : l = i <;> by_cases hlj : l = j <;>
        simp_all [Finset.pair_comm, eq_comm]

/-- Coordinate-free form of `quadraticProjection_X_mul_X`. -/
theorem quadraticProjection_X_mul_X' {m : Nat} (i j : Fin m) :
    quadraticProjection m (X i * X j) =
      squarefreeWedge (linearProjection m (X i))
        (linearProjection m (X j)) := by
  have hi : linearProjection m (X i) = fun k => if k = i then 1 else 0 := by
    ext k
    exact linearProjection_X i k
  have hj : linearProjection m (X j) = fun k => if k = j then 1 else 0 := by
    ext k
    exact linearProjection_X j k
  rw [hi, hj]
  exact quadraticProjection_X_mul_X i j

/-- Products of affine ANFs project to decomposable squarefree quadratic
forms.  This is the dimension-polymorphic version of the bridge used in the
`n = 4` proof. -/
theorem quadraticProjection_mul_of_affine {m : Nat} {p q : ANF m}
    (hp : p ∈ affine m) (hq : q ∈ affine m) :
    ∃ u v : Fin m → F₂,
      quadraticProjection m (p * q) = squarefreeWedge u v := by
  refine ⟨linearProjection m p, linearProjection m q, ?_⟩
  refine Submodule.span_induction (p := fun p _ => ∀ q, q ∈ affine m →
      quadraticProjection m (p * q) =
        squarefreeWedge (linearProjection m p) (linearProjection m q))
    ?_ ?_ ?_ ?_ hp q hq
  · intro x hx q hq
    rcases hx with hx | hx
    · simp only [Set.mem_singleton_iff] at hx
      subst x
      rw [one_mul, quadraticProjection_kills_affine m hq,
        linearProjection_one]
      exact (squarefreeWedge_zero_left _).symm
    · rcases hx with ⟨i, rfl⟩
      refine Submodule.span_induction (p := fun q _ =>
          quadraticProjection m (X i * q) =
            squarefreeWedge (linearProjection m (X i)) (linearProjection m q))
        ?_ ?_ ?_ ?_ hq
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

end

end UnrestrictedBooleanMul
