import UnrestrictedBooleanMul.Phase3.SliceExclusion

/-!
# Semantic recovery of cubic ANF coefficients

Quadratic semantic recovery is already provided by `pairPolarMap`.  The
quartic slice proof also needs the three-variable polarization identity.
The only finite certificate here is the fixed subset identity on three
indices; it contains no circuit data.
-/

namespace UnrestrictedBooleanMul
namespace Phase3

noncomputable section

def triplePolarMap (i j k : Fin 8) : ANF 8 →ₗ[F₂] F₂ :=
  sparseEvalMap ∅ + sparseEvalMap {i} + sparseEvalMap {j} +
    sparseEvalMap {k} + sparseEvalMap {i, j} +
    sparseEvalMap {i, k} + sparseEvalMap {j, k} +
    sparseEvalMap {i, j, k}

def tripleCoeffMap (i j k : Fin 8) : ANF 8 →ₗ[F₂] F₂ where
  toFun p := p.coeff ⟨{i, j, k}⟩
  map_add' p q := by simp
  map_smul' a p := by simp

private theorem subset_iff_on_triple
    (s : Finset (Fin 8)) (i j k : Fin 8)
    (hs : s ⊆ {i, j, k}) (t : Finset (Fin 8)) :
    s ⊆ t ↔
      (i ∈ s → i ∈ t) ∧ (j ∈ s → j ∈ t) ∧ (k ∈ s → k ∈ t) := by
  constructor
  · intro h
    exact ⟨fun hi => h hi, fun hj => h hj, fun hk => h hk⟩
  · rintro ⟨hi, hj, hk⟩ x hx
    have hxTrip := hs hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxTrip
    rcases hxTrip with rfl | rfl | rfl
    · exact hi hx
    · exact hj hx
    · exact hk hx

private theorem eq_triple_iff_members
    (s : Finset (Fin 8)) (i j k : Fin 8)
    (hs : s ⊆ {i, j, k}) :
    s = {i, j, k} ↔ i ∈ s ∧ j ∈ s ∧ k ∈ s := by
  constructor
  · intro h
    subst s
    simp
  · rintro ⟨hi, hj, hk⟩
    apply Finset.Subset.antisymm hs
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

/-- Möbius polarization on a three-element Boolean cube. -/
theorem subset_triple_polar_identity
    (s : Finset (Fin 8)) (i j k : Fin 8)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (if s ⊆ ∅ then (1 : F₂) else 0) +
      (if s ⊆ {i} then 1 else 0) +
      (if s ⊆ {j} then 1 else 0) +
      (if s ⊆ {k} then 1 else 0) +
      (if s ⊆ {i, j} then 1 else 0) +
      (if s ⊆ {i, k} then 1 else 0) +
      (if s ⊆ {j, k} then 1 else 0) +
      (if s ⊆ {i, j, k} then 1 else 0) =
        if s = {i, j, k} then 1 else 0 := by
  by_cases hs : s ⊆ {i, j, k}
  · simp only [subset_iff_on_triple s i j k hs,
      eq_triple_iff_members s i j k hs]
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
      by_cases hk : k ∈ s <;>
        simp [hi, hj, hk, hij, hik, hjk, Ne.symm hij, Ne.symm hik,
          Ne.symm hjk, Phase2Certificate.two_eq_zero_f2,
          Phase2Certificate.four_eq_zero_f2,
          Phase2Certificate.eight_eq_zero_f2] <;>
        ring_nf <;>
        simp [Phase2Certificate.two_eq_zero_f2,
          Phase2Certificate.four_eq_zero_f2,
          Phase2Certificate.eight_eq_zero_f2]
  · have hEmpty : ¬s ⊆ ∅ := fun h => hs (h.trans (by simp))
    have hI : ¬s ⊆ {i} := fun h => hs (h.trans (by simp))
    have hJ : ¬s ⊆ {j} := fun h => hs (h.trans (by simp))
    have hK : ¬s ⊆ {k} := fun h => hs (h.trans (by simp))
    have hIJ : ¬s ⊆ {i, j} := fun h => hs (h.trans (by simp))
    have hIK : ¬s ⊆ {i, k} := fun h => hs (h.trans (by simp))
    have hJK : ¬s ⊆ {j, k} := fun h => hs (h.trans (by simp))
    have hne : s ≠ {i, j, k} := fun h => hs (by rw [h])
    simp [hEmpty, hI, hJ, hK, hIJ, hIK, hJK, hs, hne]

theorem triplePolarMap_eq_tripleCoeffMap
    (i j k : Fin 8) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    triplePolarMap i j k = tripleCoeffMap i j k := by
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext
  intro c
  change triplePolarMap i j k (MonoidAlgebra.single s c) =
    tripleCoeffMap i j k (MonoidAlgebra.single s c)
  simp only [triplePolarMap, LinearMap.add_apply]
  rw [sparseEvalMap_single, sparseEvalMap_single,
    sparseEvalMap_single, sparseEvalMap_single,
    sparseEvalMap_single, sparseEvalMap_single,
    sparseEvalMap_single, sparseEvalMap_single]
  change
    c * (if s.vars ⊆ ∅ then 1 else 0) +
      c * (if s.vars ⊆ {i} then 1 else 0) +
      c * (if s.vars ⊆ {j} then 1 else 0) +
      c * (if s.vars ⊆ {k} then 1 else 0) +
      c * (if s.vars ⊆ {i, j} then 1 else 0) +
      c * (if s.vars ⊆ {i, k} then 1 else 0) +
      c * (if s.vars ⊆ {j, k} then 1 else 0) +
      c * (if s.vars ⊆ {i, j, k} then 1 else 0) =
        (MonoidAlgebra.single s c : ANF 8).coeff ⟨{i, j, k}⟩
  rw [MonoidAlgebra.coeff_single_apply]
  change _ = if s = ⟨{i, j, k}⟩ then c else 0
  have hid := subset_triple_polar_identity s.vars i j k hij hik hjk
  have heq : s = ⟨{i, j, k}⟩ ↔ s.vars = {i, j, k} := by
    constructor
    · intro h
      simpa [h]
    · exact Monomial.ext
  calc
    _ = c *
        ((if s.vars ⊆ ∅ then 1 else 0) +
          (if s.vars ⊆ {i} then 1 else 0) +
          (if s.vars ⊆ {j} then 1 else 0) +
          (if s.vars ⊆ {k} then 1 else 0) +
          (if s.vars ⊆ {i, j} then 1 else 0) +
          (if s.vars ⊆ {i, k} then 1 else 0) +
          (if s.vars ⊆ {j, k} then 1 else 0) +
          (if s.vars ⊆ {i, j, k} then 1 else 0)) := by ring
    _ = c * (if s.vars = {i, j, k} then 1 else 0) := by rw [hid]
    _ = if s = ⟨{i, j, k}⟩ then c else 0 := by
      by_cases hs : s.vars = {i, j, k}
      · rw [if_pos hs, if_pos (heq.mpr hs), mul_one]
      · rw [if_neg hs, if_neg (fun h => hs (heq.mp h)), mul_zero]

/-- Equality of Boolean functions determines their homogeneous cubic
projection. -/
theorem anfThreeProjection_congr_of_eval_eq {p q : ANF 8}
    (h : ∀ x, eval p x = eval q x) :
    anfThreeProjection p = anfThreeProjection q := by
  funext i j k
  change
    (if ({i, j, k} : Finset (Fin 8)).card = 3 then
      p.coeff ⟨{i, j, k}⟩ else 0) =
    if ({i, j, k} : Finset (Fin 8)).card = 3 then
      q.coeff ⟨{i, j, k}⟩ else 0
  by_cases hcard : ({i, j, k} : Finset (Fin 8)).card = 3
  · have hij : i ≠ j := by
      intro heq
      subst j
      have hle : ({i, k} : Finset (Fin 8)).card ≤ 2 := Finset.card_le_two
      have hc : ({i, k} : Finset (Fin 8)).card = 3 := by simpa using hcard
      omega
    have hik : i ≠ k := by
      intro heq
      subst k
      have hle : ({j, i} : Finset (Fin 8)).card ≤ 2 := Finset.card_le_two
      have hc : ({j, i} : Finset (Fin 8)).card = 3 := by simpa using hcard
      omega
    have hjk : j ≠ k := by
      intro heq
      subst k
      have hle : ({i, j} : Finset (Fin 8)).card ≤ 2 := Finset.card_le_two
      have hc : ({i, j} : Finset (Fin 8)).card = 3 := by simpa using hcard
      omega
    simp only [anfThreeProjection, hcard, if_true]
    have hp := congrArg (fun L : ANF 8 →ₗ[F₂] F₂ => L p)
      (triplePolarMap_eq_tripleCoeffMap i j k hij hik hjk)
    have hq := congrArg (fun L : ANF 8 →ₗ[F₂] F₂ => L q)
      (triplePolarMap_eq_tripleCoeffMap i j k hij hik hjk)
    change triplePolarMap i j k p = p.coeff ⟨{i, j, k}⟩ at hp
    change triplePolarMap i j k q = q.coeff ⟨{i, j, k}⟩ at hq
    rw [← hp, ← hq]
    change
      eval p (supportAssignment ∅) + eval p (supportAssignment {i}) +
          eval p (supportAssignment {j}) + eval p (supportAssignment {k}) +
          eval p (supportAssignment {i, j}) +
          eval p (supportAssignment {i, k}) +
          eval p (supportAssignment {j, k}) +
          eval p (supportAssignment {i, j, k}) =
        eval q (supportAssignment ∅) + eval q (supportAssignment {i}) +
          eval q (supportAssignment {j}) + eval q (supportAssignment {k}) +
          eval q (supportAssignment {i, j}) +
          eval q (supportAssignment {i, k}) +
          eval q (supportAssignment {j, k}) +
          eval q (supportAssignment {i, j, k})
    rw [h, h, h, h, h, h, h, h]
  · simp [anfThreeProjection, hcard]

end

end Phase3
end UnrestrictedBooleanMul
