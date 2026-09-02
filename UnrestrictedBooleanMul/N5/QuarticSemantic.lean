import UnrestrictedBooleanMul.N5.CubicSemantic

/-!
# Quartic ANF coordinates for ten-variable low products

This module identifies the literal quartic coefficients of a product of two
pure quadratic ANFs with the ambient exterior product used by the N5 envelope
calculations.  The construction is coordinate-free after the single
four-monomial normalization lemma and does not enumerate quadratic forms.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def anfFourProjectionTen : ANF 10 →ₗ[F₂] AmbientFourForm where
  toFun p i j k l :=
    if ({i, j, k, l} : Finset (Fin 10)).card = 4 then
      p.coeff ⟨{i, j, k, l}⟩ else 0
  map_add' p q := by
    funext i j k l
    by_cases h : ({i, j, k, l} : Finset (Fin 10)).card = 4 <;> simp [h]
  map_smul' a p := by
    funext i j k l
    by_cases h : ({i, j, k, l} : Finset (Fin 10)).card = 4 <;> simp [h]

def monomialFourTen (s : Finset (Fin 10)) : AmbientFourForm :=
  fun i j k l =>
    if ({i, j, k, l} : Finset (Fin 10)).card = 4 then
      if s = {i, j, k, l} then 1 else 0
    else 0

theorem anfFourProjectionTen_monomial (s : Finset (Fin 10)) :
    anfFourProjectionTen (monomial s) = monomialFourTen s := by
  funext i j k l
  by_cases hcard : ({i, j, k, l} : Finset (Fin 10)).card = 4 <;>
    simp [anfFourProjectionTen, monomialFourTen, hcard, coeff_monomial]

private theorem fourSet_pairwise_of_card_eq_four
    (a b c d : Fin 10)
    (hcard : ({a, b, c, d} : Finset (Fin 10)).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hab : a ≠ b := by
    intro h
    have hsub : ({a, b, c, d} : Finset (Fin 10)) ⊆ {a, c, d} := by
      intro x hx
      simpa [h, or_comm, or_left_comm, or_assoc] using hx
    have hle := Finset.card_le_card hsub
    have hthree := Finset.card_le_three (a := a) (b := c) (c := d)
    omega
  have hac : a ≠ c := by
    intro h
    have hsub : ({a, b, c, d} : Finset (Fin 10)) ⊆ {a, b, d} := by
      intro x hx
      simpa [h, or_comm, or_left_comm, or_assoc] using hx
    have hle := Finset.card_le_card hsub
    have hthree := Finset.card_le_three (a := a) (b := b) (c := d)
    omega
  have had : a ≠ d := by
    intro h
    have hsub : ({a, b, c, d} : Finset (Fin 10)) ⊆ {a, b, c} := by
      intro x hx
      simpa [h, or_comm, or_left_comm, or_assoc] using hx
    have hle := Finset.card_le_card hsub
    have hthree := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  have hbc : b ≠ c := by
    intro h
    have hsub : ({a, b, c, d} : Finset (Fin 10)) ⊆ {a, b, d} := by
      intro x hx
      simpa [h, or_comm, or_left_comm, or_assoc] using hx
    have hle := Finset.card_le_card hsub
    have hthree := Finset.card_le_three (a := a) (b := b) (c := d)
    omega
  have hbd : b ≠ d := by
    intro h
    have hsub : ({a, b, c, d} : Finset (Fin 10)) ⊆ {a, b, c} := by
      intro x hx
      simpa [h, or_comm, or_left_comm, or_assoc] using hx
    have hle := Finset.card_le_card hsub
    have hthree := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  have hcd : c ≠ d := by
    intro h
    have hsub : ({a, b, c, d} : Finset (Fin 10)) ⊆ {a, b, c} := by
      intro x hx
      simpa [h, or_comm, or_left_comm, or_assoc] using hx
    have hle := Finset.card_le_card hsub
    have hthree := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  exact ⟨hab, hac, had, hbc, hbd, hcd⟩

@[simp] private theorem pair_eq_pair_iff_of_ne
    (a b i j : Fin 10) (hab : a ≠ b) (hij : i ≠ j) :
    ({a, b} : Finset (Fin 10)) = {i, j} ↔
      (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  constructor
  · intro h
    have ha : a = i ∨ a = j := by
      have ha' : a ∈ ({i, j} : Finset (Fin 10)) := by
        rw [← h]
        simp
      simpa [eq_comm] using ha'
    have hb : b = i ∨ b = j := by
      have hb' : b ∈ ({i, j} : Finset (Fin 10)) := by
        rw [← h]
        simp
      simpa [eq_comm] using hb'
    rcases ha with hai | haj <;> rcases hb with hbi | hbj
    · exact False.elim (hab (hai.trans hbi.symm))
    · exact Or.inl ⟨hai, hbj⟩
    · exact Or.inr ⟨haj, hbi⟩
    · exact False.elim (hab (haj.trans hbj.symm))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
private theorem ambientTwoCoeff_coordinateWedge_eq
    (a b i j : Fin 10) (hab : a ≠ b) (hij : i ≠ j) :
    ambientTwoCoeff
        (squarefreeWedge (coordinateLinearTen a) (coordinateLinearTen b)) i j =
      if ({a, b} : Finset (Fin 10)) = {i, j} then 1 else 0 := by
  simp only [pair_eq_pair_iff_of_ne a b i j hab hij]
  simp only [ambientTwoCoeff_squarefreeWedge, coordinateLinearTen]
  split_ifs <;> simp_all [eq_comm, N3Certificate.two_eq_zero_f2]

private theorem pair_eq_one_of_six
    (a b i j k l : Fin 10) (hab : a ≠ b)
    (ha : a ∈ ({i, j, k, l} : Finset (Fin 10)))
    (hb : b ∈ ({i, j, k, l} : Finset (Fin 10))) :
    ({a, b} : Finset (Fin 10)) = {i, j} ∨
      ({a, b} : Finset (Fin 10)) = {i, k} ∨
      ({a, b} : Finset (Fin 10)) = {i, l} ∨
      ({a, b} : Finset (Fin 10)) = {j, k} ∨
      ({a, b} : Finset (Fin 10)) = {j, l} ∨
      ({a, b} : Finset (Fin 10)) = {k, l} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl
  all_goals simp_all [Finset.pair_comm]

private theorem fourSet_eq_pair_union (a b c d : Fin 10) :
    ({a, b, c, d} : Finset (Fin 10)) = {a, b} ∪ {c, d} := by
  ext x
  simp [or_left_comm]

private theorem fourSet_eq_of_pair_equalities
    (a b c d i j k l : Fin 10)
    (hab : ({a, b} : Finset (Fin 10)) = {i, j})
    (hcd : ({c, d} : Finset (Fin 10)) = {k, l}) :
    ({a, b, c, d} : Finset (Fin 10)) = {i, j, k, l} := by
  calc
    ({a, b, c, d} : Finset (Fin 10)) = {a, b} ∪ {c, d} :=
      fourSet_eq_pair_union a b c d
    _ = {i, j} ∪ {k, l} := by rw [hab, hcd]
    _ = {i, j, k, l} := (fourSet_eq_pair_union i j k l).symm

private theorem complementPair_eq_of_fourSet_eq
    (a b c d i j k l : Fin 10)
    (hset : ({a, b, c, d} : Finset (Fin 10)) = {i, j, k, l})
    (hab : ({a, b} : Finset (Fin 10)) = {i, j})
    (hin : Disjoint ({a, b} : Finset (Fin 10)) {c, d})
    (hout : Disjoint ({i, j} : Finset (Fin 10)) {k, l}) :
    ({c, d} : Finset (Fin 10)) = {k, l} := by
  have hu : ({a, b} : Finset (Fin 10)) ∪ {c, d} =
      {i, j} ∪ {k, l} := by
    rw [← fourSet_eq_pair_union a b c d,
      ← fourSet_eq_pair_union i j k l]
    exact hset
  rw [hab] at hu hin
  have hs := congrArg (fun s : Finset (Fin 10) => s \ {i, j}) hu
  rw [Finset.union_sdiff_cancel_left hin,
    Finset.union_sdiff_cancel_left hout] at hs
  exact hs

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
private theorem anfFourProjectionTen_four_X (a b c d : Fin 10) :
    anfFourProjectionTen ((X a * X b) * (X c * X d)) =
      ambientWedgeTwo
        (squarefreeWedge (coordinateLinearTen a) (coordinateLinearTen b))
        (squarefreeWedge (coordinateLinearTen c) (coordinateLinearTen d)) := by
  rw [show (X a * X b) * (X c * X d) = monomial {a, b, c, d} by
    rw [X, X, X, X, monomial_mul, monomial_mul, monomial_mul]
    congr 1
    ext x
    simp [or_comm, or_left_comm, or_assoc]]
  rw [anfFourProjectionTen_monomial]
  funext i j k l
  simp only [monomialFourTen, ambientWedgeTwo]
  by_cases hcard : ({i, j, k, l} : Finset (Fin 10)).card = 4
  · rw [if_pos hcard]
    rcases fourSet_pairwise_of_card_eq_four i j k l hcard with
      ⟨hij, hik, hil, hjk, hjl, hkl⟩
    by_cases hinput : ({a, b, c, d} : Finset (Fin 10)).card = 4
    · rcases fourSet_pairwise_of_card_eq_four a b c d hinput with
        ⟨hab, hac, had, hbc, hbd, hcd⟩
      rw [ambientTwoCoeff_coordinateWedge_eq a b i j hab hij,
        ambientTwoCoeff_coordinateWedge_eq a b i k hab hik,
        ambientTwoCoeff_coordinateWedge_eq a b i l hab hil,
        ambientTwoCoeff_coordinateWedge_eq a b j k hab hjk,
        ambientTwoCoeff_coordinateWedge_eq a b j l hab hjl,
        ambientTwoCoeff_coordinateWedge_eq a b k l hab hkl,
        ambientTwoCoeff_coordinateWedge_eq c d i j hcd hij,
        ambientTwoCoeff_coordinateWedge_eq c d i k hcd hik,
        ambientTwoCoeff_coordinateWedge_eq c d i l hcd hil,
        ambientTwoCoeff_coordinateWedge_eq c d j k hcd hjk,
        ambientTwoCoeff_coordinateWedge_eq c d j l hcd hjl,
        ambientTwoCoeff_coordinateWedge_eq c d k l hcd hkl]
      let z1 : F₂ :=
        (if ({a, b} : Finset (Fin 10)) = {i, j} then 1 else 0) *
          (if ({c, d} : Finset (Fin 10)) = {k, l} then 1 else 0)
      let z2 : F₂ :=
        (if ({a, b} : Finset (Fin 10)) = {i, k} then 1 else 0) *
          (if ({c, d} : Finset (Fin 10)) = {j, l} then 1 else 0)
      let z3 : F₂ :=
        (if ({a, b} : Finset (Fin 10)) = {i, l} then 1 else 0) *
          (if ({c, d} : Finset (Fin 10)) = {j, k} then 1 else 0)
      let z4 : F₂ :=
        (if ({c, d} : Finset (Fin 10)) = {i, j} then 1 else 0) *
          (if ({a, b} : Finset (Fin 10)) = {k, l} then 1 else 0)
      let z5 : F₂ :=
        (if ({c, d} : Finset (Fin 10)) = {i, k} then 1 else 0) *
          (if ({a, b} : Finset (Fin 10)) = {j, l} then 1 else 0)
      let z6 : F₂ :=
        (if ({c, d} : Finset (Fin 10)) = {i, l} then 1 else 0) *
          (if ({a, b} : Finset (Fin 10)) = {j, k} then 1 else 0)
      change (if ({a, b, c, d} : Finset (Fin 10)) = {i, j, k, l}
        then 1 else 0) = (((((z1 + z2) + z3) + z4) + z5) + z6)
      by_cases hset : ({a, b, c, d} : Finset (Fin 10)) = {i, j, k, l}
      · rw [if_pos hset]
        have ha : a ∈ ({i, j, k, l} : Finset (Fin 10)) := by
          rw [← hset]
          simp
        have hb : b ∈ ({i, j, k, l} : Finset (Fin 10)) := by
          rw [← hset]
          simp
        have hpairs := pair_eq_one_of_six a b i j k l hab ha hb
        have hin : Disjoint ({a, b} : Finset (Fin 10)) {c, d} := by
          simp [Finset.disjoint_left, hac, had, hbc, hbd,
            Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
        rcases hpairs with hp | hp | hp | hp | hp | hp
        · have hc' := complementPair_eq_of_fourSet_eq
            a b c d i j k l hset hp hin (by
              simp [Finset.disjoint_left, hik, hil, hjk, hjl,
                Ne.symm hik, Ne.symm hil, Ne.symm hjk, Ne.symm hjl])
          simp [z1, z2, z3, z4, z5, z6, hp, hc', hij, hik, hil, hjk, hjl, hkl,
            Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
            Ne.symm hjl, Ne.symm hkl]
        · have hc' := complementPair_eq_of_fourSet_eq
            a b c d i k j l (hset.trans (by
              ext x
              simp [or_comm, or_left_comm, or_assoc])) hp hin (by
              simp [Finset.disjoint_left, hij, hil, hjk, hkl,
                Ne.symm hij, Ne.symm hil, Ne.symm hjk, Ne.symm hkl])
          simp [z1, z2, z3, z4, z5, z6, hp, hc', hij, hik, hil, hjk, hjl, hkl,
            Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
            Ne.symm hjl, Ne.symm hkl]
        · have hc' := complementPair_eq_of_fourSet_eq
            a b c d i l j k (hset.trans (by
              ext x
              simp [or_comm, or_left_comm, or_assoc])) hp hin (by
              simp [Finset.disjoint_left, hij, hik, hjl, hkl,
                Ne.symm hij, Ne.symm hik, Ne.symm hjl, Ne.symm hkl])
          simp [z1, z2, z3, z4, z5, z6, hp, hc', hij, hik, hil, hjk, hjl, hkl,
            Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
            Ne.symm hjl, Ne.symm hkl]
        · have hc' := complementPair_eq_of_fourSet_eq
            a b c d j k i l (hset.trans (by
              ext x
              simp [or_comm, or_left_comm, or_assoc])) hp hin (by
              simp [Finset.disjoint_left, hij, hjl, hik, hkl,
                Ne.symm hij, Ne.symm hjl, Ne.symm hik, Ne.symm hkl])
          simp [z1, z2, z3, z4, z5, z6, hp, hc', hij, hik, hil, hjk, hjl, hkl,
            Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
            Ne.symm hjl, Ne.symm hkl]
        · have hc' := complementPair_eq_of_fourSet_eq
            a b c d j l i k (hset.trans (by
              ext x
              simp [or_comm, or_left_comm, or_assoc])) hp hin (by
              simp [Finset.disjoint_left, hij, hjk, hil, hkl,
                Ne.symm hij, Ne.symm hjk, Ne.symm hil, Ne.symm hkl])
          simp [z1, z2, z3, z4, z5, z6, hp, hc', hij, hik, hil, hjk, hjl, hkl,
            Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
            Ne.symm hjl, Ne.symm hkl]
        · have hc' := complementPair_eq_of_fourSet_eq
            a b c d k l i j (hset.trans (by
              ext x
              simp [or_comm, or_left_comm, or_assoc])) hp hin (by
              simp [Finset.disjoint_left, hik, hjk, hil, hjl,
                Ne.symm hik, Ne.symm hjk, Ne.symm hil, Ne.symm hjl])
          simp [z1, z2, z3, z4, z5, z6, hp, hc', hij, hik, hil, hjk, hjl, hkl,
            Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
            Ne.symm hjl, Ne.symm hkl]
      · rw [if_neg hset]
        have hz1 : z1 = 0 := by
          dsimp only [z1]
          by_cases hp : ({a, b} : Finset (Fin 10)) = {i, j}
          · by_cases hc' : ({c, d} : Finset (Fin 10)) = {k, l}
            · exact False.elim (hset
                (fourSet_eq_of_pair_equalities a b c d i j k l hp hc'))
            · simp [hp, hc']
          · simp [hp]
        have hz2 : z2 = 0 := by
          dsimp only [z2]
          by_cases hp : ({a, b} : Finset (Fin 10)) = {i, k}
          · by_cases hc' : ({c, d} : Finset (Fin 10)) = {j, l}
            · exact False.elim (hset
                ((fourSet_eq_of_pair_equalities a b c d i k j l hp hc').trans
                  (by ext x; simp [or_comm, or_left_comm, or_assoc])))
            · simp [hp, hc']
          · simp [hp]
        have hz3 : z3 = 0 := by
          dsimp only [z3]
          by_cases hp : ({a, b} : Finset (Fin 10)) = {i, l}
          · by_cases hc' : ({c, d} : Finset (Fin 10)) = {j, k}
            · exact False.elim (hset
                ((fourSet_eq_of_pair_equalities a b c d i l j k hp hc').trans
                  (by ext x; simp [or_comm, or_left_comm, or_assoc])))
            · simp [hp, hc']
          · simp [hp]
        have hz4 : z4 = 0 := by
          dsimp only [z4]
          by_cases hc' : ({c, d} : Finset (Fin 10)) = {i, j}
          · by_cases hp : ({a, b} : Finset (Fin 10)) = {k, l}
            · exact False.elim (hset
                ((fourSet_eq_of_pair_equalities a b c d k l i j hp hc').trans
                  (by ext x; simp [or_comm, or_left_comm, or_assoc])))
            · simp [hc', hp]
          · simp [hc']
        have hz5 : z5 = 0 := by
          dsimp only [z5]
          by_cases hc' : ({c, d} : Finset (Fin 10)) = {i, k}
          · by_cases hp : ({a, b} : Finset (Fin 10)) = {j, l}
            · exact False.elim (hset
                ((fourSet_eq_of_pair_equalities a b c d j l i k hp hc').trans
                  (by ext x; simp [or_comm, or_left_comm, or_assoc])))
            · simp [hc', hp]
          · simp [hc']
        have hz6 : z6 = 0 := by
          dsimp only [z6]
          by_cases hc' : ({c, d} : Finset (Fin 10)) = {i, l}
          · by_cases hp : ({a, b} : Finset (Fin 10)) = {j, k}
            · exact False.elim (hset
                ((fourSet_eq_of_pair_equalities a b c d j k i l hp hc').trans
                  (by ext x; simp [or_comm, or_left_comm, or_assoc])))
            · simp [hc', hp]
          · simp [hc']
        symm
        rw [hz1, hz2, hz3, hz4, hz5, hz6]
        simp
    · have hset : ({a, b, c, d} : Finset (Fin 10)) ≠ {i, j, k, l} := by
        intro h
        apply hinput
        rw [h]
        exact hcard
      rw [if_neg hset]
      have hrepeated : a = b ∨ a = c ∨ a = d ∨
          b = c ∨ b = d ∨ c = d := by
        by_contra h
        simp only [not_or] at h
        apply hinput
        exact Finset.card_eq_four.mpr
          ⟨a, b, c, d, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
            h.2.2.2.2.1, h.2.2.2.2.2, rfl⟩
      rcases hrepeated with h | h | h | h | h | h <;> subst_vars <;>
        simp only [ambientTwoCoeff_squarefreeWedge, coordinateLinearTen] <;>
        ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · rw [if_neg hcard]
    have hrepeated : i = j ∨ i = k ∨ i = l ∨
        j = k ∨ j = l ∨ k = l := by
      by_contra h
      simp only [not_or] at h
      apply hcard
      exact Finset.card_eq_four.mpr
        ⟨i, j, k, l, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
          h.2.2.2.2.1, h.2.2.2.2.2, rfl⟩
    rcases hrepeated with h | h | h | h | h | h <;> subst_vars <;>
      simp only [ambientTwoCoeff_squarefreeWedge, coordinateLinearTen] <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]

def ambientWedgeTwoBilinear :
    TwoForm →ₗ[F₂] TwoForm →ₗ[F₂] AmbientFourForm where
  toFun q := ambientWedgeTwoMap q
  map_add' q r := by
    apply LinearMap.ext
    intro c
    funext i j k l
    change ambientWedgeTwo (q + r) c i j k l =
      ambientWedgeTwo q c i j k l + ambientWedgeTwo r c i j k l
    simp only [ambientWedgeTwo, ambientTwoCoeff_add]
    ring
  map_smul' a q := by
    apply LinearMap.ext
    intro c
    funext i j k l
    change ambientWedgeTwo (a • q) c i j k l =
      (a • ambientWedgeTwo q c) i j k l
    simp only [ambientWedgeTwo, ambientTwoCoeff_smul,
      Pi.smul_apply, smul_eq_mul]
    ring

private theorem anfFourProjectionTen_quadraticMonomial_mul
    (s t : QuadraticIndex 10) :
    anfFourProjectionTen (monomial s.1 * monomial t.1) =
      ambientWedgeTwo
        ((Pi.basisFun F₂ (QuadraticIndex 10)) s)
        ((Pi.basisFun F₂ (QuadraticIndex 10)) t) := by
  rcases QuadraticIndex.exists_pair s with ⟨a, b, hab, rfl⟩
  rcases QuadraticIndex.exists_pair t with ⟨c, d, hcd, rfl⟩
  change anfFourProjectionTen
    (monomial ({a, b} : Finset (Fin 10)) *
      monomial ({c, d} : Finset (Fin 10))) = _
  have habMonomial : monomial ({a, b} : Finset (Fin 10)) = X a * X b := by
    simp [X]
  have hcdMonomial : monomial ({c, d} : Finset (Fin 10)) = X c * X d := by
    simp [X]
  rw [habMonomial, hcdMonomial, anfFourProjectionTen_four_X,
    quadraticBasisPair_eq_wedge, quadraticBasisPair_eq_wedge]

/-- Literal quartic coefficients of a pure-quadratic Boolean product are
the ambient exterior product used by the envelope modules. -/
theorem anfFourProjectionTen_quadratic_mul_quadratic
    (q c : TwoForm) :
    anfFourProjectionTen (quadraticANFOfForm q * quadraticANFOfForm c) =
      ambientWedgeTwo q c := by
  classical
  let qSum := ∑ s : QuadraticIndex 10,
    q s • (Pi.basisFun F₂ (QuadraticIndex 10)) s
  let cSum := ∑ t : QuadraticIndex 10,
    c t • (Pi.basisFun F₂ (QuadraticIndex 10)) t
  have hq : qSum = q := (twoForm_eq_sum_basis q).symm
  have hc : cSum = c := (twoForm_eq_sum_basis c).symm
  calc
    anfFourProjectionTen (quadraticANFOfForm q * quadraticANFOfForm c) =
        ∑ t : QuadraticIndex 10, ∑ s : QuadraticIndex 10,
          (c t * q s) •
            anfFourProjectionTen (monomial s.1 * monomial t.1) := by
      rw [quadraticANFOfForm, quadraticANFOfForm]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm, map_sum, map_smul, Finset.smul_sum, smul_smul]
    _ = ambientWedgeTwoBilinear qSum cSum := by
      simp only [qSum, cSum, map_sum, map_smul,
        anfFourProjectionTen_quadraticMonomial_mul]
      apply Finset.sum_congr rfl
      intro t _ht
      simp only [LinearMap.coe_sum, Finset.sum_apply,
        LinearMap.smul_apply]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      simp [smul_smul, ambientWedgeTwoBilinear, ambientWedgeTwoMap, mul_comm]
    _ = ambientWedgeTwo q c := by
      rw [hq, hc]
      rfl

theorem anfFourProjectionTen_eq_zero_of_degreeLE_three
    {p : ANF 10} (hp : N4.DegreeLE 3 p) :
    anfFourProjectionTen p = 0 := by
  funext i j k l
  change (if ({i, j, k, l} : Finset (Fin 10)).card = 4
    then p.coeff ⟨{i, j, k, l}⟩ else 0) = 0
  by_cases hcard : ({i, j, k, l} : Finset (Fin 10)).card = 4
  · rw [if_pos hcard]
    apply hp ⟨{i, j, k, l}⟩
    change 3 < ({i, j, k, l} : Finset (Fin 10)).card
    omega
  · rw [if_neg hcard]

theorem quadraticANFOfForm_degreeLE_two (q : TwoForm) :
    N4.DegreeLE 2 (quadraticANFOfForm q) :=
  pureQuadraticANFSpace_le_quadraticANFSpace ⟨q, rfl⟩

@[simp] theorem anfFourProjectionTen_one :
    anfFourProjectionTen (1 : ANF 10) = 0 :=
  anfFourProjectionTen_eq_zero_of_degreeLE_three
    ((N4.affine_le_quadraticANFSpace (one_mem_affine 10)).mono (by omega))

@[simp] theorem anfFourProjectionTen_linearANFTen
    (ell : LinearForm) :
    anfFourProjectionTen (linearANFTen ell) = 0 :=
  anfFourProjectionTen_eq_zero_of_degreeLE_three
    ((linearANFTen_degreeLE_one ell).mono (by omega))

@[simp] theorem anfFourProjectionTen_quadraticANFOfForm
    (q : TwoForm) :
    anfFourProjectionTen (quadraticANFOfForm q) = 0 :=
  anfFourProjectionTen_eq_zero_of_degreeLE_three
    ((quadraticANFOfForm_degreeLE_two q).mono (by omega))

@[simp] theorem anfFourProjectionTen_linear_mul_linear
    (ell m : LinearForm) :
    anfFourProjectionTen (linearANFTen ell * linearANFTen m) = 0 :=
  anfFourProjectionTen_eq_zero_of_degreeLE_three
    (((linearANFTen_degreeLE_one ell).mul
      (linearANFTen_degreeLE_one m)).mono (by omega))

@[simp] theorem anfFourProjectionTen_linear_mul_quadratic
    (ell : LinearForm) (q : TwoForm) :
    anfFourProjectionTen (linearANFTen ell * quadraticANFOfForm q) = 0 :=
  anfFourProjectionTen_eq_zero_of_degreeLE_three
    ((linearANFTen_degreeLE_one ell).mul
      (quadraticANFOfForm_degreeLE_two q))

@[simp] theorem anfFourProjectionTen_quadratic_mul_linear
    (q : TwoForm) (ell : LinearForm) :
    anfFourProjectionTen (quadraticANFOfForm q * linearANFTen ell) = 0 := by
  rw [mul_comm]
  exact anfFourProjectionTen_linear_mul_quadratic ell q

/-- The quartic part of a product of arbitrary degree-two factors depends
only on their pure quadratic coordinates. -/
theorem anfFourProjectionTen_quadraticCoordinateANF_mul
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    anfFourProjectionTen
        (quadraticCoordinateANF a ell q *
          quadraticCoordinateANF b m c) =
      ambientWedgeTwo q c := by
  simp only [quadraticCoordinateANF, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, map_add, map_smul,
    anfFourProjectionTen_one, anfFourProjectionTen_linearANFTen,
    anfFourProjectionTen_quadraticANFOfForm,
    anfFourProjectionTen_linear_mul_linear,
    anfFourProjectionTen_linear_mul_quadratic,
    anfFourProjectionTen_quadratic_mul_linear, smul_zero, zero_add]
  exact anfFourProjectionTen_quadratic_mul_quadratic q c

/-- Equality of two literal low-product high classes forces equality of
their quartic exterior tensors. -/
theorem ambientWedgeTwo_eq_of_highClass_eq
    (ell m ell' m' : LinearForm) (q c q' c' : TwoForm)
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c') :
    ambientWedgeTwo q c = ambientWedgeTwo q' c' := by
  let p := quadraticCoordinateANF 0 ell q *
    quadraticCoordinateANF 0 m c
  let p' := quadraticCoordinateANF 0 ell' q' *
    quadraticCoordinateANF 0 m' c'
  have hquot : highProjectionTen (p + p') = 0 := by
    rw [map_add]
    change lowProductHighClass ell m q c +
      lowProductHighClass ell' m' q' c' = 0
    rw [hhigh]
    calc
      lowProductHighClass ell' m' q' c' +
          lowProductHighClass ell' m' q' c' =
          ((1 : F₂) + 1) • lowProductHighClass ell' m' q' c' := by
            rw [add_smul, one_smul]
      _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  have hquad : p + p' ∈ N4.quadraticANFSpace 10 :=
    (highProjectionTen_eq_zero_iff (p + p')).1 hquot
  have hfour := anfFourProjectionTen_eq_zero_of_degreeLE_three
    (hquad.mono (by omega))
  rw [map_add] at hfour
  change anfFourProjectionTen p + anfFourProjectionTen p' = 0 at hfour
  rw [anfFourProjectionTen_quadraticCoordinateANF_mul,
    anfFourProjectionTen_quadraticCoordinateANF_mul] at hfour
  have hself (x : AmbientFourForm) : x + x = 0 := by
    calc
      x + x = ((1 : F₂) + 1) • x := by rw [add_smul, one_smul]
      _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  calc
    ambientWedgeTwo q c = ambientWedgeTwo q c + 0 := by rw [add_zero]
    _ = ambientWedgeTwo q c +
        (ambientWedgeTwo q' c' + ambientWedgeTwo q' c') := by
          rw [hself]
    _ = (ambientWedgeTwo q c + ambientWedgeTwo q' c') +
        ambientWedgeTwo q' c' := by ac_rfl
    _ = ambientWedgeTwo q' c' := by rw [hfour, zero_add]

end
end N5
end UnrestrictedBooleanMul
