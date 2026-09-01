import UnrestrictedBooleanMul.N5.Prefix
import UnrestrictedBooleanMul.N4.SemanticQuadratic

/-!
# Algebraic flattening of quadratic prefixes

The recursive Reed--Muller minimum-word theorem in the completed `n = 4`
development is dimension-polymorphic.  This file supplies only its
ten-variable ANF bridge, proves the quadratic product alternative, and then
performs the usual triangular flattening of an all-quadratic circuit prefix.
No truth table or circuit presentation is enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

set_option maxRecDepth 50000

/-! ## Ten-variable semantic bridge -/

/-- ANF represented by a recursive affine code on ten variables. -/
def affineCodeANF (a : N4.AffineCode 10) : ANF 10 :=
  a.constantCoeff • (1 : ANF 10) +
    ∑ i, a.linearCoeff i • X i

theorem affineCodeANF_mem_affine (a : N4.AffineCode 10) :
    affineCodeANF a ∈ affine 10 := by
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (one_mem_affine 10)
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (X_mem_affine i)

@[simp] theorem eval_affineCodeANF (a : N4.AffineCode 10)
    (x : Fin 10 → F₂) :
    eval (affineCodeANF a) x = a.eval x := by
  rw [a.eval_eq_coeff_formula]
  have hsum : eval (∑ i, a.linearCoeff i • X i) x =
      ∑ i, a.linearCoeff i * x i := by
    rw [eval_eq_evalHom, map_sum]
    simp_rw [map_smul, ← eval_eq_evalHom, eval_X]
    rfl
  simp [affineCodeANF, eval_add', eval_smul', hsum]

/-- A ten-variable ANF represented by a recursive quadratic code. -/
def QuadraticSemanticTen (p : ANF 10) : Prop :=
  ∃ q : N4.QuadraticCode 10, ∀ x, q.eval x = eval p x

def quadraticSemanticTenSpace : Submodule F₂ (ANF 10) where
  carrier := {p | QuadraticSemanticTen p}
  zero_mem' := by
    refine ⟨N4.QuadraticCode.zero 10, ?_⟩
    intro x
    simp
  add_mem' := by
    rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a.add b, ?_⟩
    intro x
    simp [ha, hb, eval_add']
  smul_mem' := by
    rintro k p ⟨q, hq⟩
    refine ⟨q.smul k, ?_⟩
    intro x
    simp [hq, eval_smul']

theorem affine_monomial_semantic_ten (i : Fin 10) :
    X i ∈ quadraticSemanticTenSpace := by
  let a := N4.AffineCode.ofCoeffs 10 0
    (fun j => if j = i then 1 else 0)
  refine ⟨a.toQuadratic, ?_⟩
  intro x
  simp [a, eval_X]

theorem one_semantic_ten : (1 : ANF 10) ∈ quadraticSemanticTenSpace := by
  let a := N4.AffineCode.ofCoeffs 10 1 (fun _ => 0)
  refine ⟨a.toQuadratic, ?_⟩
  intro x
  simp [a]

theorem quadratic_monomial_semantic_ten (i j : Fin 10) :
    X i * X j ∈ quadraticSemanticTenSpace := by
  let a := N4.AffineCode.ofCoeffs 10 0
    (fun k => if k = i then 1 else 0)
  let b := N4.AffineCode.ofCoeffs 10 0
    (fun k => if k = j then 1 else 0)
  refine ⟨N4.QuadraticCode.mulAffine a b, ?_⟩
  intro x
  simp [a, b, eval_mul', eval_X]

def lowReconstructTen (p : ANF 10) : ANF 10 :=
  ∑ s : Monomial 10,
    if s.vars.card ≤ 2 then p.coeff s • monomial s.vars else 0

theorem lowReconstructTen_eq {p : ANF 10} (hp : N4.DegreeLE 2 p) :
    lowReconstructTen p = p := by
  apply MonoidAlgebra.coeff_injective
  ext t
  simp only [lowReconstructTen, MonoidAlgebra.coeff_sum]
  change (∑ c : Monomial 10,
    (if c.vars.card ≤ 2 then p.coeff c • monomial c.vars else 0).coeff t) =
      p.coeff t
  rw [Finset.sum_eq_single t]
  · by_cases ht : t.vars.card ≤ 2
    · have hself : (monomial t.vars : ANF 10).coeff t = 1 := by
        rw [show t = ⟨t.vars⟩ by cases t; rfl]
        simp
      simp [ht, hself]
    · have hpt : p.coeff t = 0 := hp t (by omega)
      simp [ht, hpt]
  · intro c _hc hct
    have hvars : c.vars ≠ t.vars := by
      intro h
      apply hct
      exact Monomial.ext h
    have hcoeff : (monomial c.vars : ANF 10).coeff t = 0 := by
      rw [show t = ⟨t.vars⟩ by cases t; rfl]
      simp [hvars]
    split_ifs
    · change p.coeff c * (monomial c.vars : ANF 10).coeff t = 0
      rw [hcoeff, mul_zero]
    · simp
  · simp

theorem monomial_semantic_ten_of_card_le_two (s : Monomial 10)
    (hs : s.vars.card ≤ 2) :
    monomial s.vars ∈ quadraticSemanticTenSpace := by
  interval_cases hcard : s.vars.card
  · have hs0 : s.vars = ∅ := Finset.card_eq_zero.mp hcard
    rw [hs0]
    have hmono : (monomial ∅ : ANF 10) = 1 := by
      rw [monomial, MonoidAlgebra.one_def]
      congr 1
    rw [hmono]
    exact one_semantic_ten
  · rcases Finset.card_eq_one.mp hcard with ⟨i, hi⟩
    rw [hi]
    exact affine_monomial_semantic_ten i
  · rcases Finset.card_eq_two.mp hcard with ⟨i, j, hij, hsij⟩
    rw [hsij]
    simpa [X] using quadratic_monomial_semantic_ten i j

theorem quadratic_semantic_ten_of_degreeLE {p : ANF 10}
    (hp : N4.DegreeLE 2 p) :
    p ∈ quadraticSemanticTenSpace := by
  rw [← lowReconstructTen_eq hp]
  apply Submodule.sum_mem
  intro s _
  split_ifs with hs
  · exact Submodule.smul_mem _ _
      (monomial_semantic_ten_of_card_le_two s hs)
  · exact Submodule.zero_mem _

theorem anf_eq_of_eval_eq_ten {p q : ANF 10}
    (h : ∀ x, eval p x = eval q x) : p = q := by
  apply eval_injective 10
  funext x
  exact h x

def quadraticOneCodeTen : N4.QuadraticCode 10 :=
  (N4.AffineCode.ofCoeffs 10 1 (fun _ => 0)).toQuadratic

def fiber00Ten (p q g : N4.QuadraticCode 10) : N4.QuadraticCode 10 :=
  ((quadraticOneCodeTen.add p).add q).add g

def fiber01Ten (q g : N4.QuadraticCode 10) : N4.QuadraticCode 10 := q.add g
def fiber10Ten (p g : N4.QuadraticCode 10) : N4.QuadraticCode 10 := p.add g

theorem fiber_weights_sum_ten (p q g : N4.QuadraticCode 10)
    (hg : ∀ x, g.eval x = p.eval x * q.eval x) :
    N4.truthWeight (fiber00Ten p q g).eval +
      N4.truthWeight (fiber01Ten q g).eval +
      N4.truthWeight (fiber10Ten p g).eval +
      N4.truthWeight g.eval = 1024 := by
  unfold N4.truthWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hone (x : Fin 10 → F₂) : quadraticOneCodeTen.eval x = 1 := by
    simp [quadraticOneCodeTen]
  simp_rw [fiber00Ten, fiber01Ten, fiber10Ten,
    N4.QuadraticCode.eval_add, hone, hg, N4.fiber_truth_identity]
  norm_num

theorem quadraticCodeTen_exists_eval_ne_zero_of_weight_pos
    {q : N4.QuadraticCode 10} (h : 0 < N4.truthWeight q.eval) :
    ∃ x, q.eval x ≠ 0 := by
  by_contra hz
  push Not at hz
  have hall : ∀ x, q.eval x = 0 := hz
  unfold N4.truthWeight at h
  simp [hall, N4.truthBit] at h

theorem quadraticCodeTen_eval_eq_zero_of_weight_zero
    {q : N4.QuadraticCode 10} (h : N4.truthWeight q.eval = 0) :
    ∀ x, q.eval x = 0 := by
  intro x
  have hx := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Nat.zero_le _)).mp h x (Finset.mem_univ x)
  by_contra hne
  simp [N4.truthBit, hne] at hx

/-- Ten-variable Boyar--Find product alternative.  If a product of two
quadratic Boolean functions is again quadratic, its quadratic shadow is
inherited from its factors or is decomposable. -/
theorem quadratic_product_projection_alternative_ten
    {p q g : ANF 10} (hgate : g = p * q)
    (hp : N4.DegreeLE 2 p) (hq : N4.DegreeLE 2 q)
    (hg : N4.DegreeLE 2 g) :
    quadraticProjection 10 g ∈
        Submodule.span F₂
          {quadraticProjection 10 p, quadraticProjection 10 q} ∨
      IsDecomposableTwo (quadraticProjection 10 g) := by
  rcases quadratic_semantic_ten_of_degreeLE hp with ⟨pc, hpc⟩
  rcases quadratic_semantic_ten_of_degreeLE hq with ⟨qc, hqc⟩
  rcases quadratic_semantic_ten_of_degreeLE hg with ⟨gc, hgc⟩
  have hcode (x : Fin 10 → F₂) : gc.eval x = pc.eval x * qc.eval x := by
    rw [hgc, hgate, eval_mul', ← hpc, ← hqc]
  have htotal := fiber_weights_sum_ten pc qc gc hcode
  by_cases h00 : N4.truthWeight (fiber00Ten pc qc gc).eval = 0
  · left
    have hz := quadraticCodeTen_eval_eq_zero_of_weight_zero h00
    have heval : ∀ x, eval g x = eval ((1 : ANF 10) + p + q) x := by
      intro x
      have hx := hz x
      simp only [fiber00Ten, quadraticOneCodeTen,
        N4.QuadraticCode.eval_add, N4.AffineCode.eval_toQuadratic,
        N4.AffineCode.eval_ofCoeffs] at hx
      rw [eval_add', eval_add', eval_one', ← hpc, ← hqc, ← hgc]
      exact (N4.f2_eq_iff_add_eq_zero _ _).2 (by
        simpa [add_assoc, add_comm, add_left_comm] using hx)
    have heq := anf_eq_of_eval_eq_ten heval
    rw [heq, map_add, map_add, quadraticProjection_one, zero_add]
    exact (Submodule.span F₂
      {quadraticProjection 10 p, quadraticProjection 10 q}).add_mem
        (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
  · by_cases h01 : N4.truthWeight (fiber01Ten qc gc).eval = 0
    · left
      have hz := quadraticCodeTen_eval_eq_zero_of_weight_zero h01
      have heval : ∀ x, eval g x = eval q x := by
        intro x
        have hx := hz x
        simp only [fiber01Ten, N4.QuadraticCode.eval_add] at hx
        rw [← hgc, ← hqc]
        exact (N4.f2_eq_iff_add_eq_zero _ _).2
          (by simpa [add_comm] using hx)
      rw [anf_eq_of_eval_eq_ten heval]
      exact Submodule.subset_span (by simp)
    · by_cases h10 : N4.truthWeight (fiber10Ten pc gc).eval = 0
      · left
        have hz := quadraticCodeTen_eval_eq_zero_of_weight_zero h10
        have heval : ∀ x, eval g x = eval p x := by
          intro x
          have hx := hz x
          simp only [fiber10Ten, N4.QuadraticCode.eval_add] at hx
          rw [← hgc, ← hpc]
          exact (N4.f2_eq_iff_add_eq_zero _ _).2
            (by simpa [add_comm] using hx)
        rw [anf_eq_of_eval_eq_ten heval]
        exact Submodule.subset_span (by simp)
      · by_cases h11 : N4.truthWeight gc.eval = 0
        · left
          have hz := quadraticCodeTen_eval_eq_zero_of_weight_zero h11
          have heval : ∀ x, eval g x = eval (0 : ANF 10) x := by
            intro x
            rw [← hgc, hz]
            simp
          rw [anf_eq_of_eval_eq_ten heval, map_zero]
          exact Submodule.zero_mem _
        · have hp00 : 0 < N4.truthWeight (fiber00Ten pc qc gc).eval :=
            Nat.pos_of_ne_zero h00
          have hp01 : 0 < N4.truthWeight (fiber01Ten qc gc).eval :=
            Nat.pos_of_ne_zero h01
          have hp10 : 0 < N4.truthWeight (fiber10Ten pc gc).eval :=
            Nat.pos_of_ne_zero h10
          have hp11 : 0 < N4.truthWeight gc.eval := Nat.pos_of_ne_zero h11
          have hl00 := N4.QuadraticCode.minimum_weight (n := 10) (by omega)
            (quadraticCodeTen_exists_eval_ne_zero_of_weight_pos hp00)
          have hl01 := N4.QuadraticCode.minimum_weight (n := 10) (by omega)
            (quadraticCodeTen_exists_eval_ne_zero_of_weight_pos hp01)
          have hl10 := N4.QuadraticCode.minimum_weight (n := 10) (by omega)
            (quadraticCodeTen_exists_eval_ne_zero_of_weight_pos hp10)
          have hl11 := N4.QuadraticCode.minimum_weight (n := 10) (by omega)
            (quadraticCodeTen_exists_eval_ne_zero_of_weight_pos hp11)
          have hw11 : N4.truthWeight gc.eval = 256 := by
            norm_num at hl00 hl01 hl10 hl11 ⊢
            omega
          rcases N4.QuadraticCode.minimum_word_factor (n := 10) (by omega)
              (quadraticCodeTen_exists_eval_ne_zero_of_weight_pos hp11)
              (by norm_num; exact hw11) with ⟨a, b, hab⟩
          right
          have heval : ∀ x,
              eval g x = eval (affineCodeANF a * affineCodeANF b) x := by
            intro x
            rw [eval_mul', eval_affineCodeANF, eval_affineCodeANF,
              ← hab, hgc]
          rw [anf_eq_of_eval_eq_ten heval]
          exact quadraticProjection_affineProduct
            (affineCodeANF_mem_affine a) (affineCodeANF_mem_affine b)

/-! ## Triangular prefix flattening -/

/-- One decomposable generator for each gate of a fixed prefix. -/
def prefixFlattenGenerator {r j : Nat} (C : Circuit 10 r) (hj : j ≤ r)
    (i : Fin j) : TwoForm := by
  classical
  exact if IsDecomposableTwo
      (quadraticProjection 10
        (C.gate ⟨i.val, lt_of_lt_of_le i.isLt hj⟩)) then
    quadraticProjection 10
      (C.gate ⟨i.val, lt_of_lt_of_le i.isLt hj⟩) else 0

theorem prefixFlattenGenerator_decomposable {r j : Nat}
    (C : Circuit 10 r) (hj : j ≤ r) (i : Fin j) :
    IsDecomposableTwo (prefixFlattenGenerator C hj i) := by
  classical
  unfold prefixFlattenGenerator
  split_ifs with h
  · exact h
  · exact decomposableTwo_zero

theorem quadraticProjection_mem_of_mem_wire {r : Nat}
    (C : Circuit 10 r) (j : Nat) (S : Submodule F₂ TwoForm)
    (hprev : ∀ i : Fin r, i.val < j →
      quadraticProjection 10 (C.gate i) ∈ S)
    {p : ANF 10} (hp : p ∈ wireSpace C.gate j) :
    quadraticProjection 10 p ∈ S := by
  rw [wireSpace] at hp
  rcases Submodule.mem_sup.mp hp with ⟨a, ha, w, hw, rfl⟩
  rw [map_add, quadraticProjection_kills_affine 10 ha, zero_add]
  refine Submodule.span_induction (p := fun w _ =>
      quadraticProjection 10 w ∈ S) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨i, hi, rfl⟩
    exact hprev i hi
  · simp
  · intro x y _ _ hx hy
    simpa using S.add_mem hx hy
  · intro a x _ hx
    simpa using S.smul_mem a hx

theorem gate_projection_alternative_ten {r j : Nat}
    (C : Circuit 10 r)
    (hall : ∀ i : Fin r, i.val < j → C.gate i ∈ N4.quadraticANFSpace 10)
    (i : Fin r) (hi : i.val < j) :
    quadraticProjection 10 (C.gate i) ∈
        Submodule.span F₂
          {quadraticProjection 10 (C.left i),
            quadraticProjection 10 (C.right i)} ∨
      IsDecomposableTwo (quadraticProjection 10 (C.gate i)) := by
  have hwire : wireSpace C.gate i.val ≤ N4.quadraticANFSpace 10 :=
    N4.wireSpace_le_quadratic_of_prefix C.gate
      (fun k hk => hall k (lt_trans hk hi))
  exact quadratic_product_projection_alternative_ten (C.gate_eq i)
    (hwire (C.left_mem i)) (hwire (C.right_mem i)) (hall i hi)

theorem projected_prefix_gate_mem_flatten_span {r j : Nat}
    (C : Circuit 10 r) (hj : j ≤ r)
    (hall : ∀ i : Fin r, i.val < j → C.gate i ∈ N4.quadraticANFSpace 10)
    (i : Fin r) (hi : i.val < j) :
    quadraticProjection 10 (C.gate i) ∈
      decomposablePresentationSpan (prefixFlattenGenerator C hj) := by
  classical
  let S := decomposablePresentationSpan (prefixFlattenGenerator C hj)
  have hstrong : ∀ k : Nat, ∀ hkj : k < j,
      quadraticProjection 10
          (C.gate ⟨k, lt_of_lt_of_le hkj hj⟩) ∈ S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hkj
        have hkr : k < r := lt_of_lt_of_le hkj hj
        let gateIndex : Fin r := ⟨k, hkr⟩
        let prefixIndex : Fin j := ⟨k, hkj⟩
        by_cases hdec : IsDecomposableTwo
            (quadraticProjection 10 (C.gate gateIndex))
        · apply Submodule.subset_span
          refine ⟨prefixIndex, ?_⟩
          simp [prefixIndex, gateIndex, prefixFlattenGenerator, hdec]
        · rcases gate_projection_alternative_ten C hall gateIndex hkj with
            hspan | hdec'
          · apply (Submodule.span_le.mpr ?_) hspan
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact quadraticProjection_mem_of_mem_wire C k S
                (fun a ha => ih a ha (lt_trans ha hkj)) (C.left_mem gateIndex)
            · exact quadraticProjection_mem_of_mem_wire C k S
                (fun a ha => ih a ha (lt_trans ha hkj)) (C.right_mem gateIndex)
          · exact (hdec hdec').elim
  simpa only using hstrong i.val hi

/-- Every all-quadratic prefix has a semantic flattening certificate with one
decomposable generator per gate. -/
noncomputable def quadraticPrefixFlattening_of_all_quadratic {r j : Nat}
    (C : Circuit 10 r) (hj : j ≤ r)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10) :
    QuadraticPrefixFlattening C j := by
  let q := prefixFlattenGenerator C hj
  refine ⟨q, prefixFlattenGenerator_decomposable C hj, ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    unfold q prefixFlattenGenerator
    split_ifs with hdec
    · refine ⟨C.gate ⟨i.val, lt_of_lt_of_le i.isLt hj⟩, ?_, rfl⟩
      exact gate_mem_wireSpace C.gate
        ⟨i.val, lt_of_lt_of_le i.isLt hj⟩ i.isLt
    · exact Submodule.zero_mem _
  · rintro y ⟨p, hp, rfl⟩
    exact quadraticProjection_mem_of_mem_wire C j
      (decomposablePresentationSpan q)
      (fun i hi => projected_prefix_gate_mem_flatten_span C hj hall i hi) hp

/-- The complete manuscript bookkeeping package for an all-quadratic prefix. -/
theorem allQuadraticPrefix_bookkeeping {r j : Nat}
    (C : Circuit 10 r) (hj : j ≤ r)
    (hnr : ∀ i : Fin r, i.val < j → N4.NonredundantAt C i)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10) :
    j = N4.flagTargetRank (N4.circuitFlag C j) (mulTarget 5) +
          N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) ∧
      N4.flagTargetRank (N4.circuitFlag C j) (mulTarget 5) ≤
        targetCapacity
          (presentationDefect
            (quadraticPrefixFlattening_of_all_quadratic C hj hall).generator) ∧
      Module.finrank F₂
          (presentationDefect
            (quadraticPrefixFlattening_of_all_quadratic C hj hall).generator) ≤
        N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) := by
  exact circuit_bookkeeping_capacity C hj hnr
    (quadraticPrefixFlattening_of_all_quadratic C hj hall)

/-- Computing all nine outputs puts the whole Hankel target in the quadratic
image of the final wire space. -/
theorem targetTwoSpace_le_quadraticPrefixImage_final {r : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) :
    targetTwoSpace ≤ quadraticPrefixImage C r := by
  have htarget : mulTarget 5 ≤ C.finalWire := by
    rw [mulTarget, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hC i
  rintro _ ⟨c, rfl⟩
  refine ⟨targetANF c, ?_, quadraticProjection_targetANF c⟩
  exact htarget (targetANF_mem_mulTarget c)

/-- An all-quadratic twelve-AND circuit cannot compute five-term
multiplication.  This is the semantic flattening corollary of the capacity
obstruction, not an imported quadratic-rank result. -/
theorem no_all_quadratic_twelve_circuit (C : Circuit 10 12)
    (hC : C.Computes (Mul 5))
    (hall : ∀ i : Fin 12, C.gate i ∈ N4.quadraticANFSpace 10) : False := by
  let hflat := quadraticPrefixFlattening_of_all_quadratic C (le_refl 12)
    (fun i _ => hall i)
  apply no_twelve_decomposable_span hflat.generator hflat.decomposable
  rw [hflat.span_eq]
  exact targetTwoSpace_le_quadraticPrefixImage_final C hC

end

end N5
end UnrestrictedBooleanMul
