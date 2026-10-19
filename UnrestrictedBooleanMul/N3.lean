module

public import UnrestrictedBooleanMul.N3.ProductC3
public import UnrestrictedBooleanMul.N3.ProductC20
public import UnrestrictedBooleanMul.N3.ProductC25
public import UnrestrictedBooleanMul.N3.ProductC30
public import UnrestrictedBooleanMul.N3.ProductC31
public import UnrestrictedBooleanMul.N3.ProductC32
public import UnrestrictedBooleanMul.N3.ProductC34
public import UnrestrictedBooleanMul.N3.ProductG0
public import UnrestrictedBooleanMul.N3.ProductG1
public import UnrestrictedBooleanMul.N3.Geometry

@[expose] public section

namespace UnrestrictedBooleanMul

open N3Certificate

noncomputable section

theorem algebraic_cert (a b : Fin 10 → F₂) (z : Fin 12 → F₂)
    (h : rationalRep a * rationalRep b = ambientRep z) :
    z 8 = z 9 ∧ z 9 = z 10 := by
  have h3 : c3 a b = 0 := by
    rw [← product_coeff_c3, h]
    solve_ambient_coeff
  have h20 : c20 a b = 0 := by
    rw [← product_coeff_c20, h]
    solve_ambient_coeff
  have h25 : c25 a b = 0 := by
    rw [← product_coeff_c25, h]
    solve_ambient_coeff
  have h30 : c30 a b = 0 := by
    rw [← product_coeff_c30, h]
    solve_ambient_coeff
  have h31 : c31 a b = 0 := by
    rw [← product_coeff_c31, h]
    solve_ambient_coeff
  have h32 : c32 a b = 0 := by
    rw [← product_coeff_c32, h]
    solve_ambient_coeff
  have h34 : c34 a b = 0 := by
    rw [← product_coeff_c34, h]
    solve_ambient_coeff
  have hg0 := N3Certificate.cert0 a b h3 h25 h31 h32
  have hg1 := N3Certificate.cert1 a b h20 h30 h32 h34
  rw [← product_coeff_g0, h] at hg0
  rw [← product_coeff_g1, h] at hg1
  have hz89 : z 8 + z 9 = 0 := by
    simpa +decide [ambientRep, ambientBasis, UnrestrictedBooleanMul.Mul,
      mulCoefficient, aVar, bVar, X, monomial_mul, coeff_monomial,
      Fin.sum_univ_succ] using hg0
  have hz910 : z 9 + z 10 = 0 := by
    simpa +decide [ambientRep, ambientBasis, UnrestrictedBooleanMul.Mul,
      mulCoefficient, aVar, bVar, X, monomial_mul, coeff_monomial,
      Fin.sum_univ_succ] using hg1
  constructor
  · rw [← CharTwo.sub_eq_add] at hz89
    exact sub_eq_zero.mp hz89
  · rw [← CharTwo.sub_eq_add] at hz910
    exact sub_eq_zero.mp hz910

def rationalOfAmbient (z : Fin 12 → F₂) : Fin 10 → F₂ :=
  ![z 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7 + z 8, z 11 + z 8, z 8]

theorem ambientRep_mem_rationalSpace (z : Fin 12 → F₂)
    (h₈₉ : z 8 = z 9) (h₉₁₀ : z 9 = z 10) : ambientRep z ∈ rationalSpace := by
  rw [mem_rationalSpace_iff]
  refine ⟨rationalOfAmbient z, ?_⟩
  simp [rationalOfAmbient, rationalRep, ambientRep, rationalBasis, ambientBasis,
    targetSum, Fin.sum_univ_succ]
  rw [← h₈₉, ← h₉₁₀, ← h₈₉]
  match_scalars <;> simp [add_assoc, CharTwo.add_self_eq_zero]

theorem rational_mul_mem_of_mem_ambient {f g : ANF 6}
    (hf : f ∈ rationalSpace) (hg : g ∈ rationalSpace)
    (hfg : f * g ∈ ambientSpace) : f * g ∈ rationalSpace := by
  rcases mem_rationalSpace_iff.mp hf with ⟨x, rfl⟩
  rcases mem_rationalSpace_iff.mp hg with ⟨y, rfl⟩
  rcases mem_ambientSpace_iff.mp hfg with ⟨z, hz⟩
  have hcoeff := algebraic_cert x y z hz.symm
  rw [← hz]
  exact ambientRep_mem_rationalSpace z hcoeff.1 hcoeff.2

theorem mul_three_one_not_mem_rationalSpace :
    UnrestrictedBooleanMul.Mul 3 1 ∉ rationalSpace := by
  intro h
  rcases mem_rationalSpace_iff.mp h with ⟨c, hc⟩
  have hp := congrArg ambientProjection hc
  have h₈ := congrFun hp 8
  have h₉ := congrFun hp 9
  simp [rationalRep, rationalBasis, targetSum, Fin.sum_univ_succ,
    Pi.basisFun] at h₈ h₉
  exact one_ne_zero (h₈.symm.trans h₉)

theorem finalWire_finrank_le_twelve (C : Circuit 6 5) :
    Module.finrank F₂ C.finalWire ≤ 12 := by
  rw [C.finalWire_eq]
  have hg : Module.finrank F₂ (Submodule.span F₂ (Set.range C.gate)) ≤ 5 := by
    exact (finrank_span_le_card (Set.range C.gate)).trans (by
      convert! Fintype.card_range_le C.gate
      rw [Set.toFinset_card])
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (affine 6) (Submodule.span F₂ (Set.range C.gate))
  have ha := affine_six_finrank_le
  omega

theorem ambientSpace_le_finalWire (C : Circuit 6 5)
    (computes : C.Computes (UnrestrictedBooleanMul.Mul 3)) :
    ambientSpace ≤ C.finalWire := by
  rw [ambientSpace_eq_mulAmbient]
  apply sup_le
  · simpa [Circuit.finalWire] using affine_le_wireSpace C.gate (j := 5)
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact computes i

theorem finalWire_eq_ambientSpace (C : Circuit 6 5)
    (computes : C.Computes (UnrestrictedBooleanMul.Mul 3)) :
    C.finalWire = ambientSpace := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (ambientSpace_le_finalWire C computes)
  rw [ambientSpace_finrank]
  exact finalWire_finrank_le_twelve C

theorem five_gate_impossible (C : Circuit 6 5) :
    ¬ C.Computes (UnrestrictedBooleanMul.Mul 3) := by
  intro computes
  have hfinal := finalWire_eq_ambientSpace C computes
  have gatesR : ∀ i : Fin 5, C.gate i ∈ rationalSpace := by
    intro i
    have all : ∀ k : Nat, ∀ hk : k < 5, C.gate ⟨k, hk⟩ ∈ rationalSpace := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk
          let j : Fin 5 := ⟨k, hk⟩
          have hw : wireSpace C.gate k ≤ rationalSpace := by
            apply sup_le affine_le_rationalSpace
            apply Submodule.span_le.mpr
            rintro p ⟨t, ht, rfl⟩
            exact ih t.val ht t.isLt
          have hl : C.left j ∈ rationalSpace := hw (by simpa [j] using C.left_mem j)
          have hr : C.right j ∈ rationalSpace := hw (by simpa [j] using C.right_mem j)
          have hg : C.left j * C.right j ∈ ambientSpace := by
            rw [← C.gate_eq j, ← hfinal]
            exact gate_mem_finalWire C j
          rw [C.gate_eq j]
          exact rational_mul_mem_of_mem_ambient hl hr hg
    exact all i.val i.isLt
  have hfinalR : C.finalWire ≤ rationalSpace := by
    rw [C.finalWire_eq]
    apply sup_le affine_le_rationalSpace
    apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact gatesR i
  exact mul_three_one_not_mem_rationalSpace (hfinalR (computes 1))

theorem mul_three_dimension_lower (r : Nat) (h : HasCircuit (Mul 3) r) : 5 ≤ r := by
  rcases h with ⟨⟨C, computes⟩⟩
  exact circuit_lower_bound_of_projection C (Mul 3) TargetCoordinates.threeProjection
    TargetCoordinates.threeProjection_kills_affine TargetCoordinates.threeProjection_Mul computes

theorem mul_three_lower (r : Nat) (h : HasCircuit (Mul 3) r) : 6 ≤ r := by
  have h₅ := mul_three_dimension_lower r h
  by_contra h₆
  have hr : r = 5 := by omega
  subst r
  rcases h with ⟨⟨C, computes⟩⟩
  exact five_gate_impossible C computes

theorem mc_mul_three : MC(Mul 3) = 6 :=
  mc_eq_of_lower_upper mul_three_upper mul_three_lower

end

end UnrestrictedBooleanMul
