import UnrestrictedBooleanMul.N5.EnvelopeTwoRotation

/-!
# Local-versus-dependent shadows in the first-order envelope

This module isolates the final algebraic calculation in the one-local-
rotation branch of manuscript Lemma 11.2.  After rewiring, one product has
the rational value--jet plane and the other has quadratic plane `(0,d)`.
The result below turns the cubic relation into an old-envelope correction
plus two decomposable quadratic forms.  It uses only exterior bilinearity and
Boolean idempotence; there is no circuit or assignment enumeration.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

attribute [local simp] hankelIndex

@[simp] theorem ambientTwoHadamard_rationalZeroValue_jet :
    ambientTwoHadamard rationalZeroValueTwo rationalZeroJetTwo = 0 := by
  unfold ambientTwoHadamard
  rw [rationalZeroValueTwo_eq_target, rationalZeroJetTwo_eq_target]
  apply twoForm_ext_blocks
  · intro i j hij
    rw [targetTwo_sameA, targetTwo_sameA]
    rfl
  · intro i j hij
    rw [targetTwo_sameB, targetTwo_sameB]
    rfl
  · intro i j
    rw [targetTwo_cross, targetTwo_cross]
    fin_cases i <;> fin_cases j <;>
      simp [rZeroCoeff, jZeroCoeff, hankelIndex]

theorem rationalZeroValueTwo_mem_firstOrderEnvelope :
    rationalZeroValueTwo ∈ firstOrderEnvelopeTwoSpace := by
  rw [rationalZeroValueTwo_eq_target]
  exact targetTwo_exactFirstOrderDirection_mem 0

theorem rationalZeroJetTwo_mem_firstOrderEnvelope :
    rationalZeroJetTwo ∈ firstOrderEnvelopeTwoSpace := by
  rw [rationalZeroJetTwo_eq_target]
  exact targetTwo_exactFirstOrderDirection_mem 3

/-! ## The algebraic Hankel block -/

/-- The sparse set of exterior coordinates used in the zero-jet Hankel
pivot.  These are equations, not a finite atlas of points. -/
private structure RationalZeroHankelBlockRelations
    (z : Fin 5 → F₂) (c : TargetCoeff) : Prop where
  h012 : z 0 * c (hankelIndex 1 2) + z 1 * c (hankelIndex 0 2) = 0
  h013 : z 0 * c (hankelIndex 1 3) + z 1 * c (hankelIndex 0 3) = 0
  h014 : z 0 * c (hankelIndex 1 4) + z 1 * c (hankelIndex 0 4) = 0
  h022 : z 0 * c (hankelIndex 2 2) + z 2 * c (hankelIndex 0 2) = 0
  h023 : z 0 * c (hankelIndex 2 3) + z 2 * c (hankelIndex 0 3) = 0
  h024 : z 0 * c (hankelIndex 2 4) + z 2 * c (hankelIndex 0 4) = 0
  h032 : z 0 * c (hankelIndex 3 2) + z 3 * c (hankelIndex 0 2) = 0
  h033 : z 0 * c (hankelIndex 3 3) + z 3 * c (hankelIndex 0 3) = 0
  h034 : z 0 * c (hankelIndex 3 4) + z 3 * c (hankelIndex 0 4) = 0
  h042 : z 0 * c (hankelIndex 4 2) + z 4 * c (hankelIndex 0 2) = 0
  h043 : z 0 * c (hankelIndex 4 3) + z 4 * c (hankelIndex 0 3) = 0
  h044 : z 0 * c (hankelIndex 4 4) + z 4 * c (hankelIndex 0 4) = 0
  h123 : z 1 * c (hankelIndex 2 3) + z 2 * c (hankelIndex 1 3) = 0
  h124 : z 1 * c (hankelIndex 2 4) + z 2 * c (hankelIndex 1 4) = 0
  h134 : z 1 * c (hankelIndex 3 4) + z 3 * c (hankelIndex 1 4) = 0
  h144 : z 1 * c (hankelIndex 4 4) + z 4 * c (hankelIndex 1 4) = 0
  h233 : z 2 * c (hankelIndex 3 3) + z 3 * c (hankelIndex 2 3) = 0
  h234 : z 2 * c (hankelIndex 3 4) + z 3 * c (hankelIndex 2 4) = 0
  h244 : z 2 * c (hankelIndex 4 4) + z 4 * c (hankelIndex 2 4) = 0
  h343 : z 3 * c (hankelIndex 4 3) + z 4 * c (hankelIndex 3 3) = 0
  h344 : z 3 * c (hankelIndex 4 4) + z 4 * c (hankelIndex 3 4) = 0

private theorem exists_eq_one_of_ne_zero_five (z : Fin 5 → F₂)
    (hz : z ≠ 0) : ∃ i, z i = 1 := by
  by_contra h
  push_neg at h
  apply hz
  funext i
  exact (f2_eq_zero_or_one (z i)).resolve_right (h i)

/-- A nonzero exterior factor forces the middle Hankel tail to be constant.
The proof is a polynomial pivot in the five possible nonzero coordinates;
no values of `z` or `c` are enumerated. -/
private theorem rationalZeroHankelBlock_tail_three
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (hU : c 2 + c 3 + c 5 + c 6 = 0)
    (hz : z ≠ 0) :
    c 3 = c 2 := by
  rcases exists_eq_one_of_ne_zero_five z hz with ⟨p, hp⟩
  have hp0 : z p + 1 = 0 := by rw [hp]; decide
  fin_cases p
  · have h3 : c 3 = c 2 := by
      linear_combination
        (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
          simp [N3Certificate.pow_two_f2,
            N3Certificate.two_eq_zero_f2]))
        (z 1 * z 2) * h.h012 + (z 0 * z 2) * h.h013 +
          z 0 * h.h014 + z 1 * h.h022 + z 0 * h.h024 +
          z 0 * hU + c 2 * hp0 + c 3 * hp0
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    exact h3
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      z 1 * h.h012 + h.h013 + z 0 * h.h013 +
        c 2 * hp0 + c 3 * hp0
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      h.h013 + z 1 * h.h013 + z 0 * h.h014 + h.h022 + h.h023 +
        c 2 * hp0 + c 3 * hp0
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      (z 1 * z 2) * h.h012 + (z 0 * z 2) * h.h013 +
        z 0 * h.h014 + z 1 * h.h022 + z 0 * h.h024 +
        h.h032 + h.h033 + c 2 * hp0 + c 3 * hp0
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      (z 1 * z 2) * h.h012 + (z 1 * z 3) * h.h012 +
        (z 0 * z 2) * h.h013 + (z 0 * z 3) * h.h013 +
        h.h014 + z 0 * h.h014 + z 1 * h.h014 + z 1 * h.h022 +
        z 0 * h.h024 + z 1 * h.h032 + z 0 * h.h034 +
        h.h042 + h.h043 + c 2 * hp0 + c 3 * hp0
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]

private theorem rationalZeroHankelBlock_tail_four
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (hU : c 2 + c 3 + c 5 + c 6 = 0)
    (hz : z ≠ 0) : c 4 = c 2 := by
  rcases exists_eq_one_of_ne_zero_five z hz with ⟨p, hp⟩
  have hp0 : z p + 1 = 0 := by rw [hp]; decide
  fin_cases p
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      h.h012 + z 1 * h.h012 + (z 1 * z 2) * h.h012 +
        z 0 * h.h013 + (z 0 * z 2) * h.h013 + z 0 * h.h014 +
        z 1 * h.h022 + z 0 * h.h024 + z 0 * hU +
        c 2 * hp0 + c 4 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      z 1 * h.h012 + h.h013 + z 0 * h.h013 + z 1 * h.h013 +
        h.h014 + z 0 * h.h014 + c 2 * hp0 + c 4 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      (z 1 * z 2) * h.h012 + h.h013 + z 1 * h.h013 +
        (z 0 * z 2) * h.h013 + h.h022 + z 1 * h.h022 +
        h.h024 + z 0 * h.h024 + c 2 * hp0 + c 4 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      (z 1 * z 3) * h.h012 + (z 0 * z 3) * h.h013 +
        h.h014 + z 1 * h.h014 + h.h032 + z 1 * h.h032 +
        h.h034 + z 0 * h.h034 + c 2 * hp0 + c 4 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      (z 1 * z 4) * h.h012 + z 2 * h.h013 +
        (z 0 * z 4) * h.h013 + (z 1 * z 2) * h.h013 +
        z 2 * h.h014 + (z 0 * z 2) * h.h014 + z 0 * h.h024 +
        z 1 * h.h024 + h.h042 + z 1 * h.h042 + h.h044 +
        z 0 * h.h044 + c 2 * hp0 + c 4 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]

private theorem rationalZeroHankelBlock_tail_five
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (hU : c 2 + c 3 + c 5 + c 6 = 0)
    (hz : z ≠ 0) : c 5 = c 2 := by
  rcases exists_eq_one_of_ne_zero_five z hz with ⟨p, hp⟩
  have hp0 : z p + 1 = 0 := by rw [hp]; decide
  fin_cases p
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      h.h012 + z 1 * h.h012 + (z 1 * z 2) * h.h012 + h.h013 +
        z 0 * h.h013 + z 1 * h.h013 + (z 0 * z 2) * h.h013 +
        z 1 * h.h022 + z 0 * h.h024 + z 0 * hU +
        c 2 * hp0 + c 5 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      z 1 * h.h012 + (z 1 * z 2) * h.h012 + h.h013 +
        z 0 * h.h013 + z 1 * h.h013 + (z 0 * z 2) * h.h013 +
        z 1 * h.h022 + h.h024 + z 0 * h.h024 + h.h123 +
        c 2 * hp0 + c 5 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      (z 1 * z 2) * h.h012 + h.h013 + z 1 * h.h013 +
        (z 0 * z 2) * h.h013 + h.h022 + z 1 * h.h022 +
        h.h024 + z 0 * h.h024 + z 2 * h.h123 + h.h124 +
        z 1 * h.h124 + c 2 * hp0 + c 5 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      (z 1 * z 3) * h.h012 + (z 0 * z 3) * h.h013 + h.h014 +
        z 1 * h.h014 + z 3 * h.h022 + (z 2 * z 3) * h.h022 +
        z 3 * h.h024 + (z 0 * z 3) * h.h024 + h.h032 +
        z 1 * h.h032 + z 3 * h.h123 + h.h134 + z 1 * h.h134 +
        c 2 * hp0 + c 5 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]
  · linear_combination
      (norm := (simp [CharTwo.sub_eq_add] <;> ring_nf <;>
        simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
      (z 1 * z 4) * h.h012 + z 2 * h.h013 +
        (z 0 * z 4) * h.h013 + (z 1 * z 2) * h.h013 +
        z 2 * h.h014 + (z 0 * z 2) * h.h014 + z 4 * h.h022 +
        (z 2 * z 4) * h.h022 + z 0 * h.h024 + z 1 * h.h024 +
        z 4 * h.h024 + (z 0 * z 4) * h.h024 + h.h042 +
        z 1 * h.h042 + z 4 * h.h123 + h.h144 + z 1 * h.h144 +
        c 2 * hp0 + c 5 * hp0 <;>
      ring_nf <;> simp [N3Certificate.two_eq_zero_f2]

private theorem rationalZeroHankelBlock_tail_six
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (hU : c 2 + c 3 + c 5 + c 6 = 0)
    (hz : z ≠ 0) : c 6 = c 2 := by
  have h3 := rationalZeroHankelBlock_tail_three z c h hU hz
  have h5 := rationalZeroHankelBlock_tail_five z c h hU hz
  rw [h3, h5] at hU
  have h26 : c 2 + c 6 = 0 := by
    calc
      c 2 + c 6 = (c 2 + c 2) + (c 2 + c 6) := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = c 2 + c 2 + c 2 + c 6 := by ac_rfl
      _ = 0 := hU
  exact (CharTwo.add_eq_zero.mp h26).symm

private theorem rationalZeroHankelBlock_tail_seven
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (hU : c 2 + c 3 + c 5 + c 6 = 0)
    (hz : z ≠ 0) : c 7 = c 2 := by
  have h3 := rationalZeroHankelBlock_tail_three z c h hU hz
  have h4 := rationalZeroHankelBlock_tail_four z c h hU hz
  have h5 := rationalZeroHankelBlock_tail_five z c h hU hz
  have h6 := rationalZeroHankelBlock_tail_six z c h hU hz
  rcases f2_eq_zero_or_one (c 2) with h2 | h2
  · rcases f2_eq_zero_or_one (c 7) with h7 | h7
    · exact h7.trans h2.symm
    · have hz0 : z 0 = 0 := by simpa [h7, h4, h2] using h.h034
      have hz1 : z 1 = 0 := by simpa [h7, h5, h2] using h.h134
      have hz2 : z 2 = 0 := by simpa [h7, h6, h2] using h.h234
      have hz3 : z 3 = 0 := by simpa [h7, h6, h2] using h.h343
      have hz4 : z 4 = 0 := by simpa [h7, hz3] using h.h344
      exfalso
      apply hz
      funext i
      fin_cases i <;> assumption
  · have h01 : z 0 + z 1 = 0 := by
      simpa [h2, h3] using h.h012
    have h02 : z 0 + z 2 = 0 := by
      simpa [h2, h4] using h.h022
    have h03 : z 0 + z 3 = 0 := by
      simpa [h2, h5] using h.h032
    have h04 : z 0 + z 4 = 0 := by
      simpa [h2, h6] using h.h042
    have hz1 : z 1 = z 0 := (CharTwo.add_eq_zero.mp h01).symm
    have hz2 : z 2 = z 0 := (CharTwo.add_eq_zero.mp h02).symm
    have hz3 : z 3 = z 0 := (CharTwo.add_eq_zero.mp h03).symm
    have hz4 : z 4 = z 0 := (CharTwo.add_eq_zero.mp h04).symm
    have hz0ne : z 0 ≠ 0 := by
      intro hz0
      apply hz
      funext i
      fin_cases i <;> simp [hz0, hz1, hz2, hz3, hz4]
    have hz0 : z 0 = 1 :=
      (f2_eq_zero_or_one (z 0)).resolve_left hz0ne
    have hseven : c 7 + 1 = 0 := by
      simpa [h4, h2, hz3, hz0] using h.h034
    exact (CharTwo.add_eq_zero.mp hseven).trans h2.symm

private theorem rationalZeroHankelBlock_tail
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (hU : c 2 + c 3 + c 5 + c 6 = 0)
    (hz : z ≠ 0) :
    c 3 = c 2 ∧ c 4 = c 2 ∧ c 5 = c 2 ∧
      c 6 = c 2 ∧ c 7 = c 2 := by
  exact ⟨rationalZeroHankelBlock_tail_three z c h hU hz,
    rationalZeroHankelBlock_tail_four z c h hU hz,
    rationalZeroHankelBlock_tail_five z c h hU hz,
    rationalZeroHankelBlock_tail_six z c h hU hz,
    rationalZeroHankelBlock_tail_seven z c h hU hz⟩

private theorem rationalZeroHankelBlockEquation_a_of_cubic
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo = factorPlaneCubic x y 0 (targetTwo c))
    (i k j : Fin 5) (hik : i ≠ k)
    (hlocal : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo (aCoord i) (aCoord k) (bCoord j) = 0) :
    x (aCoord i) * c (hankelIndex k j) +
      x (aCoord k) * c (hankelIndex i j) = 0 := by
  have hc := congrFun (congrFun (congrFun hcubic
    (aCoord i)) (aCoord k)) (bCoord j)
  rw [hlocal] at hc
  simpa [factorPlaneCubic, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, ambientTwoCoeff_zero,
    ambientTwoCoeff_targetTwo_cross, ambientTwoCoeff,
    targetTwo_sameA, hik, aCoord_ne_bCoord] using hc.symm

private theorem rationalZeroHankelBlockEquation_b_of_cubic
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo = factorPlaneCubic x y 0 (targetTwo c))
    (i k j : Fin 5) (hik : i ≠ k)
    (hlocal : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo (aCoord j) (bCoord i) (bCoord k) = 0) :
    x (bCoord i) * c (hankelIndex k j) +
      x (bCoord k) * c (hankelIndex i j) = 0 := by
  have hc := congrFun (congrFun (congrFun hcubic
    (aCoord j)) (bCoord i)) (bCoord k)
  rw [hlocal] at hc
  simpa [factorPlaneCubic, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, ambientTwoCoeff_zero,
    ambientTwoCoeff_targetTwo_cross, ambientTwoCoeff,
    targetTwo_sameB, hik, aCoord_ne_bCoord,
    mul_comm, add_comm] using hc.symm

private theorem rationalZeroHankelBlockRelations_a_of_cubic
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo = factorPlaneCubic x y 0 (targetTwo c)) :
    RationalZeroHankelBlockRelations (fun i => x (aCoord i)) c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply rationalZeroHankelBlockEquation_a_of_cubic
      ell m x y c hcubic
    · decide
    · simp [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, rationalZeroValueTwo,
        rationalZeroJetTwo, targetPairTwo,
        ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
        aLinear, bLinear, Pi.basisFun,
        aCoord_ne_bCoord, bCoord_ne_aCoord]

private theorem rationalZeroHankelBlockRelations_b_of_cubic
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo = factorPlaneCubic x y 0 (targetTwo c)) :
    RationalZeroHankelBlockRelations (fun i => x (bCoord i)) c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply rationalZeroHankelBlockEquation_b_of_cubic
      ell m x y c hcubic
    · decide
    · simp [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, rationalZeroValueTwo,
        rationalZeroJetTwo, targetPairTwo,
        ambientTwoCoeff_add, ambientTwoCoeff_squarefreeWedge,
        aLinear, bLinear, Pi.basisFun,
        aCoord_ne_bCoord, bCoord_ne_aCoord]

private theorem linearForm_eq_zero_of_halves_eq_zero
    (x : LinearForm)
    (hA : (fun i : Fin 5 => x (aCoord i)) = 0)
    (hB : (fun i : Fin 5 => x (bCoord i)) = 0) : x = 0 := by
  funext i
  fin_cases i
  all_goals first
    | simpa [aCoord] using congrFun hA 0
    | simpa [aCoord] using congrFun hA 1
    | simpa [aCoord] using congrFun hA 2
    | simpa [aCoord] using congrFun hA 3
    | simpa [aCoord] using congrFun hA 4
    | simpa [bCoord] using congrFun hB 0
    | simpa [bCoord] using congrFun hB 1
    | simpa [bCoord] using congrFun hB 2
    | simpa [bCoord] using congrFun hB 3
    | simpa [bCoord] using congrFun hB 4

private theorem rationalZeroHankelBlock_constant_of_two_eq_one
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (h2 : c 2 = 1) (h3 : c 3 = c 2) (h4 : c 4 = c 2)
    (h5 : c 5 = c 2) (h6 : c 6 = c 2) :
    z 1 = z 0 ∧ z 2 = z 0 ∧ z 3 = z 0 ∧ z 4 = z 0 := by
  have h01 : z 0 + z 1 = 0 := by simpa [h2, h3] using h.h012
  have h02 : z 0 + z 2 = 0 := by simpa [h2, h4] using h.h022
  have h03 : z 0 + z 3 = 0 := by simpa [h2, h5] using h.h032
  have h04 : z 0 + z 4 = 0 := by simpa [h2, h6] using h.h042
  exact ⟨(CharTwo.add_eq_zero.mp h01).symm,
    (CharTwo.add_eq_zero.mp h02).symm,
    (CharTwo.add_eq_zero.mp h03).symm,
    (CharTwo.add_eq_zero.mp h04).symm⟩

private theorem rationalZeroHankelBlock_eight_eq_one
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (h2 : c 2 = 1) (h3 : c 3 = c 2) (h4 : c 4 = c 2)
    (h5 : c 5 = c 2) (h6 : c 6 = c 2) (hz : z ≠ 0) :
    c 8 = 1 := by
  rcases rationalZeroHankelBlock_constant_of_two_eq_one
      z c h h2 h3 h4 h5 h6 with ⟨hz1, hz2, hz3, hz4⟩
  have hz0ne : z 0 ≠ 0 := by
    intro hz0
    apply hz
    funext i
    fin_cases i <;> simp [hz0, hz1, hz2, hz3, hz4]
  have hz0 : z 0 = 1 := (f2_eq_zero_or_one (z 0)).resolve_left hz0ne
  have h8 : c 8 + 1 = 0 := by
    simpa [h2, h4, hz0, hz4] using h.h044
  exact CharTwo.add_eq_zero.mp h8

private theorem rationalZeroHankelBlock_infinity_support
    (z : Fin 5 → F₂) (c : TargetCoeff)
    (h : RationalZeroHankelBlockRelations z c)
    (h2 : c 2 = 0) (h8 : c 8 = 1)
    (h4 : c 4 = c 2) (h5 : c 5 = c 2)
    (h6 : c 6 = c 2) (h7 : c 7 = c 2) :
    z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 := by
  exact ⟨by simpa [h2, h8, h4] using h.h044,
    by simpa [h2, h8, h5] using h.h144,
    by simpa [h2, h8, h6] using h.h244,
    by simpa [h2, h8, h7] using h.h344⟩

private theorem ambientVectorWedgeTwo_factorSpan
    (u v : LinearForm) (a b : F₂) :
    ambientVectorWedgeTwo (a • u + b • v) (squarefreeWedge u v) = 0 := by
  funext i j k
  simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff_squarefreeWedge]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

private theorem ambientVectorWedgeTwo_zero_right (x : LinearForm) :
    ambientVectorWedgeTwo x 0 = 0 := by
  funext i j k
  simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]

private theorem rationalZero_targetCoeff_decomposition
    (c : TargetCoeff)
    (h3 : c 3 = c 2) (h4 : c 4 = c 2) (h5 : c 5 = c 2)
    (h6 : c 6 = c 2) (h7 : c 7 = c 2) :
    c = (c 0 + c 2) • rZeroCoeff +
        (c 1 + c 2) • jZeroCoeff + c 2 • rOneCoeff +
          (c 8 + c 2) • rInfinityCoeff := by
  funext s
  fin_cases s <;>
    simp [rZeroCoeff, jZeroCoeff, rOneCoeff, rInfinityCoeff,
      h3, h4, h5, h6, h7, N3Certificate.two_eq_zero_f2]
  all_goals
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero,
      add_zero, zero_add]
  case «8» => rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem targetTwo_rationalZero_decomposition
    (c : TargetCoeff)
    (hcoeff : c = (c 0 + c 2) • rZeroCoeff +
      (c 1 + c 2) • jZeroCoeff + c 2 • rOneCoeff +
        (c 8 + c 2) • rInfinityCoeff) :
    targetTwo c = (c 0 + c 2) • rationalZeroValueTwo +
      (c 1 + c 2) • rationalZeroJetTwo +
        (c 2 • targetTwo rOneCoeff +
          (c 8 + c 2) • targetTwo rInfinityCoeff) := by
  calc
    targetTwo c = targetTwo ((c 0 + c 2) • rZeroCoeff +
        (c 1 + c 2) • jZeroCoeff + c 2 • rOneCoeff +
          (c 8 + c 2) • rInfinityCoeff) := congrArg targetTwo hcoeff
    _ = (c 0 + c 2) • rationalZeroValueTwo +
        (c 1 + c 2) • rationalZeroJetTwo +
          (c 2 • targetTwo rOneCoeff +
            (c 8 + c 2) • targetTwo rInfinityCoeff) := by
      rw [rationalZeroValueTwo_eq_target, rationalZeroJetTwo_eq_target]
      change targetTwoLinear _ = _
      simp only [map_add, map_smul]
      rw [add_assoc]
      rfl

private theorem linearForm_eq_infinitySpan
    (x : LinearForm)
    (hA0 : x (aCoord 0) = 0) (hA1 : x (aCoord 1) = 0)
    (hA2 : x (aCoord 2) = 0) (hA3 : x (aCoord 3) = 0)
    (hB0 : x (bCoord 0) = 0) (hB1 : x (bCoord 1) = 0)
    (hB2 : x (bCoord 2) = 0) (hB3 : x (bCoord 3) = 0) :
    x = x (aCoord 4) • aLinear 4 + x (bCoord 4) • bLinear 4 := by
  funext i
  fin_cases i <;>
    simp [aLinear, bLinear, Pi.basisFun, aCoord, bCoord]
  all_goals first
    | simpa [aCoord] using hA0
    | simpa [aCoord] using hA1
    | simpa [aCoord] using hA2
    | simpa [aCoord] using hA3
    | simpa [bCoord] using hB0
    | simpa [bCoord] using hB1
    | simpa [bCoord] using hB2
    | simpa [bCoord] using hB3

private theorem linearForm_eq_oneSpan
    (x : LinearForm)
    (hA1 : x (aCoord 1) = x (aCoord 0))
    (hA2 : x (aCoord 2) = x (aCoord 0))
    (hA3 : x (aCoord 3) = x (aCoord 0))
    (hA4 : x (aCoord 4) = x (aCoord 0))
    (hB1 : x (bCoord 1) = x (bCoord 0))
    (hB2 : x (bCoord 2) = x (bCoord 0))
    (hB3 : x (bCoord 3) = x (bCoord 0))
    (hB4 : x (bCoord 4) = x (bCoord 0)) :
    x = x (aCoord 0) • (∑ i : Fin 5, aLinear i) +
      x (bCoord 0) • (∑ i : Fin 5, bLinear i) := by
  funext i
  fin_cases i <;>
    simp [aLinear, bLinear, Pi.basisFun, aCoord, bCoord,
      Fin.sum_univ_succ, hA1, hA2, hA3, hA4,
      hB1, hB2, hB3, hB4]
  all_goals first
    | simpa [aCoord] using hA1
    | simpa [aCoord] using hA2
    | simpa [aCoord] using hA3
    | simpa [aCoord] using hA4
    | simpa [bCoord] using hB1
    | simpa [bCoord] using hB2
    | simpa [bCoord] using hB3
    | simpa [bCoord] using hB4

/-- A nonzero cubic syzygy for a plane containing the rational value at zero
forces the companion into one of the three exceptional directions through
that value.  The proof reuses the Hankel tail pivot above and adds only the
three boundary coordinates omitted by the local/dependent calculation. -/
theorem rationalZero_nonregular_companion_classification
    (x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hind : LinearIndependent F₂
      (quadraticPlaneDirections rationalZeroValueTwo (targetTwo c)))
    (hx : x ≠ 0)
    (hcubic : factorPlaneCubic x y rationalZeroValueTwo (targetTwo c) = 0) :
    (∃ α : F₂, c = α • rZeroCoeff + jZeroCoeff) ∨
      (∃ α : F₂, c = α • rZeroCoeff + rOneCoeff) ∨
        ∃ α : F₂, c = α • rZeroCoeff + rInfinityCoeff := by
  have hlocalDependent :
      factorPlaneCubic 0 y rationalZeroValueTwo rationalZeroJetTwo =
        factorPlaneCubic x 0 0 (targetTwo c) := by
    funext i j k
    have h := congrFun (congrFun (congrFun hcubic i) j) k
    simp only [factorPlaneCubic, ambientVectorWedgeTwo,
      N4.vectorWedgeTwoN, Pi.add_apply] at h ⊢
    simpa [ambientTwoCoeff_zero, add_comm] using
      (CharTwo.add_eq_zero.mp h).symm
  have hU : c 2 + c 3 + c 5 + c 6 = 0 :=
    (mem_firstOrderEnvelopeCoeffSpace c).1 hc
  let zA : Fin 5 → F₂ := fun i => x (aCoord i)
  let zB : Fin 5 → F₂ := fun i => x (bCoord i)
  have hA : RationalZeroHankelBlockRelations zA c :=
    rationalZeroHankelBlockRelations_a_of_cubic
      0 y x 0 c hlocalDependent
  have hB : RationalZeroHankelBlockRelations zB c :=
    rationalZeroHankelBlockRelations_b_of_cubic
      0 y x 0 c hlocalDependent
  have hnonzero : zA ≠ 0 ∨ zB ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (linearForm_eq_zero_of_halves_eq_zero x h.1 h.2)
  have htail : c 3 = c 2 ∧ c 4 = c 2 ∧ c 5 = c 2 ∧
      c 6 = c 2 ∧ c 7 = c 2 := by
    rcases hnonzero with hAz | hBz
    · exact rationalZeroHankelBlock_tail zA c hA hU hAz
    · exact rationalZeroHankelBlock_tail zB c hB hU hBz
  rcases htail with ⟨h3, h4, h5, h6, h7⟩
  rcases f2_eq_zero_or_one (c 2) with h2 | h2
  · rcases f2_eq_zero_or_one (c 8) with h8 | h8
    · have h1 : c 1 = 1 := by
        rcases f2_eq_zero_or_one (c 1) with h1 | h1
        · have hcform : c = c 0 • rZeroCoeff := by
            funext s
            fin_cases s <;>
              simp [rZeroCoeff, h1, h2, h3, h4, h5, h6, h7, h8]
          have htarget : targetTwo c = c 0 • rationalZeroValueTwo := by
            calc
              targetTwo c = targetTwo (c 0 • rZeroCoeff) :=
                congrArg targetTwo hcform
              _ = c 0 • targetTwo rZeroCoeff := by
                change targetTwoLinear (c 0 • rZeroCoeff) = _
                rw [map_smul]
                simp only [targetTwo]
              _ = c 0 • rationalZeroValueTwo := by
                rw [rationalZeroValueTwo_eq_target]
          rcases quadraticPlaneDirections_independent_nonzero_ne
              rationalZeroValueTwo (targetTwo c) hind with
            ⟨_, hcne, hne⟩
          rcases f2_eq_zero_or_one (c 0) with h0 | h0
          · exact (hcne (by simp [htarget, h0])).elim
          · exact (hne (by simp [htarget, h0])).elim
        · exact h1
      left
      refine ⟨c 0, ?_⟩
      funext s
      fin_cases s <;>
        simp [rZeroCoeff, jZeroCoeff, h1, h2, h3, h4, h5, h6, h7, h8]
    · have hAsupport := rationalZeroHankelBlock_infinity_support
          zA c hA h2 h8 h4 h5 h6 h7
      have hBsupport := rationalZeroHankelBlock_infinity_support
          zB c hB h2 h8 h4 h5 h6 h7
      rcases hAsupport with ⟨hA0, hA1, hA2, hA3⟩
      rcases hBsupport with ⟨hB0, hB1, hB2, hB3⟩
      have h1 : c 1 = 0 := by
        by_cases hA4 : x (aCoord 4) = 0
        · have hB4 : x (bCoord 4) ≠ 0 := by
            intro hB4
            apply hx
            apply linearForm_eq_zero_of_halves_eq_zero
            · funext i
              fin_cases i <;> simp_all [zA]
            · funext i
              fin_cases i <;> simp_all [zB]
          have hB4one : x (bCoord 4) = 1 :=
            (f2_eq_zero_or_one _).resolve_left hB4
          have hcoord := congrFun (congrFun (congrFun hcubic
            (aCoord 1)) (bCoord 0)) (bCoord 4)
          simpa [factorPlaneCubic, ambientVectorWedgeTwo,
            N4.vectorWedgeTwoN, ambientTwoCoeff_targetTwo_cross,
            ambientTwoCoeff, targetTwo_sameB, aCoord_ne_bCoord,
            bCoord_ne_aCoord, rationalZeroValueTwo, targetPairTwo,
            aLinear, bLinear, Pi.basisFun, h2, h5, hB4one,
            show x (bCoord 0) = 0 by simpa [zB] using hB0] using hcoord
        · have hA4one : x (aCoord 4) = 1 :=
            (f2_eq_zero_or_one _).resolve_left hA4
          have hcoord := congrFun (congrFun (congrFun hcubic
            (aCoord 0)) (aCoord 4)) (bCoord 1)
          simpa [factorPlaneCubic, ambientVectorWedgeTwo,
            N4.vectorWedgeTwoN, ambientTwoCoeff_targetTwo_cross,
            ambientTwoCoeff, targetTwo_sameA, aCoord_ne_bCoord,
            bCoord_ne_aCoord, rationalZeroValueTwo, targetPairTwo,
            aLinear, bLinear, Pi.basisFun, h2, h5, hA4one,
            show x (aCoord 0) = 0 by simpa [zA] using hA0] using hcoord
      right; right
      refine ⟨c 0, ?_⟩
      funext s
      fin_cases s <;>
        simp [rZeroCoeff, rInfinityCoeff, h1, h2, h3, h4, h5, h6, h7, h8]
  · have h8 : c 8 = 1 := by
      rcases hnonzero with hAz | hBz
      · exact rationalZeroHankelBlock_eight_eq_one
          zA c hA h2 h3 h4 h5 h6 hAz
      · exact rationalZeroHankelBlock_eight_eq_one
          zB c hB h2 h3 h4 h5 h6 hBz
    rcases rationalZeroHankelBlock_constant_of_two_eq_one
        zA c hA h2 h3 h4 h5 h6 with ⟨hA1, hA2, hA3, hA4⟩
    rcases rationalZeroHankelBlock_constant_of_two_eq_one
        zB c hB h2 h3 h4 h5 h6 with ⟨hB1, hB2, hB3, hB4⟩
    have h1 : c 1 = 1 := by
      by_cases hA0 : x (aCoord 0) = 0
      · have hB0 : x (bCoord 0) ≠ 0 := by
          intro hB0
          apply hx
          apply linearForm_eq_zero_of_halves_eq_zero
          · funext i
            fin_cases i <;> simp [zA, hA0, hA1, hA2, hA3, hA4]
          · funext i
            fin_cases i <;> simp [zB, hB0, hB1, hB2, hB3, hB4]
        have hB0one : x (bCoord 0) = 1 :=
          (f2_eq_zero_or_one _).resolve_left hB0
        have hcoord := congrFun (congrFun (congrFun hcubic
          (aCoord 0)) (bCoord 1)) (bCoord 2)
        have hB1one : x (bCoord 1) = 1 := by simpa [zB, hB0one] using hB1
        have hB2one : x (bCoord 2) = 1 := by simpa [zB, hB0one] using hB2
        have hsum : 1 + c 1 = 0 := by
          simpa [factorPlaneCubic, ambientVectorWedgeTwo,
            N4.vectorWedgeTwoN, ambientTwoCoeff_targetTwo_cross,
            ambientTwoCoeff, targetTwo_sameB, aCoord_ne_bCoord,
            bCoord_ne_aCoord, rationalZeroValueTwo, targetPairTwo,
            aLinear, bLinear, Pi.basisFun, h2, hB1one, hB2one] using hcoord
        exact (CharTwo.add_eq_zero.mp hsum).symm
      · have hA0one : x (aCoord 0) = 1 :=
          (f2_eq_zero_or_one _).resolve_left hA0
        have hcoord := congrFun (congrFun (congrFun hcubic
          (aCoord 1)) (aCoord 2)) (bCoord 0)
        have hA1one : x (aCoord 1) = 1 := by simpa [zA, hA0one] using hA1
        have hA2one : x (aCoord 2) = 1 := by simpa [zA, hA0one] using hA2
        have hsum : 1 + c 1 = 0 := by
          simpa [factorPlaneCubic, ambientVectorWedgeTwo,
            N4.vectorWedgeTwoN, ambientTwoCoeff_targetTwo_cross,
            ambientTwoCoeff, targetTwo_sameA, aCoord_ne_bCoord,
            bCoord_ne_aCoord, rationalZeroValueTwo, targetPairTwo,
            aLinear, bLinear, Pi.basisFun, h2, hA1one, hA2one] using hcoord
        exact (CharTwo.add_eq_zero.mp hsum).symm
    right; left
    refine ⟨c 0 + 1, ?_⟩
    funext s
    fin_cases s <;>
      simp [rZeroCoeff, rOneCoeff, h1, h2, h3, h4, h5, h6, h7, h8,
        add_assoc, CharTwo.add_self_eq_zero]

/-- Structural classification for the local-versus-dependent cubic
equation.  A nonzero dependent factor leaves only the value direction at
one or infinity after the zero-place value and jet have been removed. -/
theorem rationalZero_local_dependent_structure
    (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
        rationalZeroJetTwo = factorPlaneCubic x y 0 (targetTwo c)) :
    ∃ α β : F₂, ∃ remote : TwoForm,
      remote ∈ firstOrderEnvelopeTwoSpace ∧
      targetTwo c = α • rationalZeroValueTwo +
        β • rationalZeroJetTwo + remote ∧
      ambientVectorWedgeTwo x remote = 0 := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, 0, targetTwo c, ⟨c, hc, rfl⟩, ?_, ?_⟩
    · simp
    · funext i j k
      simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]
  · have hU : c 2 + c 3 + c 5 + c 6 = 0 := by
      have hmissing := (mem_firstOrderEnvelopeCoeffSpace c).1 hc
      exact hmissing
    let zA : Fin 5 → F₂ := fun i => x (aCoord i)
    let zB : Fin 5 → F₂ := fun i => x (bCoord i)
    have hA : RationalZeroHankelBlockRelations zA c := by
      exact rationalZeroHankelBlockRelations_a_of_cubic ell m x y c hcubic
    have hB : RationalZeroHankelBlockRelations zB c := by
      exact rationalZeroHankelBlockRelations_b_of_cubic ell m x y c hcubic
    have hnonzero : zA ≠ 0 ∨ zB ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (linearForm_eq_zero_of_halves_eq_zero x h.1 h.2)
    have htail : c 3 = c 2 ∧ c 4 = c 2 ∧ c 5 = c 2 ∧
        c 6 = c 2 ∧ c 7 = c 2 := by
      rcases hnonzero with hAz | hBz
      · exact rationalZeroHankelBlock_tail zA c hA hU hAz
      · exact rationalZeroHankelBlock_tail zB c hB hU hBz
    rcases htail with ⟨h3, h4, h5, h6, h7⟩
    let remote : TwoForm :=
      c 2 • targetTwo rOneCoeff +
        (c 8 + c 2) • targetTwo rInfinityCoeff
    have hremote : remote ∈ firstOrderEnvelopeTwoSpace := by
      exact firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.smul_mem _
          (targetTwo_exactFirstOrderDirection_mem 1))
        (firstOrderEnvelopeTwoSpace.smul_mem _
          (targetTwo_exactFirstOrderDirection_mem 2))
    have hcoeff : c = (c 0 + c 2) • rZeroCoeff +
        (c 1 + c 2) • jZeroCoeff + c 2 • rOneCoeff +
          (c 8 + c 2) • rInfinityCoeff :=
      rationalZero_targetCoeff_decomposition c h3 h4 h5 h6 h7
    have hd : targetTwo c = (c 0 + c 2) • rationalZeroValueTwo +
        (c 1 + c 2) • rationalZeroJetTwo + remote := by
      exact targetTwo_rationalZero_decomposition c hcoeff
    refine ⟨c 0 + c 2, c 1 + c 2, remote, hremote, hd, ?_⟩
    rcases f2_eq_zero_or_one (c 2) with h2 | h2
    · rcases f2_eq_zero_or_one (c 8) with h8 | h8
      · simpa [remote, h2, h8] using ambientVectorWedgeTwo_zero_right x
      · rcases rationalZeroHankelBlock_infinity_support
            zA c hA h2 h8 h4 h5 h6 h7 with ⟨hA0, hA1, hA2, hA3⟩
        rcases rationalZeroHankelBlock_infinity_support
            zB c hB h2 h8 h4 h5 h6 h7 with ⟨hB0, hB1, hB2, hB3⟩
        have hxshape : x = x (aCoord 4) • aLinear 4 +
            x (bCoord 4) • bLinear 4 := by
          exact linearForm_eq_infinitySpan x
            (by simpa [zA] using hA0) (by simpa [zA] using hA1)
            (by simpa [zA] using hA2) (by simpa [zA] using hA3)
            (by simpa [zB] using hB0) (by simpa [zB] using hB1)
            (by simpa [zB] using hB2) (by simpa [zB] using hB3)
        have hremoteEq : remote = squarefreeWedge (aLinear 4) (bLinear 4) := by
          calc
            remote = targetTwo rInfinityCoeff := by simp [remote, h2, h8]
            _ = targetPairTwo 4 4 := targetTwo_rInfinity
            _ = squarefreeWedge (aLinear 4) (bLinear 4) := rfl
        rw [hxshape, hremoteEq]
        exact ambientVectorWedgeTwo_factorSpan (aLinear 4) (bLinear 4)
          (x (aCoord 4)) (x (bCoord 4))
    · have h8 : c 8 = 1 := by
        rcases hnonzero with hAz | hBz
        · exact rationalZeroHankelBlock_eight_eq_one
            zA c hA h2 h3 h4 h5 h6 hAz
        · exact rationalZeroHankelBlock_eight_eq_one
            zB c hB h2 h3 h4 h5 h6 hBz
      rcases rationalZeroHankelBlock_constant_of_two_eq_one
          zA c hA h2 h3 h4 h5 h6 with ⟨hA1, hA2, hA3, hA4⟩
      rcases rationalZeroHankelBlock_constant_of_two_eq_one
          zB c hB h2 h3 h4 h5 h6 with ⟨hB1, hB2, hB3, hB4⟩
      have hxshape : x = x (aCoord 0) • (∑ i : Fin 5, aLinear i) +
          x (bCoord 0) • (∑ i : Fin 5, bLinear i) := by
        exact linearForm_eq_oneSpan x
          (by simpa [zA] using hA1) (by simpa [zA] using hA2)
          (by simpa [zA] using hA3) (by simpa [zA] using hA4)
          (by simpa [zB] using hB1) (by simpa [zB] using hB2)
          (by simpa [zB] using hB3) (by simpa [zB] using hB4)
      have hremoteEq : remote =
          squarefreeWedge (∑ i : Fin 5, aLinear i)
            (∑ i : Fin 5, bLinear i) := by
        calc
          remote = targetTwo rOneCoeff := by
            simp [remote, h2, h8, N3Certificate.two_eq_zero_f2]
          _ = squarefreeWedge (∑ i : Fin 5, aLinear i)
              (∑ i : Fin 5, bLinear i) := targetTwo_rOne
      rw [hxshape, hremoteEq]
      exact ambientVectorWedgeTwo_factorSpan
        (∑ i : Fin 5, aLinear i) (∑ i : Fin 5, bLinear i)
          (x (aCoord 0)) (x (bCoord 0))
/-- Algebraic local/dependent shadow decomposition at the rational-zero
two-jet.  The structural input is exactly what remains after stripping the
two local target coefficients from `d`: the residual `remote` direction is
annihilated by the dependent product's linear factor.

The conclusion is deliberately in the form consumed by
`firstOrderEnvelope_add_two_decomposable_ne_missingCoset`. -/
theorem rationalZero_local_dependent_shadow_decomposition
    (a b a' b' α β : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = α • rationalZeroValueTwo +
      β • rationalZeroJetTwo + remote)
    (hcubic :
      factorPlaneCubic ell m rationalZeroValueTwo rationalZeroJetTwo =
        factorPlaneCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ u v s t : LinearForm,
      lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' x y 0 d =
      r + squarefreeWedge u v + squarefreeWedge s t := by
  have hvalue := rationalZeroValueTwo_mem_firstOrderEnvelope
  have hjet := rationalZeroJetTwo_mem_firstOrderEnvelope
  have hdmem : d ∈ firstOrderEnvelopeTwoSpace := by
    rw [hd]
    exact firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue)
        (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)) hremote
  by_cases hx : x = 0
  · subst x
    have hcubicZero :
        factorPlaneCubic ell m rationalZeroValueTwo
          rationalZeroJetTwo = 0 := by
      rw [factorPlaneCubic_zero_left] at hcubic
      have hzero : ambientVectorWedgeTwo 0 d = 0 := by
        funext i j k
        simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]
      exact hcubic.trans hzero
    rcases rationalZero_booleanCorrection_decomposition ell m hcubicZero with
      ⟨r₀, hr₀, z, hcorrection⟩
    let r : TwoForm :=
      a • rationalZeroJetTwo + b • rationalZeroValueTwo + a' • d + r₀
    refine ⟨r, ?_, ell, z, 0, 0, ?_⟩
    · exact firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.add_mem
          (firstOrderEnvelopeTwoSpace.add_mem
            (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)
            (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue))
          (firstOrderEnvelopeTwoSpace.smul_mem _ hdmem)) hr₀
    · rw [show squarefreeWedge (0 : LinearForm) 0 = 0 by simp, add_zero]
      funext q
      rcases QuadraticIndex.exists_pair q with ⟨i, j, hij, rfl⟩
      have hcorr := congrFun hcorrection (quadraticPair i j hij)
      have hhad := congrFun ambientTwoHadamard_rationalZeroValue_jet
        (quadraticPair i j hij)
      simp only [Pi.add_apply, lowProductQuadraticShadow_pair,
        Pi.zero_apply,
        mul_zero, add_zero, zero_mul, zero_add] at hcorr ⊢
      simp only [ambientTwoHadamard, Pi.zero_apply] at hhad
      change _ =
        (a • rationalZeroJetTwo + b • rationalZeroValueTwo + a' • d + r₀)
            (quadraticPair i j hij) + _ at ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair, ambientBooleanContraction_pair] at hcorr ⊢
      linear_combination hcorr + hhad
  · let X : LinearForm := ell + β • x
    let Y : LinearForm := m + α • x
    have hcubicZero :
        factorPlaneCubic X Y rationalZeroValueTwo
          rationalZeroJetTwo = 0 := by
      funext i j k
      have hc := congrFun (congrFun (congrFun hcubic i) j) k
      have hr := congrFun (congrFun (congrFun hxremote i) j) k
      simp only [factorPlaneCubic, ambientVectorWedgeTwo,
        N4.vectorWedgeTwoN, ambientTwoCoeff_add, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, ambientTwoCoeff_zero] at hc hr ⊢
      simp only [X, Y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hd] at hc
      simp only [ambientTwoCoeff_add, ambientTwoCoeff_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
      linear_combination
        (norm := (ring_nf; simp [N3Certificate.two_eq_zero_f2]))
        hc + hr
    rcases rationalZero_booleanCorrection_decomposition X Y hcubicZero with
      ⟨r₀, hr₀, z, hcorrection⟩
    rcases ambientBooleanContraction_of_vectorWedge_zero
        x remote hx hxremote with ⟨w, _hremoteWedge, hremoteContraction⟩
    let r : TwoForm :=
      a • rationalZeroJetTwo + b • rationalZeroValueTwo + a' • d +
        remote + r₀
    let t : LinearForm :=
      α • ell + β • m + y + ambientDiagonalProduct x w
    refine ⟨r, ?_, X, z, x, t, ?_⟩
    · exact firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.add_mem
          (firstOrderEnvelopeTwoSpace.add_mem
            (firstOrderEnvelopeTwoSpace.add_mem
              (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)
              (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue))
            (firstOrderEnvelopeTwoSpace.smul_mem _ hdmem)) hremote) hr₀
    · funext q
      rcases QuadraticIndex.exists_pair q with ⟨i, j, hij, rfl⟩
      have hcorr := congrFun hcorrection (quadraticPair i j hij)
      have hcontract := congrFun hremoteContraction
        (quadraticPair i j hij)
      have hhad := congrFun ambientTwoHadamard_rationalZeroValue_jet
        (quadraticPair i j hij)
      simp only [Pi.add_apply, lowProductQuadraticShadow_pair,
        Pi.zero_apply,
        mul_zero, add_zero, zero_mul, zero_add] at hcorr ⊢
      simp only [ambientBooleanContraction_pair, Pi.add_apply] at hcontract
      simp only [ambientTwoHadamard, Pi.zero_apply] at hhad
      dsimp only [r]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair, ambientBooleanContraction_pair] at hcorr ⊢
      simp only [X, Y, t, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        squarefreeWedge_pair] at hcorr ⊢
      rw [hd]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination
        (norm := (ring_nf; simp [N3Certificate.pow_two_f2,
          N3Certificate.two_eq_zero_f2]))
        hcorr + hcontract + hhad

/-- Missing-coset exclusion corresponding to the preceding decomposition. -/
theorem rationalZero_local_dependent_shadow_not_missingCoset
    (a b a' b' α β : F₂)
    (ell m x y : LinearForm) (d remote : TwoForm)
    (hremote : remote ∈ firstOrderEnvelopeTwoSpace)
    (hd : d = α • rationalZeroValueTwo +
      β • rationalZeroJetTwo + remote)
    (hcubic :
      factorPlaneCubic ell m rationalZeroValueTwo rationalZeroJetTwo =
        factorPlaneCubic x y 0 d)
    (hxremote : ambientVectorWedgeTwo x remote = 0)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' x y 0 d ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  rcases rationalZero_local_dependent_shadow_decomposition
      a b a' b' α β ell m x y d remote hremote hd hcubic hxremote with
    ⟨r, hr, p, q, s, t, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q s t u hu
  exact hdecomp.symm.trans hmissing

/-- The rational-zero local/dependent branch with all structural hypotheses
discharged from the cubic equation and first-order-envelope membership. -/
theorem rationalZero_actual_local_dependent_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m x y : LinearForm) (c : TargetCoeff)
    (hc : c ∈ firstOrderEnvelopeCoeffSpace)
    (hcubic : factorPlaneCubic ell m rationalZeroValueTwo
      rationalZeroJetTwo = factorPlaneCubic x y 0 (targetTwo c))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m rationalZeroValueTwo
          rationalZeroJetTwo +
        lowProductQuadraticShadow a' b' x y 0 (targetTwo c) ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases rationalZero_local_dependent_structure ell m x y c hc hcubic with
    ⟨α, β, remote, hremote, hd, hxremote⟩
  exact rationalZero_local_dependent_shadow_not_missingCoset
    a b a' b' α β ell m x y (targetTwo c) remote
      hremote hd hcubic hxremote u hu

end

end N5
end UnrestrictedBooleanMul
