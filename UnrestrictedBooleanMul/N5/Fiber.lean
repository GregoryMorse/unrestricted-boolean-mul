import UnrestrictedBooleanMul.N5.QuadraticSpace
import UnrestrictedBooleanMul.N4.Exterior
import UnrestrictedBooleanMul.N4.Flag

/-!
# Decomposable fibers and the target--defect ledger

The zero-fiber calculation is proved from Hankel minors.  The circuit ledger is
the generic short-exact-sequence identity already checked in the `n = 4`
development; this module provides the `n = 5` interface without duplicating
that linear algebra.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The `5 × 5` Hankel matrix attached to a target coefficient word. -/
def hankelMatrix (c : TargetCoeff) : Matrix (Fin 5) (Fin 5) F₂ :=
  fun i j => c (hankelIndex i j)

/-- Algebraic rank-at-most-one condition: every `2 × 2` minor vanishes. -/
def HankelRankLEOne (c : TargetCoeff) : Prop :=
  ∀ i k j l : Fin 5,
    hankelMatrix c i j * hankelMatrix c k l =
      hankelMatrix c i l * hankelMatrix c k j

/-- Rational place at zero. -/
def rZeroCoeff : TargetCoeff :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Rational place at one. -/
def rOneCoeff : TargetCoeff :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Rational place at infinity. -/
def rInfinityCoeff : TargetCoeff :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The rational-place target subspace. -/
def rationalCoeffSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ {rZeroCoeff, rOneCoeff, rInfinityCoeff}

@[simp] theorem rZeroCoeff_hankel (i j : Fin 5) :
    rZeroCoeff (hankelIndex i j) =
      if i = 0 ∧ j = 0 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem rOneCoeff_apply (s : Fin 9) : rOneCoeff s = 1 := by
  fin_cases s <;> rfl

@[simp] theorem rInfinityCoeff_hankel (i j : Fin 5) :
    rInfinityCoeff (hankelIndex i j) =
      if i = 4 ∧ j = 4 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem targetTwo_rZero : targetTwo rZeroCoeff = targetPairTwo 0 0 := by
  rw [targetTwo_eq_double_sum]
  classical
  simp only [rZeroCoeff_hankel, ite_smul, one_smul, zero_smul]
  rw [Fintype.sum_eq_single (0 : Fin 5)]
  · rw [Fintype.sum_eq_single (0 : Fin 5)]
    · simp
    · intro j hj
      simp [hj]
  · intro i hi
    apply Finset.sum_eq_zero
    intro j _
    simp [hi]

theorem targetTwo_rInfinity :
    targetTwo rInfinityCoeff = targetPairTwo 4 4 := by
  rw [targetTwo_eq_double_sum]
  classical
  simp only [rInfinityCoeff_hankel, ite_smul, one_smul, zero_smul]
  rw [Fintype.sum_eq_single (4 : Fin 5)]
  · rw [Fintype.sum_eq_single (4 : Fin 5)]
    · simp
    · intro j hj
      simp [hj]
  · intro i hi
    apply Finset.sum_eq_zero
    intro j _
    simp [hi]

theorem targetTwo_rOne :
    targetTwo rOneCoeff =
      squarefreeWedge (∑ i : Fin 5, aLinear i) (∑ j : Fin 5, bLinear j) := by
  rw [targetTwo_eq_double_sum]
  simp only [rOneCoeff_apply, one_smul]
  symm
  calc
    squarefreeWedge (∑ i : Fin 5, aLinear i) (∑ j : Fin 5, bLinear j) =
        ∑ i : Fin 5, squarefreeWedge (aLinear i) (∑ j : Fin 5, bLinear j) := by
      simpa using squarefreeWedge_sum_left (Finset.univ : Finset (Fin 5))
        aLinear (∑ j : Fin 5, bLinear j)
    _ = ∑ i : Fin 5, ∑ j : Fin 5,
        squarefreeWedge (aLinear i) (bLinear j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using squarefreeWedge_sum_right (aLinear i)
        (Finset.univ : Finset (Fin 5)) bLinear
    _ = ∑ i : Fin 5, ∑ j : Fin 5, targetPairTwo i j := by
      rfl

@[simp] theorem decomposable_target_rZero :
    IsDecomposableTwo (targetTwo rZeroCoeff) := by
  exact ⟨aLinear 0, bLinear 0, targetTwo_rZero⟩

@[simp] theorem decomposable_target_rOne :
    IsDecomposableTwo (targetTwo rOneCoeff) := by
  exact ⟨∑ i : Fin 5, aLinear i, ∑ j : Fin 5, bLinear j, targetTwo_rOne⟩

@[simp] theorem decomposable_target_rInfinity :
    IsDecomposableTwo (targetTwo rInfinityCoeff) := by
  exact ⟨aLinear 4, bLinear 4, targetTwo_rInfinity⟩

private theorem rankOne_minor {c : TargetCoeff} (h : HankelRankLEOne c)
    (i k j l : Fin 5) :
    c (hankelIndex i j) * c (hankelIndex k l) =
      c (hankelIndex i l) * c (hankelIndex k j) := by
  simpa [HankelRankLEOne, hankelMatrix] using h i k j l

/-- The nonzero rank-one length-nine Hankel words are precisely the three
`F₂`-rational places. -/
theorem rankOne_target_classification {c : TargetCoeff}
    (h : HankelRankLEOne c) (hc : c ≠ 0) :
    c = rZeroCoeff ∨ c = rOneCoeff ∨ c = rInfinityCoeff := by
  rcases f2_eq_zero_or_one (c 0) with hc0 | hc0
  · have hc1 : c 1 = 0 := by
      have hm := rankOne_minor h (0 : Fin 5) 1 1 0
      simpa [hankelIndex, hc0, N3Certificate.mul_self_f2] using hm
    have hc2 : c 2 = 0 := by
      have hm := rankOne_minor h (0 : Fin 5) 2 2 0
      simpa [hankelIndex, hc0, N3Certificate.mul_self_f2] using hm
    have hc3 : c 3 = 0 := by
      have hm := rankOne_minor h (0 : Fin 5) 3 3 0
      simpa [hankelIndex, hc0, N3Certificate.mul_self_f2] using hm
    have hc4 : c 4 = 0 := by
      have hm := rankOne_minor h (0 : Fin 5) 4 4 0
      simpa [hankelIndex, hc0, N3Certificate.mul_self_f2] using hm
    have hc5 : c 5 = 0 := by
      have hm := rankOne_minor h (1 : Fin 5) 4 4 1
      simpa [hankelIndex, hc2, N3Certificate.mul_self_f2] using hm
    have hc6 : c 6 = 0 := by
      have hm := rankOne_minor h (2 : Fin 5) 4 4 2
      simpa [hankelIndex, hc4, N3Certificate.mul_self_f2] using hm
    have hc7 : c 7 = 0 := by
      have hm := rankOne_minor h (3 : Fin 5) 4 4 3
      simpa [hankelIndex, hc6, N3Certificate.mul_self_f2] using hm
    have hc8 : c 8 = 1 := by
      rcases f2_eq_zero_or_one (c 8) with hc8 | hc8
      · exfalso
        apply hc
        funext i
        fin_cases i <;> assumption
      · exact hc8
    exact Or.inr (Or.inr (by
      funext i
      fin_cases i <;>
        simp [rInfinityCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]))
  · have hc2 : c 2 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 5) 1 0 1
      simpa [hankelIndex, hc0, N3Certificate.mul_self_f2] using hm
    have hc3 : c 3 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 5) 1 0 2
      simpa [hankelIndex, hc0, hc2, N3Certificate.mul_self_f2] using hm
    have hc4 : c 4 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 5) 2 0 2
      simpa [hankelIndex, hc0, hc2, N3Certificate.mul_self_f2] using hm
    have hc5 : c 5 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 5) 2 0 3
      simpa [hankelIndex, hc0, hc2, hc3, N3Certificate.mul_self_f2] using hm
    have hc6 : c 6 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 5) 3 0 3
      simpa [hankelIndex, hc0, hc3, N3Certificate.mul_self_f2] using hm
    have hc7 : c 7 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 5) 3 0 4
      simpa [hankelIndex, hc0, hc3, hc4, N3Certificate.mul_self_f2] using hm
    have hc8 : c 8 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 5) 4 0 4
      simpa [hankelIndex, hc0, hc4, N3Certificate.mul_self_f2] using hm
    rcases f2_eq_zero_or_one (c 1) with hc1 | hc1
    · exact Or.inl (by
        funext i
        fin_cases i <;>
          simp [rZeroCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8])
    · exact Or.inr (Or.inl (by
        funext i
        fin_cases i <;>
          simp [rOneCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]))

def aPart (u : LinearForm) : Fin 5 → F₂ := fun i => u (aCoord i)
def bPart (u : LinearForm) : Fin 5 → F₂ := fun j => u (bCoord j)

/-- A decomposable target word has Hankel rank at most one. -/
theorem decomposableTarget_rankOne {c : TargetCoeff}
    (hdec : IsDecomposableTwo (targetTwo c)) : HankelRankLEOne c := by
  rcases hdec with ⟨u, v, huv⟩
  have hApart : ∀ i j : Fin 5,
      aPart u i * aPart v j + aPart u j * aPart v i = 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact CharTwo.add_self_eq_zero _
    · have hcoord := congrFun huv
          (quadraticPair (aCoord i) (aCoord j)
            (fun h => hij (aCoord_injective h)))
      rw [targetTwo_sameA c i j hij] at hcoord
      simpa [aPart, squarefreeWedge_pair] using hcoord.symm
  rcases N4.dependent_of_vectorWedge_zero (aPart u) (aPart v) hApart with
    hu | hv | huvA
  · intro i k j l
    simp only [hankelMatrix]
    have hij := congrFun huv
      (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j))
    have hkl := congrFun huv
      (quadraticPair (aCoord k) (bCoord l) (aCoord_ne_bCoord k l))
    have hil := congrFun huv
      (quadraticPair (aCoord i) (bCoord l) (aCoord_ne_bCoord i l))
    have hkj := congrFun huv
      (quadraticPair (aCoord k) (bCoord j) (aCoord_ne_bCoord k j))
    simp only [targetTwo_cross, squarefreeWedge_pair] at hij hkl hil hkj
    rw [hij, hkl, hil, hkj]
    have hui : u (aCoord i) = 0 := congrFun hu i
    have huk : u (aCoord k) = 0 := congrFun hu k
    simp [hui, huk]
    ring
  · intro i k j l
    simp only [hankelMatrix]
    have hij := congrFun huv
      (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j))
    have hkl := congrFun huv
      (quadraticPair (aCoord k) (bCoord l) (aCoord_ne_bCoord k l))
    have hil := congrFun huv
      (quadraticPair (aCoord i) (bCoord l) (aCoord_ne_bCoord i l))
    have hkj := congrFun huv
      (quadraticPair (aCoord k) (bCoord j) (aCoord_ne_bCoord k j))
    simp only [targetTwo_cross, squarefreeWedge_pair] at hij hkl hil hkj
    rw [hij, hkl, hil, hkj]
    have hvi : v (aCoord i) = 0 := congrFun hv i
    have hvk : v (aCoord k) = 0 := congrFun hv k
    simp [hvi, hvk]
    ring
  · intro i k j l
    simp only [hankelMatrix]
    have hij := congrFun huv
      (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j))
    have hkl := congrFun huv
      (quadraticPair (aCoord k) (bCoord l) (aCoord_ne_bCoord k l))
    have hil := congrFun huv
      (quadraticPair (aCoord i) (bCoord l) (aCoord_ne_bCoord i l))
    have hkj := congrFun huv
      (quadraticPair (aCoord k) (bCoord j) (aCoord_ne_bCoord k j))
    simp only [targetTwo_cross, squarefreeWedge_pair] at hij hkl hil hkj
    rw [hij, hkl, hil, hkj]
    have hui : u (aCoord i) = v (aCoord i) := congrFun huvA i
    have huk : u (aCoord k) = v (aCoord k) := congrFun huvA k
    simp only [hui, huk]
    ring

/-- Classification of nonzero decomposable target forms. -/
theorem decomposableTarget_classification {c : TargetCoeff}
    (hdec : IsDecomposableTwo (targetTwo c)) (hc : c ≠ 0) :
    c = rZeroCoeff ∨ c = rOneCoeff ∨ c = rInfinityCoeff :=
  rankOne_target_classification (decomposableTarget_rankOne hdec) hc

/-- The decomposable fiber over a quadratic quotient class. -/
def decomposableFiber (q : QuadraticQuotient) : Set TwoForm :=
  {p | IsDecomposableTwo p ∧ quadraticQuotientProjection p = q}

theorem targetTwo_mem_targetTwoSpace (c : TargetCoeff) :
    targetTwo c ∈ targetTwoSpace := by
  exact ⟨c, rfl⟩

theorem quadraticQuotientProjection_eq_zero_iff (p : TwoForm) :
    quadraticQuotientProjection p = 0 ↔ p ∈ targetTwoSpace := by
  change Submodule.Quotient.mk p = 0 ↔ p ∈ targetTwoSpace
  exact Submodule.Quotient.mk_eq_zero targetTwoSpace

@[simp] theorem quadraticQuotientProjection_targetTwo (c : TargetCoeff) :
    quadraticQuotientProjection (targetTwo c) = 0 :=
  (quadraticQuotientProjection_eq_zero_iff _).2
    (targetTwo_mem_targetTwoSpace c)

@[simp] theorem decomposableTwo_zero : IsDecomposableTwo (0 : TwoForm) := by
  exact ⟨0, 0, by simp⟩

/-- Manuscript Lemma 2.1 (zero fiber): the decomposable points in the target
are zero and the three rational-place forms. -/
theorem zeroFiber_eq_rational :
    decomposableFiber 0 =
      {0, targetTwo rZeroCoeff, targetTwo rOneCoeff,
        targetTwo rInfinityCoeff} := by
  ext p
  constructor
  · rintro ⟨hdec, hpq⟩
    have hpT : p ∈ targetTwoSpace :=
      (quadraticQuotientProjection_eq_zero_iff p).1 hpq
    rcases hpT with ⟨c, hc⟩
    have hp : p = targetTwo c := hc.symm
    subst p
    by_cases hc0 : c = 0
    · subst c
      simp
    · rcases decomposableTarget_classification hdec hc0 with
        hzero | hone | hinfinity
      · subst c
        exact Or.inr (Or.inl rfl)
      · subst c
        exact Or.inr (Or.inr (Or.inl rfl))
      · subst c
        exact Or.inr (Or.inr (Or.inr rfl))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨decomposableTwo_zero, map_zero quadraticQuotientProjection⟩
    · exact ⟨decomposable_target_rZero,
        quadraticQuotientProjection_targetTwo rZeroCoeff⟩
    · exact ⟨decomposable_target_rOne,
        quadraticQuotientProjection_targetTwo rOneCoeff⟩
    · exact ⟨decomposable_target_rInfinity,
        quadraticQuotientProjection_targetTwo rInfinityCoeff⟩

/-- Difference space of a fiber relative to a chosen point in that fiber. -/
def fiberDifferenceSpace (q : QuadraticQuotient) (base : TwoForm) :
    Submodule F₂ TwoForm :=
  Submodule.span F₂ {d | ∃ p ∈ decomposableFiber q, d = p - base}

/-- The target/defect short exact sequence, specialized to the five-term
target but inherited from the generic circuit-flag proof. -/
theorem targetDefect_exact {V : Submodule F₂ (ANF 10)}
    (hAff : affine 10 ≤ V) :
    Module.finrank F₂ ↑V - Module.finrank F₂ ↑(affine 10) =
      N4.flagTargetRank V (mulTarget 5) +
        N4.flagDefectRank V (mulTarget 5) :=
  N4.flag_rank_ledger hAff

end

end N5
end UnrestrictedBooleanMul
