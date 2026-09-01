import UnrestrictedBooleanMul.N5.ClosedPlaces

/-!
# Rank-two Hankel support

The rank condition is expressed by vanishing `3 × 3` minors.  The proof that
all such words lie in the eight-dimensional closed-place envelope uses five
overlapping Hankel minors and a Boolean polynomial certificate.  This is a
kernel-checked ideal calculation, not a table lookup or an imported search
result.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Characteristic-two determinant of a `3 × 3` Hankel submatrix. -/
def hankelMinorThree (c : TargetCoeff)
    (i k m j l n : Fin 5) : F₂ :=
  hankelMatrix c i j * hankelMatrix c k l * hankelMatrix c m n +
  hankelMatrix c i j * hankelMatrix c k n * hankelMatrix c m l +
  hankelMatrix c i l * hankelMatrix c k j * hankelMatrix c m n +
  hankelMatrix c i l * hankelMatrix c k n * hankelMatrix c m j +
  hankelMatrix c i n * hankelMatrix c k j * hankelMatrix c m l +
  hankelMatrix c i n * hankelMatrix c k l * hankelMatrix c m j

/-- Algebraic cross-rank-at-most-two condition. -/
def HankelRankLETwo (c : TargetCoeff) : Prop :=
  ∀ i k m j l n : Fin 5, hankelMinorThree c i k m j l n = 0

private theorem f2_pow_succ (x : F₂) (n : Nat) : x ^ (n + 1) = x := by
  rcases f2_eq_zero_or_one x with rfl | rfl <;> simp

private theorem minor_middle {c : TargetCoeff} (h : HankelRankLETwo c) :
    c 2 * c 4 * c 6 + c 2 * c 5 + c 3 * c 6 + c 4 = 0 := by
  have hm := h (0 : Fin 5) 1 2 2 3 4
  change c 2 * c 4 * c 6 + c 2 * c 5 * c 5 +
      c 3 * c 3 * c 6 + c 3 * c 5 * c 4 +
      c 4 * c 3 * c 5 + c 4 * c 4 * c 4 = 0 at hm
  simpa only [N3Certificate.mul_self_f2, mul_assoc, mul_comm,
    mul_left_comm, add_assoc, add_comm, add_left_comm,
    CharTwo.add_self_eq_zero, CharTwo.add_cancel_left,
    CharTwo.add_cancel_right, zero_add, add_zero] using hm

private theorem minor_left {c : TargetCoeff} (h : HankelRankLETwo c) :
    c 0 * c 2 * c 4 + c 0 * c 3 + c 1 * c 4 + c 2 = 0 := by
  have hm := h (0 : Fin 5) 1 2 0 1 2
  change c 0 * c 2 * c 4 + c 0 * c 3 * c 3 +
      c 1 * c 1 * c 4 + c 1 * c 3 * c 2 +
      c 2 * c 1 * c 3 + c 2 * c 2 * c 2 = 0 at hm
  simpa only [N3Certificate.mul_self_f2, mul_assoc, mul_comm,
    mul_left_comm, add_assoc, add_comm, add_left_comm,
    CharTwo.add_self_eq_zero, CharTwo.add_cancel_left,
    CharTwo.add_cancel_right, zero_add, add_zero] using hm

private theorem minor_right {c : TargetCoeff} (h : HankelRankLETwo c) :
    c 4 * c 6 * c 8 + c 4 * c 7 + c 5 * c 8 + c 6 = 0 := by
  have hm := h (2 : Fin 5) 3 4 2 3 4
  change c 4 * c 6 * c 8 + c 4 * c 7 * c 7 +
      c 5 * c 5 * c 8 + c 5 * c 7 * c 6 +
      c 6 * c 5 * c 7 + c 6 * c 6 * c 6 = 0 at hm
  simpa only [N3Certificate.mul_self_f2, mul_assoc, mul_comm,
    mul_left_comm, add_assoc, add_comm, add_left_comm,
    CharTwo.add_self_eq_zero, CharTwo.add_cancel_left,
    CharTwo.add_cancel_right, zero_add, add_zero] using hm

private theorem minor_left_shift {c : TargetCoeff} (h : HankelRankLETwo c) :
    c 1 * c 3 * c 5 + c 1 * c 4 + c 2 * c 5 + c 3 = 0 := by
  have hm := h (0 : Fin 5) 1 2 1 2 3
  change c 1 * c 3 * c 5 + c 1 * c 4 * c 4 +
      c 2 * c 2 * c 5 + c 2 * c 4 * c 3 +
      c 3 * c 2 * c 4 + c 3 * c 3 * c 3 = 0 at hm
  simpa only [N3Certificate.mul_self_f2, mul_assoc, mul_comm,
    mul_left_comm, add_assoc, add_comm, add_left_comm,
    CharTwo.add_self_eq_zero, CharTwo.add_cancel_left,
    CharTwo.add_cancel_right, zero_add, add_zero] using hm

private theorem minor_right_shift {c : TargetCoeff} (h : HankelRankLETwo c) :
    c 3 * c 5 * c 7 + c 3 * c 6 + c 4 * c 7 + c 5 = 0 := by
  have hm := h (1 : Fin 5) 2 3 2 3 4
  change c 3 * c 5 * c 7 + c 3 * c 6 * c 6 +
      c 4 * c 4 * c 7 + c 4 * c 6 * c 5 +
      c 5 * c 4 * c 6 + c 5 * c 5 * c 5 = 0 at hm
  simpa only [N3Certificate.mul_self_f2, mul_assoc, mul_comm,
    mul_left_comm, add_assoc, add_comm, add_left_comm,
    CharTwo.add_self_eq_zero, CharTwo.add_cancel_left,
    CharTwo.add_cancel_right, zero_add, add_zero] using hm

/-- Boolean ideal certificate reducing rank-two support to the single missing
linear coordinate of the eight-dimensional closed-place envelope. -/
private theorem rankTwo_envelope_identity (c : TargetCoeff) :
    c 2 + c 3 + c 5 + c 6 =
      (c 2 + c 2*c 3*c 5 + c 2*c 3*c 6 + c 3*c 4 +
          c 3*c 4*c 6 + c 4*c 6 + c 5) *
        (c 2*c 4*c 6 + c 2*c 5 + c 3*c 6 + c 4) +
      (1 + c 2*c 3*c 4 + c 2*c 4 + c 3) *
        (c 0*c 2*c 4 + c 0*c 3 + c 1*c 4 + c 2) +
      (1 + c 3 + c 3*c 4*c 5 + c 3*c 6*c 8 + c 3*c 8 +
          c 4*c 5*c 8 + c 4*c 6 + c 4*c 7 + c 5*c 8) *
        (c 4*c 6*c 8 + c 4*c 7 + c 5*c 8 + c 6) +
      (1 + c 2*c 3 + c 2*c 3*c 5 + c 2*c 4 + c 3*c 4 +
          c 3*c 4*c 5 + c 4*c 5 + c 5) *
        (c 1*c 3*c 5 + c 1*c 4 + c 2*c 5 + c 3) +
      (c 3 + c 3*c 4*c 8 + c 3*c 6*c 8 + c 4*c 5 +
          c 4*c 5*c 8 + c 5 + c 6*c 8) *
      (c 3*c 5*c 7 + c 3*c 6 + c 4*c 7 + c 5) := by
  have htwo : (2 : F₂) = 0 := N3Certificate.two_eq_zero_f2
  have hfour : (4 : F₂) = 0 := by decide
  ring_nf
  simp only [pow_two, N3Certificate.mul_self_f2]
  ring_nf
  simp only [htwo, hfour, mul_zero, add_zero]

/-- Every rank-two Hankel word satisfies the defining equation of the
closed-place envelope. -/
theorem rankTwoHankel_equation {c : TargetCoeff} (h : HankelRankLETwo c) :
    c 2 + c 3 + c 5 + c 6 = 0 := by
  rw [rankTwo_envelope_identity c]
  rw [minor_middle h, minor_left h, minor_right h,
    minor_left_shift h, minor_right_shift h]
  simp

/-- Explicit reconstruction of a coefficient word from the eight
closed-place directions. -/
private def closedPlaceCoordinates (c : TargetCoeff) : Fin 8 → F₂ :=
  ![c 0 + c 7,
    c 7,
    c 8 + c 7,
    c 1 + c 2 + c 4 + c 5,
    c 2 + c 5,
    c 2 + c 4 + c 5 + c 7,
    c 2 + c 4,
    c 2 + c 3 + c 4 + c 5]

private theorem closedPlace_reconstruction {c : TargetCoeff}
    (hc : c 2 + c 3 + c 5 + c 6 = 0) :
    c = ∑ i : Fin 8, closedPlaceCoordinates c i • closedPlaceDirections i := by
  have h6 : c 6 = c 2 + (c 3 + c 5) := by
    calc
      c 6 = c 6 + 0 := (add_zero _).symm
      _ = c 6 + (c 2 + c 3 + c 5 + c 6) := by rw [hc]
      _ = c 2 + (c 3 + c 5) := by
        simp [add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero]
  funext s
  fin_cases s <;>
    simp [closedPlaceCoordinates, closedPlaceDirections, rZeroCoeff,
      rOneCoeff, rInfinityCoeff, jZeroCoeff, jOneCoeff, jInfinityCoeff,
      dStarZeroCoeff, dStarOneCoeff, Fin.sum_univ_succ,
      add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero,
      CharTwo.add_cancel_left]
  try { exact h6 }

/-- Rank-two Hankel support, envelope form of manuscript Lemma 4.1. -/
theorem rankTwoHankel_support {c : TargetCoeff} (h : HankelRankLETwo c) :
    c ∈ closedPlaceCoeffSpace := by
  rw [closedPlace_reconstruction (rankTwoHankel_equation h)]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩)

end

end N5
end UnrestrictedBooleanMul
