import UnrestrictedBooleanMul.N5.LocalShadow

/-!
# Quadratic shadows of low products

This module records the Boolean degree-two part of a product
`(a + ell + q) * (b + m + c)` directly in squarefree coordinates.  Its main
purpose is to connect the one- and two-rotation Pluecker classification with
target shadows: replacing one factor by the sum of both factors changes the
quadratic shadow by exactly the quadratic part of the unchanged factor.

All identities are algebraic over `F₂`; no assignments are enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Boolean degree-lowering contraction created when a linear monomial
repeats one variable of a quadratic monomial. -/
def ambientBooleanContraction (ell : LinearForm) (q : TwoForm) : TwoForm :=
  fun s => (∑ i ∈ s.1, ell i) * q s

/-- Quadratic terms created when two quadratic monomials have identical
support. -/
def ambientTwoHadamard (q c : TwoForm) : TwoForm :=
  fun s => q s * c s

/-- Complete Boolean quadratic shadow of
`(a + ell + q) * (b + m + c)`. -/
def lowProductQuadraticShadow
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) : TwoForm :=
  a • c + b • q + squarefreeWedge ell m +
    ambientBooleanContraction ell c + ambientBooleanContraction m q +
    ambientTwoHadamard q c

/-- The complete high part (quartic, then cubic) of a product of two
degree-at-most-two factors. -/
def lowProductHighPart (ell m : LinearForm) (q c : TwoForm) :
    AmbientFourForm × AmbientThreeForm :=
  (ambientWedgeTwo q c, factorPlaneCubic ell m q c)

/-- The complete high part is symmetric in the two factors. -/
theorem lowProductHighPart_swap
    (ell m : LinearForm) (q c : TwoForm) :
    lowProductHighPart ell m q c = lowProductHighPart m ell c q := by
  apply Prod.ext
  · funext i j k l
    simp only [lowProductHighPart, ambientWedgeTwo]
    ring
  · simp only [lowProductHighPart, factorPlaneCubic]
    rw [add_comm]

/-- The elementary factor rotation `Y ↦ X + Y` leaves both the quartic
and cubic homogeneous parts unchanged. -/
theorem lowProductHighPart_rotate_right
    (ell m : LinearForm) (q c : TwoForm) :
    lowProductHighPart ell (ell + m) q (q + c) =
      lowProductHighPart ell m q c := by
  apply Prod.ext
  · change ambientWedgeTwo q (q + c) = ambientWedgeTwo q c
    calc
      ambientWedgeTwo q (q + c) =
          ambientWedgeTwo q q + ambientWedgeTwo q c :=
        map_add (ambientWedgeTwoMap q) q c
      _ = ambientWedgeTwo q c := by rw [ambientWedgeTwo_self, zero_add]
  · funext i j k
    simp only [lowProductHighPart, factorPlaneCubic,
      ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      ambientTwoCoeff_add, Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]

/-- The companion rotation `X ↦ X + Y` leaves the complete high part
unchanged. -/
theorem lowProductHighPart_rotate_left
    (ell m : LinearForm) (q c : TwoForm) :
    lowProductHighPart (ell + m) m (q + c) c =
      lowProductHighPart ell m q c := by
  calc
    lowProductHighPart (ell + m) m (q + c) c =
        lowProductHighPart m (ell + m) c (q + c) :=
      lowProductHighPart_swap (ell + m) m (q + c) c
    _ = lowProductHighPart m ell c q := by
      simpa [add_comm] using lowProductHighPart_rotate_right m ell c q
    _ = lowProductHighPart ell m q c :=
      lowProductHighPart_swap m ell c q

theorem ambientBooleanContraction_add_left
    (ell m : LinearForm) (q : TwoForm) :
    ambientBooleanContraction (ell + m) q =
      ambientBooleanContraction ell q + ambientBooleanContraction m q := by
  funext s
  simp only [ambientBooleanContraction, Pi.add_apply,
    Finset.sum_add_distrib]
  ring

theorem ambientBooleanContraction_add_right
    (ell : LinearForm) (q c : TwoForm) :
    ambientBooleanContraction ell (q + c) =
      ambientBooleanContraction ell q + ambientBooleanContraction ell c := by
  funext s
  simp only [ambientBooleanContraction, Pi.add_apply]
  ring

@[simp] theorem ambientBooleanContraction_zero_left (q : TwoForm) :
    ambientBooleanContraction 0 q = 0 := by
  funext s
  simp [ambientBooleanContraction]

@[simp] theorem ambientBooleanContraction_zero_right (ell : LinearForm) :
    ambientBooleanContraction ell 0 = 0 := by
  funext s
  simp [ambientBooleanContraction]

theorem ambientTwoHadamard_add_left (q c d : TwoForm) :
    ambientTwoHadamard (q + c) d =
      ambientTwoHadamard q d + ambientTwoHadamard c d := by
  funext s
  simp only [ambientTwoHadamard, Pi.add_apply]
  ring

theorem ambientTwoHadamard_add_right (q c d : TwoForm) :
    ambientTwoHadamard q (c + d) =
      ambientTwoHadamard q c + ambientTwoHadamard q d := by
  funext s
  simp only [ambientTwoHadamard, Pi.add_apply]
  ring

theorem ambientTwoHadamard_comm (q c : TwoForm) :
    ambientTwoHadamard q c = ambientTwoHadamard c q := by
  funext s
  simp [ambientTwoHadamard, mul_comm]

@[simp] theorem ambientTwoHadamard_self (q : TwoForm) :
    ambientTwoHadamard q q = q := by
  funext s
  exact N3Certificate.mul_self_f2 (q s)

@[simp] theorem ambientTwoHadamard_zero_left (q : TwoForm) :
    ambientTwoHadamard 0 q = 0 := by
  funext s
  simp [ambientTwoHadamard]

@[simp] theorem ambientTwoHadamard_zero_right (q : TwoForm) :
    ambientTwoHadamard q 0 = 0 := by
  funext s
  simp [ambientTwoHadamard]

theorem squarefreeWedge_comm_f2 (ell m : LinearForm) :
    squarefreeWedge ell m = squarefreeWedge m ell := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair]
  ring

@[simp] theorem squarefreeWedge_self_f2 (ell : LinearForm) :
    squarefreeWedge ell ell = 0 := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair, Pi.zero_apply]
  simp [mul_comm]

/-- The quadratic shadow is symmetric in its two factors. -/
theorem lowProductQuadraticShadow_swap
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    lowProductQuadraticShadow a b ell m q c =
      lowProductQuadraticShadow b a m ell c q := by
  rw [lowProductQuadraticShadow, lowProductQuadraticShadow,
    squarefreeWedge_comm_f2, ambientTwoHadamard_comm]
  module

/-- Right factor rotation `Y ↦ X + Y`: since `X(X+Y)=X+XY`, the
quadratic shadow changes by exactly the quadratic part `q` of `X`. -/
theorem lowProductQuadraticShadow_rotate_right
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    lowProductQuadraticShadow a (a + b) ell (ell + m) q (q + c) =
      q + lowProductQuadraticShadow a b ell m q c := by
  rw [lowProductQuadraticShadow, lowProductQuadraticShadow,
    ambientBooleanContraction_add_left,
    ambientBooleanContraction_add_right,
    ambientTwoHadamard_add_right, ambientTwoHadamard_self,
    squarefreeWedge_add_right, squarefreeWedge_self_f2]
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Left factor rotation `X ↦ X + Y`. -/
theorem lowProductQuadraticShadow_rotate_left
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm) :
    lowProductQuadraticShadow (a + b) b (ell + m) m (q + c) c =
      c + lowProductQuadraticShadow a b ell m q c := by
  calc
    lowProductQuadraticShadow (a + b) b (ell + m) m (q + c) c =
        lowProductQuadraticShadow b (a + b) m (ell + m) c (q + c) :=
      lowProductQuadraticShadow_swap (a + b) b (ell + m) m (q + c) c
    _ = lowProductQuadraticShadow b (b + a) m (m + ell) c (c + q) := by
      rw [add_comm a b, add_comm ell m, add_comm q c]
    _ = c + lowProductQuadraticShadow b a m ell c q :=
      lowProductQuadraticShadow_rotate_right b a m ell c q
    _ = c + lowProductQuadraticShadow a b ell m q c := by
      rw [lowProductQuadraticShadow_swap b a m ell c q]

/-- One rational rotation changes the target shadow only by an old
quadratic factor direction. -/
theorem rotate_right_shadow_mod_submodule
    (W : Submodule F₂ TwoForm)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hq : q ∈ W) :
    lowProductQuadraticShadow a (a + b) ell (ell + m) q (q + c) +
      lowProductQuadraticShadow a b ell m q c ∈ W := by
  rw [lowProductQuadraticShadow_rotate_right]
  have hself : lowProductQuadraticShadow a b ell m q c +
      lowProductQuadraticShadow a b ell m q c = 0 := by
    funext s
    exact @CharTwo.add_self_eq_zero F₂ _ _
      (lowProductQuadraticShadow a b ell m q c s)
  rw [add_assoc, hself, add_zero]
  exact hq

/-- The analogous left rotation changes the shadow only by `c`. -/
theorem rotate_left_shadow_mod_submodule
    (W : Submodule F₂ TwoForm)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hc : c ∈ W) :
    lowProductQuadraticShadow (a + b) b (ell + m) m (q + c) c +
      lowProductQuadraticShadow a b ell m q c ∈ W := by
  rw [lowProductQuadraticShadow_rotate_left]
  have hself : lowProductQuadraticShadow a b ell m q c +
      lowProductQuadraticShadow a b ell m q c = 0 := by
    funext s
    exact @CharTwo.add_self_eq_zero F₂ _ _
      (lowProductQuadraticShadow a b ell m q c s)
  rw [add_assoc, hself, add_zero]
  exact hc

/-- The two-step basis change `(X, Y) ↦ (Y, X + Y)` also preserves the
quadratic shadow modulo an old envelope containing `c`.  Together with the
two elementary rotation lemmas, this covers the three nontrivial local
changes used by the equal-wedge classification. -/
theorem two_rotations_shadow_mod_submodule
    (W : Submodule F₂ TwoForm)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hc : c ∈ W) :
    lowProductQuadraticShadow b (a + b) m (ell + m) c (q + c) +
      lowProductQuadraticShadow a b ell m q c ∈ W := by
  rw [add_comm a b, add_comm ell m, add_comm q c]
  rw [lowProductQuadraticShadow_swap a b ell m q c]
  exact rotate_right_shadow_mod_submodule W b a m ell c q hc

/-- One right rotation preserves the complete high part and changes the
quadratic shadow only inside an old quadratic envelope containing `q`. -/
theorem lowProduct_rotate_right_high_and_shadow_mod_submodule
    (W : Submodule F₂ TwoForm)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hq : q ∈ W) :
    lowProductHighPart ell (ell + m) q (q + c) =
        lowProductHighPart ell m q c ∧
      lowProductQuadraticShadow a (a + b) ell (ell + m) q (q + c) +
        lowProductQuadraticShadow a b ell m q c ∈ W :=
  ⟨lowProductHighPart_rotate_right ell m q c,
    rotate_right_shadow_mod_submodule W a b ell m q c hq⟩

/-- Companion complete-high/shadow statement for a left rotation. -/
theorem lowProduct_rotate_left_high_and_shadow_mod_submodule
    (W : Submodule F₂ TwoForm)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hc : c ∈ W) :
    lowProductHighPart (ell + m) m (q + c) c =
        lowProductHighPart ell m q c ∧
      lowProductQuadraticShadow (a + b) b (ell + m) m (q + c) c +
        lowProductQuadraticShadow a b ell m q c ∈ W :=
  ⟨lowProductHighPart_rotate_left ell m q c,
    rotate_left_shadow_mod_submodule W a b ell m q c hc⟩

/-- The two-step change `(X, Y) ↦ (Y, X + Y)` likewise preserves the
complete high part and the quadratic shadow modulo the old envelope. -/
theorem lowProduct_two_rotations_high_and_shadow_mod_submodule
    (W : Submodule F₂ TwoForm)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hc : c ∈ W) :
    lowProductHighPart m (ell + m) c (q + c) =
        lowProductHighPart ell m q c ∧
      lowProductQuadraticShadow b (a + b) m (ell + m) c (q + c) +
        lowProductQuadraticShadow a b ell m q c ∈ W := by
  constructor
  · calc
      lowProductHighPart m (ell + m) c (q + c) =
          lowProductHighPart m ell c q := by
        simpa [add_comm] using lowProductHighPart_rotate_right m ell c q
      _ = lowProductHighPart ell m q c :=
        lowProductHighPart_swap m ell c q
  · exact two_rotations_shadow_mod_submodule W a b ell m q c hc

end
end N5
end UnrestrictedBooleanMul
