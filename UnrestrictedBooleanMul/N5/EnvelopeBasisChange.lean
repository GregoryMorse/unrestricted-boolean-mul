import UnrestrictedBooleanMul.N5.EnvelopeShadow

/-!
# Algebraic basis changes for exceptional n=5 planes

An ordered basis of a two-dimensional plane over `F₂` has six possible
presentations.  This module packages those six changes and proves directly
that they preserve the complete high part of a low product while changing
its Boolean quadratic shadow only inside the first-order envelope.

This is finite linear algebra on a two-dimensional coefficient space, not an
enumeration of circuits or Boolean assignments.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The six ordered bases obtained from an ordered basis `(X,Y)` of a
two-dimensional vector space over `F₂`. -/
inductive PlaneBasisChange where
  | identity
  | swap
  | rotateRight
  | rotateLeft
  | cycleRight
  | cycleLeft
  deriving DecidableEq

/-- Apply the same basis change to any additive pair. -/
def PlaneBasisChange.basisPair {α : Type*} [Add α]
    (g : PlaneBasisChange) (x y : α) : α × α :=
  match g with
  | .identity => (x, y)
  | .swap => (y, x)
  | .rotateRight => (x, x + y)
  | .rotateLeft => (x + y, y)
  | .cycleRight => (y, x + y)
  | .cycleLeft => (x + y, x)

/-- Inverse of an ordered-plane basis change.  The two rotations are
involutions, while the two cyclic changes are inverse to one another. -/
def PlaneBasisChange.inverse : PlaneBasisChange → PlaneBasisChange
  | .identity => .identity
  | .swap => .swap
  | .rotateRight => .rotateRight
  | .rotateLeft => .rotateLeft
  | .cycleRight => .cycleLeft
  | .cycleLeft => .cycleRight

theorem PlaneBasisChange.basisPair_apply_inverse
    {α : Type*} [AddCommGroup α] [Module F₂ α]
    (g : PlaneBasisChange) (x y : α) :
    g.basisPair (g.inverse.basisPair x y).1
        (g.inverse.basisPair x y).2 = (x, y) := by
  have htwo : (2 : F₂) = 0 := by decide
  have hself (z : α) : z + z = 0 := by
    rw [← two_smul F₂ z, htwo, zero_smul]
  have hleft (z w : α) : z + (z + w) = w := by
    rw [← add_assoc, hself, zero_add]
  have hright (z w : α) : (z + w) + w = z := by
    rw [add_assoc, hself, add_zero]
  have hsandwich (z w : α) : (z + w) + z = w := by
    rw [add_comm z w, hright]
  have houter (z w : α) : z + (w + z) = w := by
    rw [add_comm w z, hleft]
  cases g <;> apply Prod.ext <;>
    simp [PlaneBasisChange.inverse, PlaneBasisChange.basisPair,
      hleft, hright, hsandwich, houter]

theorem PlaneBasisChange.inverse_basisPair_apply
    {α : Type*} [AddCommGroup α] [Module F₂ α]
    (g : PlaneBasisChange) (x y : α) :
    g.inverse.basisPair (g.basisPair x y).1 (g.basisPair x y).2 =
      (x, y) := by
  have htwo : (2 : F₂) = 0 := by decide
  have hself (z : α) : z + z = 0 := by
    rw [← two_smul F₂ z, htwo, zero_smul]
  have hleft (z w : α) : z + (z + w) = w := by
    rw [← add_assoc, hself, zero_add]
  have hright (z w : α) : (z + w) + w = z := by
    rw [add_assoc, hself, add_zero]
  have hsandwich (z w : α) : (z + w) + z = w := by
    rw [add_comm z w, hright]
  have houter (z w : α) : z + (w + z) = w := by
    rw [add_comm w z, hleft]
  cases g <;> apply Prod.ext <;>
    simp [PlaneBasisChange.inverse, PlaneBasisChange.basisPair,
      hleft, hright, hsandwich, houter]

/-- Complete high part after changing the ordered factor basis. -/
def changedLowProductHighPart
    (g : PlaneBasisChange) (ell m : LinearForm) (q c : TwoForm) :
    AmbientFourForm × AmbientThreeForm :=
  let linearPair := g.basisPair ell m
  let twoPair := g.basisPair q c
  lowProductHighPart linearPair.1 linearPair.2 twoPair.1 twoPair.2

/-- Boolean quadratic shadow after applying the same basis change to the
constant, linear, and quadratic parts of the two factors. -/
def changedLowProductQuadraticShadow
    (g : PlaneBasisChange) (a b : F₂) (ell m : LinearForm)
    (q c : TwoForm) : TwoForm :=
  let constantPair := g.basisPair a b
  let linearPair := g.basisPair ell m
  let twoPair := g.basisPair q c
  lowProductQuadraticShadow constantPair.1 constantPair.2
    linearPair.1 linearPair.2 twoPair.1 twoPair.2

theorem changedLowProductHighPart_inverse
    (g : PlaneBasisChange) (ell m : LinearForm) (q c : TwoForm) :
    changedLowProductHighPart g
        (g.inverse.basisPair ell m).1 (g.inverse.basisPair ell m).2 q c =
      lowProductHighPart ell m (g.basisPair q c).1
        (g.basisPair q c).2 := by
  simp only [changedLowProductHighPart]
  rw [g.basisPair_apply_inverse ell m]

theorem changedLowProductQuadraticShadow_inverse
    (g : PlaneBasisChange) (a b : F₂) (ell m : LinearForm)
    (q c : TwoForm) :
    changedLowProductQuadraticShadow g
        (g.inverse.basisPair a b).1 (g.inverse.basisPair a b).2
        (g.inverse.basisPair ell m).1 (g.inverse.basisPair ell m).2 q c =
      lowProductQuadraticShadow a b ell m (g.basisPair q c).1
        (g.basisPair q c).2 := by
  simp only [changedLowProductQuadraticShadow]
  rw [g.basisPair_apply_inverse a b, g.basisPair_apply_inverse ell m]

private theorem add_self_eq_zero_twoForm (X : TwoForm) : X + X = 0 := by
  funext s
  exact CharTwo.add_self_eq_zero (X s)

/-- Every one of the six changes preserves the high part and changes the
quadratic shadow only by an element of the first-order envelope. -/
theorem exceptionalPlane_basisChange_high_and_shadow
    (P : ExceptionalIndependentPlane) (g : PlaneBasisChange)
    (a b : F₂) (ell m : LinearForm) :
    changedLowProductHighPart g ell m P.left P.right =
        lowProductHighPart ell m P.left P.right ∧
      changedLowProductQuadraticShadow g a b ell m P.left P.right +
          lowProductQuadraticShadow a b ell m P.left P.right ∈
        firstOrderEnvelopeTwoSpace := by
  cases g with
  | identity =>
      constructor
      · rfl
      · change lowProductQuadraticShadow a b ell m P.left P.right +
            lowProductQuadraticShadow a b ell m P.left P.right ∈
          firstOrderEnvelopeTwoSpace
        rw [add_self_eq_zero_twoForm]
        exact firstOrderEnvelopeTwoSpace.zero_mem
  | swap =>
      constructor
      · exact lowProductHighPart_swap m ell P.right P.left
      · change lowProductQuadraticShadow b a m ell P.right P.left +
            lowProductQuadraticShadow a b ell m P.left P.right ∈
          firstOrderEnvelopeTwoSpace
        rw [lowProductQuadraticShadow_swap b a m ell P.right P.left,
          add_self_eq_zero_twoForm]
        exact firstOrderEnvelopeTwoSpace.zero_mem
  | rotateRight =>
      exact lowProduct_rotate_right_high_and_shadow_mod_submodule
        firstOrderEnvelopeTwoSpace a b ell m P.left P.right
          P.left_mem_firstOrderEnvelope
  | rotateLeft =>
      exact lowProduct_rotate_left_high_and_shadow_mod_submodule
        firstOrderEnvelopeTwoSpace a b ell m P.left P.right
          P.right_mem_firstOrderEnvelope
  | cycleRight =>
      exact lowProduct_two_rotations_high_and_shadow_mod_submodule
        firstOrderEnvelopeTwoSpace a b ell m P.left P.right
          P.right_mem_firstOrderEnvelope
  | cycleLeft =>
      constructor
      · change lowProductHighPart (ell + m) ell (P.left + P.right) P.left =
          lowProductHighPart ell m P.left P.right
        calc
          lowProductHighPart (ell + m) ell (P.left + P.right) P.left =
              lowProductHighPart ell (ell + m) P.left
                (P.left + P.right) :=
            lowProductHighPart_swap (ell + m) ell
              (P.left + P.right) P.left
          _ = lowProductHighPart ell m P.left P.right :=
            lowProductHighPart_rotate_right ell m P.left P.right
      · change lowProductQuadraticShadow (a + b) a (ell + m) ell
              (P.left + P.right) P.left +
            lowProductQuadraticShadow a b ell m P.left P.right ∈
          firstOrderEnvelopeTwoSpace
        rw [lowProductQuadraticShadow_swap (a + b) a (ell + m) ell
          (P.left + P.right) P.left]
        exact rotate_right_shadow_mod_submodule firstOrderEnvelopeTwoSpace
          a b ell m P.left P.right P.left_mem_firstOrderEnvelope

/-- The cubic part of every changed presentation is the cubic part of the
canonical presentation. -/
theorem exceptionalPlane_basisChange_cubic
    (P : ExceptionalIndependentPlane) (g : PlaneBasisChange)
    (ell m : LinearForm) :
    (changedLowProductHighPart g ell m P.left P.right).2 =
      factorPlaneCubic ell m P.left P.right := by
  have h := (exceptionalPlane_basisChange_high_and_shadow
    P g 0 0 ell m).1
  simpa [lowProductHighPart] using congrArg Prod.snd h

private theorem paired_sums_reassociate
    (X₁ X₂ Y₁ Y₂ : TwoForm) :
    (X₁ + X₂) + (Y₁ + Y₂) = (X₁ + Y₁) + (X₂ + Y₂) := by
  module

/-- Two changed presentations differ from the corresponding two canonical
presentations by a single element of the first-order envelope. -/
theorem exceptionalPlane_basisChange_shadow_sum_add_canonical_mem
    (P : ExceptionalIndependentPlane) (g : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) :
    (changedLowProductQuadraticShadow g a b ell m P.left P.right +
        changedLowProductQuadraticShadow g a' b' ell' m' P.left P.right) +
      (lowProductQuadraticShadow a b ell m P.left P.right +
        lowProductQuadraticShadow a' b' ell' m' P.left P.right) ∈
      firstOrderEnvelopeTwoSpace := by
  rw [paired_sums_reassociate]
  exact firstOrderEnvelopeTwoSpace.add_mem
    (exceptionalPlane_basisChange_high_and_shadow P g a b ell m).2
    (exceptionalPlane_basisChange_high_and_shadow P g a' b' ell' m').2

/-- Missing-coset exclusion for all six ordered bases of each of the seven
exceptional independent planes. -/
theorem exceptionalIndependentPlane_basisChange_shadow_not_missingCoset
    (P : ExceptionalIndependentPlane) (g : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic :
      (changedLowProductHighPart g ell m P.left P.right).2 =
        (changedLowProductHighPart g ell' m' P.left P.right).2)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    changedLowProductQuadraticShadow g a b ell m P.left P.right +
        changedLowProductQuadraticShadow g a' b' ell' m' P.left P.right ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hcanonicalCubic :
      factorPlaneCubic ell m P.left P.right =
        factorPlaneCubic ell' m' P.left P.right := by
    rw [← exceptionalPlane_basisChange_cubic P g ell m,
      ← exceptionalPlane_basisChange_cubic P g ell' m']
    exact hcubic
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (changedLowProductQuadraticShadow g a b ell m P.left P.right +
      changedLowProductQuadraticShadow g a' b' ell' m' P.left P.right)
    (lowProductQuadraticShadow a b ell m P.left P.right +
      lowProductQuadraticShadow a' b' ell' m' P.left P.right)
    (exceptionalPlane_basisChange_shadow_sum_add_canonical_mem
      P g a b a' b' ell m ell' m')
  · exact exceptionalIndependentPlane_shadow_not_missingCoset P
      a b a' b' ell m ell' m' hcanonicalCubic
  · exact hu

/-- An arbitrary ordered presentation of one of the seven exceptional
independent planes. -/
def IsExceptionalIndependentPlanePresentation (q c : TwoForm) : Prop :=
  ∃ (P : ExceptionalIndependentPlane) (g : PlaneBasisChange),
    q = (g.basisPair P.left P.right).1 ∧
      c = (g.basisPair P.left P.right).2

/-- Presentation-free form of the seven exceptional-plane exclusions.  The
constants and linear parts are pulled back through the inverse basis change;
no coordinates of the ambient ten-dimensional space are enumerated. -/
theorem exceptionalIndependentPlanePresentation_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (q c : TwoForm)
    (hpresentation : IsExceptionalIndependentPlanePresentation q c)
    (hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q c)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q c ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases hpresentation with ⟨P, g, hq, hc⟩
  subst q
  subst c
  let ab := g.inverse.basisPair a b
  let ab' := g.inverse.basisPair a' b'
  let lm := g.inverse.basisPair ell m
  let lm' := g.inverse.basisPair ell' m'
  have hcubicChanged :
      (changedLowProductHighPart g lm.1 lm.2 P.left P.right).2 =
        (changedLowProductHighPart g lm'.1 lm'.2 P.left P.right).2 := by
    rw [show lm = g.inverse.basisPair ell m by rfl,
      show lm' = g.inverse.basisPair ell' m' by rfl,
      changedLowProductHighPart_inverse,
      changedLowProductHighPart_inverse]
    exact hcubic
  have hexclusion :=
    exceptionalIndependentPlane_basisChange_shadow_not_missingCoset
      P g ab.1 ab.2 ab'.1 ab'.2 lm.1 lm.2 lm'.1 lm'.2
        hcubicChanged u hu
  rw [show ab = g.inverse.basisPair a b by rfl,
    show ab' = g.inverse.basisPair a' b' by rfl,
    show lm = g.inverse.basisPair ell m by rfl,
    show lm' = g.inverse.basisPair ell' m' by rfl,
    changedLowProductQuadraticShadow_inverse,
    changedLowProductQuadraticShadow_inverse] at hexclusion
  exact hexclusion

end

end N5
end UnrestrictedBooleanMul
