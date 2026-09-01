import UnrestrictedBooleanMul.N5.FirstOrderEnvelope
import UnrestrictedBooleanMul.N5.SecantPfaffian
import UnrestrictedBooleanMul.N4.Exterior

/-!
# Missing-coset rigidity

The unique target coset outside the first-order envelope has Hankel
cross-rank at least three.  Besides the coefficient statement proved in
`FirstOrderEnvelope`, this file derives two coordinate-free consequences used
by the nonlinear suffix argument: the coset contains no sum of two
decomposable two-forms, and exterior multiplication by any of its members is
injective on linear forms.

The proof is algebraic.  A nonzero vector in the exterior kernel would factor
the two-form; the existing symbolic secant theorem would then force Hankel
rank at most two, contradicting the missing-coordinate pivot.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

abbrev AmbientThreeForm :=
  Fin 10 → Fin 10 → Fin 10 → F₂

/-- Exterior multiplication of an ambient vector by a squarefree quadratic
form, expressed using its symmetric zero-diagonal coefficient matrix. -/
def ambientVectorWedgeTwo (u : LinearForm) (p : TwoForm) :
    AmbientThreeForm :=
  N4.vectorWedgeTwoN u (ambientTwoCoeff p)

/-- Exterior multiplication by a fixed ambient two-form as a linear map on
linear forms. -/
def ambientVectorWedgeMap (p : TwoForm) :
    LinearForm →ₗ[F₂] AmbientThreeForm where
  toFun u := ambientVectorWedgeTwo u p
  map_add' u v := by
    funext i j k
    simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      Pi.add_apply]
    ring
  map_smul' a u := by
    funext i j k
    simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Converting a squarefree quadratic form to its symmetric ambient matrix
and back loses no information. -/
theorem eq_squarefreeWedge_of_ambientTwoCoeff_eq_vectorWedgeN
    (p : TwoForm) (u v : LinearForm)
    (h : ambientTwoCoeff p = N4.vectorWedgeN u v) :
    p = squarefreeWedge u v := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  have hijCoeff := congrFun (congrFun h i) j
  simpa [ambientTwoCoeff, hij, N4.vectorWedgeN,
    squarefreeWedge_pair] using hijCoeff

/-- A nonzero vector annihilating a quadratic form forces a decomposable
factorization of that form. -/
theorem eq_squarefreeWedge_of_ambientVectorWedgeTwo_eq_zero
    (p : TwoForm) (u : LinearForm) (hu : u ≠ 0)
    (h : ambientVectorWedgeTwo u p = 0) :
    ∃ v : LinearForm, p = squarefreeWedge u v := by
  rcases N4.decomposable_of_vectorWedgeTwoN_zero
      u (ambientTwoCoeff p) hu h with ⟨v, hv⟩
  exact ⟨v, eq_squarefreeWedge_of_ambientTwoCoeff_eq_vectorWedgeN
    p u v hv⟩

/-- Manuscript Lemma 11.1, secant form: no member of the missing target coset
is a sum of two decomposable ambient two-forms. -/
theorem missingCoset_not_sum_two_decomposable
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    ¬ ∃ x y z w : LinearForm,
      targetTwo (firstOrderMissingCoeff + u) =
        squarefreeWedge x y + squarefreeWedge z w := by
  rintro ⟨x, y, z, w, hsecant⟩
  exact missingCoset_not_rankTwoHankel u hu
    (target_sum_two_decomposable_rankTwo hsecant)

/-- In particular, the missing target coset contains no decomposable
two-form. -/
theorem missingCoset_not_decomposable
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    ¬ IsDecomposableTwo (targetTwo (firstOrderMissingCoeff + u)) := by
  rintro ⟨x, y, hxy⟩
  apply missingCoset_not_sum_two_decomposable u hu
  refine ⟨x, y, 0, 0, ?_⟩
  simpa using hxy

/-- Manuscript equation (11.2), degree-one part: exterior multiplication by
a member of the missing coset has zero kernel on linear forms. -/
theorem missingCoset_vectorWedge_ker_eq_bot
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    LinearMap.ker
      (ambientVectorWedgeMap (targetTwo (firstOrderMissingCoeff + u))) = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxzero : ambientVectorWedgeTwo x
        (targetTwo (firstOrderMissingCoeff + u)) = 0 :=
      (LinearMap.mem_ker).1 hx
    have hx0 : x = 0 := by
      by_contra hxne
      rcases eq_squarefreeWedge_of_ambientVectorWedgeTwo_eq_zero
          (targetTwo (firstOrderMissingCoeff + u)) x hxne hxzero with
        ⟨y, hy⟩
      apply missingCoset_not_decomposable u hu
      exact ⟨x, y, hy⟩
    simpa [hx0]
  · exact bot_le

/-- Elementwise form of the zero-kernel theorem. -/
theorem missingCoset_vectorWedge_eq_zero_iff
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (x : LinearForm) :
    ambientVectorWedgeTwo x (targetTwo (firstOrderMissingCoeff + u)) = 0
      ↔ x = 0 := by
  constructor
  · intro hx
    have hxker : x ∈ LinearMap.ker
        (ambientVectorWedgeMap (targetTwo (firstOrderMissingCoeff + u))) :=
      (LinearMap.mem_ker).2 hx
    rw [missingCoset_vectorWedge_ker_eq_bot u hu] at hxker
    simpa using hxker
  · rintro rfl
    funext i j k
    simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]

end

end N5
end UnrestrictedBooleanMul
