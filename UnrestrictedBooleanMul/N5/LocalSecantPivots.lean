import UnrestrictedBooleanMul.N5.SecantPfaffian
import UnrestrictedBooleanMul.N5.RelationGiftPivots

/-!
# Local secant coefficient pivots

The sparse relation through an effective point rewrites as a rank-four
secant after moving that point's chosen lift.  This module fixes the two
six-dimensional target-coefficient spaces selected by the corresponding
Pfaffian equations and proves their exact dimensions.  The remaining local
lemmas show that the secant coefficients land in these spaces.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Three tail constraints selected by a doubled rational point at zero. -/
def rationalZeroSecantConstraint :
    TargetCoeff →ₗ[F₂] (Fin 3 → F₂) where
  toFun c := ![c 3 + c 5, c 4 + c 6, c 4 + c 5 + c 6 + c 7]
  map_add' c d := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a c := by ext i; fin_cases i <;> simp <;> ring

/-- Three norm-block constraints selected by the degree-two place. -/
def degreeTwoSecantConstraint :
    TargetCoeff →ₗ[F₂] (Fin 3 → F₂) where
  toFun c :=
    ![c 1 + c 2 + c 4 + c 5,
      c 1 + c 3 + c 4 + c 6,
      c 1 + c 7]
  map_add' c d := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a c := by ext i; fin_cases i <;> simp <;> ring

def rationalZeroSecantCoeffSpace : Submodule F₂ TargetCoeff :=
  LinearMap.ker rationalZeroSecantConstraint

def degreeTwoSecantCoeffSpace : Submodule F₂ TargetCoeff :=
  LinearMap.ker degreeTwoSecantConstraint

/-- Explicit section of the rational secant constraints. -/
def rationalZeroSecantConstraintSection :
    (Fin 3 → F₂) →ₗ[F₂] TargetCoeff where
  toFun t := ![0, 0, 0, t 0, t 1, 0, 0, t 1 + t 2, 0]
  map_add' t u := by
    ext i
    fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' a t := by
    ext i
    fin_cases i <;> simp [mul_add]

theorem rationalZeroSecantConstraint_section (t : Fin 3 → F₂) :
    rationalZeroSecantConstraint
      (rationalZeroSecantConstraintSection t) = t := by
  ext i
  fin_cases i
  · simp [rationalZeroSecantConstraint,
      rationalZeroSecantConstraintSection]
  · simp [rationalZeroSecantConstraint,
      rationalZeroSecantConstraintSection]
  · simp [rationalZeroSecantConstraint,
      rationalZeroSecantConstraintSection]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]

/-- Explicit section of the degree-two secant constraints. -/
def degreeTwoSecantConstraintSection :
    (Fin 3 → F₂) →ₗ[F₂] TargetCoeff where
  toFun t := ![0, 0, t 0, t 1, 0, 0, 0, t 2, 0]
  map_add' t u := by ext i; fin_cases i <;> simp
  map_smul' a t := by ext i; fin_cases i <;> simp

theorem degreeTwoSecantConstraint_section (t : Fin 3 → F₂) :
    degreeTwoSecantConstraint (degreeTwoSecantConstraintSection t) = t := by
  ext i
  fin_cases i <;>
    simp [degreeTwoSecantConstraint, degreeTwoSecantConstraintSection]

theorem rationalZeroSecantConstraint_surjective :
    Function.Surjective rationalZeroSecantConstraint := by
  intro t
  exact ⟨rationalZeroSecantConstraintSection t,
    rationalZeroSecantConstraint_section t⟩

theorem degreeTwoSecantConstraint_surjective :
    Function.Surjective degreeTwoSecantConstraint := by
  intro t
  exact ⟨degreeTwoSecantConstraintSection t,
    degreeTwoSecantConstraint_section t⟩

/-- The rational secant coefficient space has codimension three. -/
theorem rationalZeroSecantCoeffSpace_finrank :
    Module.finrank F₂ rationalZeroSecantCoeffSpace = 6 := by
  have h := rationalZeroSecantConstraint.finrank_range_add_finrank_ker
  have hrange : LinearMap.range rationalZeroSecantConstraint = ⊤ :=
    LinearMap.range_eq_top.mpr rationalZeroSecantConstraint_surjective
  rw [hrange] at h
  have h' : 3 + Module.finrank F₂
      (LinearMap.ker rationalZeroSecantConstraint) = 9 := by
    simpa [TargetCoeff] using h
  change Module.finrank F₂
    (LinearMap.ker rationalZeroSecantConstraint) = 6
  omega

/-- The degree-two secant coefficient space also has codimension three. -/
theorem degreeTwoSecantCoeffSpace_finrank :
    Module.finrank F₂ degreeTwoSecantCoeffSpace = 6 := by
  have h := degreeTwoSecantConstraint.finrank_range_add_finrank_ker
  have hrange : LinearMap.range degreeTwoSecantConstraint = ⊤ :=
    LinearMap.range_eq_top.mpr degreeTwoSecantConstraint_surjective
  rw [hrange] at h
  have h' : 3 + Module.finrank F₂
      (LinearMap.ker degreeTwoSecantConstraint) = 9 := by
    simpa [TargetCoeff] using h
  change Module.finrank F₂
    (LinearMap.ker degreeTwoSecantConstraint) = 6
  omega

/-- Rational evaluation together with the zero first jet. -/
def rationalZeroLocalCoeffDirection : Fin 4 → TargetCoeff :=
  ![closedPlaceDirections 0, closedPlaceDirections 1,
    closedPlaceDirections 2, closedPlaceDirections 3]

def rationalZeroLocalCoeffSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ (Set.range rationalZeroLocalCoeffDirection)

theorem rationalZeroLocalCoeffDirection_linearIndependent :
    LinearIndependent F₂ rationalZeroLocalCoeffDirection := by
  let index : Fin 4 → Fin 8 := ![0, 1, 2, 3]
  have hindex : Function.Injective index := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [index] at h ⊢
  have heq : rationalZeroLocalCoeffDirection =
      closedPlaceDirections ∘ index := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact closedPlaceDirections_linearIndependent.comp index hindex

theorem rationalZeroLocalCoeffSpace_finrank :
    Module.finrank F₂ rationalZeroLocalCoeffSpace = 4 :=
  finrank_span_eq_card rationalZeroLocalCoeffDirection_linearIndependent

theorem rationalZeroLocalCoeffSpace_le_secant :
    rationalZeroLocalCoeffSpace ≤ rationalZeroSecantCoeffSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change rationalZeroSecantConstraint
      (rationalZeroLocalCoeffDirection i) = 0
  fin_cases i <;> ext k <;> fin_cases k <;>
    decide

/-- Rational evaluation together with the two degree-two norm directions. -/
def degreeTwoLocalCoeffDirection : Fin 5 → TargetCoeff :=
  ![closedPlaceDirections 0, closedPlaceDirections 1,
    closedPlaceDirections 2, closedPlaceDirections 6,
    closedPlaceDirections 7]

def degreeTwoLocalCoeffSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ (Set.range degreeTwoLocalCoeffDirection)

theorem degreeTwoLocalCoeffDirection_linearIndependent :
    LinearIndependent F₂ degreeTwoLocalCoeffDirection := by
  let index : Fin 5 → Fin 8 := ![0, 1, 2, 6, 7]
  have hindex : Function.Injective index := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [index] at h ⊢
  have heq : degreeTwoLocalCoeffDirection =
      closedPlaceDirections ∘ index := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact closedPlaceDirections_linearIndependent.comp index hindex

theorem degreeTwoLocalCoeffSpace_finrank :
    Module.finrank F₂ degreeTwoLocalCoeffSpace = 5 :=
  finrank_span_eq_card degreeTwoLocalCoeffDirection_linearIndependent

theorem degreeTwoLocalCoeffSpace_le_secant :
    degreeTwoLocalCoeffSpace ≤ degreeTwoSecantCoeffSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change degreeTwoSecantConstraint (degreeTwoLocalCoeffDirection i) = 0
  fin_cases i <;> ext k <;> fin_cases k <;>
    decide

/-! ## Quotient dimension supplied by the pivots -/

/-- If `A` lies in both a candidate coefficient space `S` and the quotient
subspace `D`, then quotienting `S` by `D` loses at least `finrank A`
dimensions. -/
theorem finrank_range_mkQ_domRestrict_le_sub
    {V : Type*} [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ V]
    (A S D : Submodule F₂ V) (hAS : A ≤ S) (hAD : A ≤ D) :
    Module.finrank F₂
        (LinearMap.range ((Submodule.mkQ D).domRestrict S)) ≤
      Module.finrank F₂ S - Module.finrank F₂ A := by
  let f := (Submodule.mkQ D).domRestrict S
  let A' : Submodule F₂ S := A.comap S.subtype
  have hAker : A' ≤ LinearMap.ker f := by
    intro x hx
    apply (LinearMap.mem_ker).2
    apply (Submodule.Quotient.mk_eq_zero D).2
    exact hAD hx
  have hArank : Module.finrank F₂ A' = Module.finrank F₂ A := by
    exact (Submodule.comapSubtypeEquivOfLe hAS).finrank_eq
  have hkerLower : Module.finrank F₂ A ≤
      Module.finrank F₂ (LinearMap.ker f) := by
    rw [← hArank]
    exact Submodule.finrank_mono hAker
  have hASrank : Module.finrank F₂ A ≤ Module.finrank F₂ S :=
    Submodule.finrank_mono hAS
  have hrank := f.finrank_range_add_finrank_ker
  change Module.finrank F₂ (LinearMap.range f) ≤
    Module.finrank F₂ S - Module.finrank F₂ A
  omega

/-- After quotienting by the rational evaluation and zero-jet directions,
the rational local secant space has dimension at most two. -/
theorem rationalZeroSecantQuotientRank_le_two
    (D : Submodule F₂ TargetCoeff)
    (hlocal : rationalZeroLocalCoeffSpace ≤ D) :
    Module.finrank F₂
        (LinearMap.range
          ((Submodule.mkQ D).domRestrict rationalZeroSecantCoeffSpace)) ≤ 2 := by
  have h := finrank_range_mkQ_domRestrict_le_sub
    rationalZeroLocalCoeffSpace rationalZeroSecantCoeffSpace D
    rationalZeroLocalCoeffSpace_le_secant hlocal
  rw [rationalZeroSecantCoeffSpace_finrank,
    rationalZeroLocalCoeffSpace_finrank] at h
  exact h

/-- After quotienting by the rational evaluation and norm directions, the
degree-two local secant space has dimension at most one. -/
theorem degreeTwoSecantQuotientRank_le_one
    (D : Submodule F₂ TargetCoeff)
    (hlocal : degreeTwoLocalCoeffSpace ≤ D) :
    Module.finrank F₂
        (LinearMap.range
          ((Submodule.mkQ D).domRestrict degreeTwoSecantCoeffSpace)) ≤ 1 := by
  have h := finrank_range_mkQ_domRestrict_le_sub
    degreeTwoLocalCoeffSpace degreeTwoSecantCoeffSpace D
    degreeTwoLocalCoeffSpace_le_secant hlocal
  rw [degreeTwoSecantCoeffSpace_finrank,
    degreeTwoLocalCoeffSpace_finrank] at h
  exact h

/-- Synthesis of a local affine Klein point as its canonical quotient lift
plus its target-plane translation. -/
theorem localTwoForm_closedPlaceLocalPoint
    (place : Fin 4) (q : LocalKleinParam) (z : LocalTargetParam) :
    localTwoForm place (closedPlaceLocalPoint place q z) =
      closedPlaceLift place q + targetTwo (closedPlaceTargetCoeff place z) := by
  rw [closedPlaceLocalPoint_eq_canonical_add_target]
  change localTwoFormLinear place
      (closedPlaceCanonicalCoord place q + closedPlaceTargetCoord place z) = _
  rw [(localTwoFormLinear place).map_add]
  change closedPlaceLift place q +
      localTwoForm place (closedPlaceTargetCoord place z) = _
  rw [← targetTwo_closedPlaceTargetCoeff]

/-- A local decomposable lift corrected by `c` is the rank-four secant
candidate whose Pfaffians provide the pivot equations. -/
def localSecantCandidate (place : Fin 4) (q : LocalKleinParam)
    (z : LocalTargetParam) (c : TargetCoeff) : TwoForm :=
  localTwoForm place (closedPlaceLocalPoint place q z) + targetTwo c

/-- Every two-wedge presentation of a local secant candidate supplies all
six-coordinate Pfaffian equations. -/
theorem localSecantCandidate_pfaffian
    (place : Fin 4) (q : LocalKleinParam) (z : LocalTargetParam)
    (c : TargetCoeff) (i j k l m n : Fin 10)
    (hsecant : ∃ u v x y : LinearForm,
      localSecantCandidate place q z c =
        squarefreeWedge u v + squarefreeWedge x y) :
    secantPfaffianValue (localSecantCandidate place q z c)
      i j k l m n = 0 :=
  secantPfaffianValue_eq_zero_of_two_decomposable
    (localSecantCandidate place q z c) i j k l m n hsecant

end

end N5
end UnrestrictedBooleanMul
