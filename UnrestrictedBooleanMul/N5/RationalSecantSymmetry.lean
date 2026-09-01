import UnrestrictedBooleanMul.N5.RationalPlaceSymmetry
import UnrestrictedBooleanMul.N5.LineSecantGifts

/-!
# Rational local secant pivots at all three places

The zero-place secant certificate is transported by the two algebraic
generators of the rational-place symmetry group.  This supplies the same
six-dimensional secant space, and hence the same two-dimensional quotient
bound, at the rational places one and infinity.  No effective-fiber atlas is
enumerated here.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The linear action induced on the nine target coefficients. -/
def rationalTargetCoeffLinear (θ : Fin 2) :
    TargetCoeff →ₗ[F₂] TargetCoeff where
  toFun := rationalTargetCoeffChange θ
  map_add' c d := by
    ext i
    fin_cases θ <;> fin_cases i <;>
      simp [rationalTargetCoeffChange] <;> ring
  map_smul' a c := by
    ext i
    fin_cases θ <;> fin_cases i <;>
      simp [rationalTargetCoeffChange, mul_add]

/-- Both rational-place generators are involutions on target coefficients. -/
theorem rationalTargetCoeffChange_involutive
    (θ : Fin 2) (c : TargetCoeff) :
    rationalTargetCoeffChange θ (rationalTargetCoeffChange θ c) = c := by
  ext i
  fin_cases θ <;> fin_cases i <;>
    simp [rationalTargetCoeffChange] <;>
    ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2]

theorem rationalTargetCoeffLinear_injective (θ : Fin 2) :
    Function.Injective (rationalTargetCoeffLinear θ) := by
  intro c d h
  have h' := congrArg (rationalTargetCoeffChange θ) h
  simpa [rationalTargetCoeffLinear,
    rationalTargetCoeffChange_involutive] using h'

/-- Pull the zero-place Pfaffian constraints back along one rational-place
symmetry.  For `θ = 0` this is the place-one secant space; for `θ = 1` it is
the place-infinity secant space. -/
def transformedRationalSecantConstraint (θ : Fin 2) :
    TargetCoeff →ₗ[F₂] (Fin 3 → F₂) :=
  rationalZeroSecantConstraint.comp (rationalTargetCoeffLinear θ)

def transformedRationalSecantCoeffSpace (θ : Fin 2) :
    Submodule F₂ TargetCoeff :=
  LinearMap.ker (transformedRationalSecantConstraint θ)

theorem transformedRationalSecantConstraint_surjective (θ : Fin 2) :
    Function.Surjective (transformedRationalSecantConstraint θ) := by
  intro t
  rcases rationalZeroSecantConstraint_surjective t with ⟨c, hc⟩
  refine ⟨rationalTargetCoeffChange θ c, ?_⟩
  change rationalZeroSecantConstraint
      (rationalTargetCoeffChange θ
        (rationalTargetCoeffChange θ c)) = t
  rw [rationalTargetCoeffChange_involutive]
  exact hc

/-- Every transported rational secant space has codimension three. -/
theorem transformedRationalSecantCoeffSpace_finrank (θ : Fin 2) :
    Module.finrank F₂ (transformedRationalSecantCoeffSpace θ) = 6 := by
  have h := (transformedRationalSecantConstraint θ).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (transformedRationalSecantConstraint θ) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (transformedRationalSecantConstraint_surjective θ)
  rw [hrange] at h
  have h' : 3 + Module.finrank F₂
      (LinearMap.ker (transformedRationalSecantConstraint θ)) = 9 := by
    simpa [TargetCoeff] using h
  change Module.finrank F₂
    (LinearMap.ker (transformedRationalSecantConstraint θ)) = 6
  omega

/-- The common rational evaluation directions together with the first jet at
the image of zero under `θ`. -/
def transformedRationalLocalCoeffDirection
    (θ : Fin 2) : Fin 4 → TargetCoeff :=
  match θ with
  | 0 => ![closedPlaceDirections 0, closedPlaceDirections 1,
      closedPlaceDirections 2, closedPlaceDirections 4]
  | 1 => ![closedPlaceDirections 0, closedPlaceDirections 1,
      closedPlaceDirections 2, closedPlaceDirections 5]

def transformedRationalLocalCoeffSpace (θ : Fin 2) :
    Submodule F₂ TargetCoeff :=
  Submodule.span F₂ (Set.range (transformedRationalLocalCoeffDirection θ))

theorem transformedRationalLocalCoeffDirection_linearIndependent (θ : Fin 2) :
    LinearIndependent F₂ (transformedRationalLocalCoeffDirection θ) := by
  let index : Fin 4 → Fin 8 :=
    match θ with
    | 0 => ![0, 1, 2, 4]
    | 1 => ![0, 1, 2, 5]
  have hindex : Function.Injective index := by
    intro i j h
    fin_cases θ <;> fin_cases i <;> fin_cases j <;>
      simp [index] at h ⊢
  have heq : transformedRationalLocalCoeffDirection θ =
      closedPlaceDirections ∘ index := by
    funext i
    fin_cases θ <;> fin_cases i <;> rfl
  rw [heq]
  exact closedPlaceDirections_linearIndependent.comp index hindex

theorem transformedRationalLocalCoeffSpace_finrank (θ : Fin 2) :
    Module.finrank F₂ (transformedRationalLocalCoeffSpace θ) = 4 :=
  finrank_span_eq_card
    (transformedRationalLocalCoeffDirection_linearIndependent θ)

theorem transformedRationalLocalCoeffSpace_le_secant (θ : Fin 2) :
    transformedRationalLocalCoeffSpace θ ≤
      transformedRationalSecantCoeffSpace θ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change transformedRationalSecantConstraint θ
      (transformedRationalLocalCoeffDirection θ i) = 0
  fin_cases θ <;> fin_cases i <;> ext k <;> fin_cases k <;>
    decide

theorem transformedRationalLocalCoeffSpace_le_localDisplacementCoeffSpace
    (Q : Submodule F₂ QuadraticQuotient) (θ : Fin 2)
    (hplace : IsRepresentedPlace Q (rationalPlacePerm θ 0)) :
    transformedRationalLocalCoeffSpace θ ≤ localDisplacementCoeffSpace Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  fin_cases θ <;> fin_cases i
  · change closedPlaceDirections 0 ∈ localDisplacementCoeffSpace Q
    exact closedPlaceDirection_mem_localDisplacementCoeffSpace Q 0 (by
      simp [IsActiveDisplacementDirection])
  · change closedPlaceDirections 1 ∈ localDisplacementCoeffSpace Q
    exact closedPlaceDirection_mem_localDisplacementCoeffSpace Q 1 (by
      simp [IsActiveDisplacementDirection])
  · change closedPlaceDirections 2 ∈ localDisplacementCoeffSpace Q
    exact closedPlaceDirection_mem_localDisplacementCoeffSpace Q 2 (by
      simp [IsActiveDisplacementDirection])
  · change closedPlaceDirections 4 ∈ localDisplacementCoeffSpace Q
    exact closedPlaceDirection_mem_localDisplacementCoeffSpace Q 4 (by
      simpa [rationalPlacePerm, IsActiveDisplacementDirection] using hplace)
  · change closedPlaceDirections 0 ∈ localDisplacementCoeffSpace Q
    exact closedPlaceDirection_mem_localDisplacementCoeffSpace Q 0 (by
      simp [IsActiveDisplacementDirection])
  · change closedPlaceDirections 1 ∈ localDisplacementCoeffSpace Q
    exact closedPlaceDirection_mem_localDisplacementCoeffSpace Q 1 (by
      simp [IsActiveDisplacementDirection])
  · change closedPlaceDirections 2 ∈ localDisplacementCoeffSpace Q
    exact closedPlaceDirection_mem_localDisplacementCoeffSpace Q 2 (by
      simp [IsActiveDisplacementDirection])
  · change closedPlaceDirections 5 ∈ localDisplacementCoeffSpace Q
    exact closedPlaceDirection_mem_localDisplacementCoeffSpace Q 5 (by
      simpa [rationalPlacePerm, IsActiveDisplacementDirection] using hplace)

/-- Transport of a normalized rational local secant back to the zero chart. -/
theorem transformed_normalizedRationalSecant_mem
    (θ : Fin 2) (place : Fin 4) (hplace : place ≠ 3)
    (hperm : rationalPlacePerm θ place = 0)
    (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (c : TargetCoeff)
    (hsecant : ∃ u v y z : LinearForm,
      closedPlaceLift place q + targetTwo c =
        squarefreeWedge u v + squarefreeWedge y z) :
    rationalTargetCoeffChange θ c ∈ rationalZeroSecantCoeffSpace := by
  rcases hsecant with ⟨u, v, y, z, hsecant⟩
  have htransport := congrArg (rationalPlaceTwoFormLinear θ) hsecant
  have htransport' :
      closedPlaceLift 0 q + targetTwo (rationalTargetCoeffChange θ c) =
        squarefreeWedge (rationalPlaceLinear θ u)
            (rationalPlaceLinear θ v) +
          squarefreeWedge (rationalPlaceLinear θ y)
            (rationalPlaceLinear θ z) := by
    simpa only [map_add, rationalPlaceTwoFormLinear_rationalLift θ place hplace,
      hperm, rationalPlaceTwoFormLinear_targetTwo,
      rationalPlaceTwoFormLinear_squarefreeWedge'] using htransport
  exact rationalZero_normalizedLocalSecant_mem q hq
    (rationalTargetCoeffChange θ c)
    ⟨_, _, _, _, htransport'⟩

/-- A rational local secant remains a rational local secant after either
generator.  This is the reusable algebraic transport behind the fourth
local pivot below. -/
theorem transport_normalizedRationalSecant
    (θ : Fin 2) (place : Fin 4) (hplace : place ≠ 3)
    (q : LocalKleinParam) (c : TargetCoeff)
    (hsecant : ∃ u v y z : LinearForm,
      closedPlaceLift place q + targetTwo c =
        squarefreeWedge u v + squarefreeWedge y z) :
    ∃ u v y z : LinearForm,
      closedPlaceLift (rationalPlacePerm θ place) q +
          targetTwo (rationalTargetCoeffChange θ c) =
        squarefreeWedge u v + squarefreeWedge y z := by
  rcases hsecant with ⟨u, v, y, z, hsecant⟩
  have htransport := congrArg (rationalPlaceTwoFormLinear θ) hsecant
  refine ⟨rationalPlaceLinear θ u, rationalPlaceLinear θ v,
    rationalPlaceLinear θ y, rationalPlaceLinear θ z, ?_⟩
  simpa only [map_add, rationalPlaceTwoFormLinear_rationalLift θ place hplace,
    rationalPlaceTwoFormLinear_targetTwo,
    rationalPlaceTwoFormLinear_squarefreeWedge'] using htransport

/-! ## The fourth symmetry pivot -/

/-- Four independent rational secant constraints.  The first three are the
direct zero-chart constraints; the last is supplied by the other symmetry
word carrying the same rational place to zero. -/
def strongRationalSecantConstraint (place : Fin 3) :
    TargetCoeff →ₗ[F₂] (Fin 4 → F₂) where
  toFun c := match place with
    | 0 => ![c 3 + c 5, c 4 + c 6,
        c 4 + c 5 + c 6 + c 7, c 4 + c 5]
    | 1 => ![c 2 + c 3 + c 4 + c 5, c 2 + c 6,
        c 3 + c 7, c 1 + c 5]
    | 2 => ![c 3 + c 5, c 2 + c 4,
        c 1 + c 2 + c 3 + c 4, c 3 + c 4]
  map_add' c d := by
    ext i
    fin_cases place <;> fin_cases i <;> simp <;> ring
  map_smul' a c := by
    ext i
    fin_cases place <;> fin_cases i <;> simp [mul_add]

def strongRationalSecantCoeffSpace (place : Fin 3) :
    Submodule F₂ TargetCoeff :=
  LinearMap.ker (strongRationalSecantConstraint place)

/-- Explicit right inverse of the four rational constraints. -/
def strongRationalSecantConstraintSection (place : Fin 3) :
    (Fin 4 → F₂) →ₗ[F₂] TargetCoeff where
  toFun t := match place with
    | 0 => ![0, 0, 0, t 0 + t 1 + t 2,
        t 1 + t 2 + t 3, t 1 + t 2, t 2 + t 3, 0, 0]
    | 1 => ![0, t 3, t 1, t 2, t 0 + t 1 + t 2,
        0, 0, 0, 0]
    | 2 => ![0, t 0 + t 1 + t 2, t 0 + t 1 + t 3, t 0,
        t 0 + t 3, 0, 0, 0, 0]
  map_add' t u := by
    ext i
    fin_cases place <;> fin_cases i <;> simp <;> ring
  map_smul' a t := by
    ext i
    fin_cases place <;> fin_cases i <;> simp [mul_add]

theorem strongRationalSecantConstraint_section
    (place : Fin 3) (t : Fin 4 → F₂) :
    strongRationalSecantConstraint place
        (strongRationalSecantConstraintSection place t) = t := by
  ext i
  fin_cases place <;> fin_cases i <;>
    simp [strongRationalSecantConstraint,
      strongRationalSecantConstraintSection] <;>
    ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.three_eq_one_f2,
      N3Certificate.four_eq_zero_f2]

theorem strongRationalSecantConstraint_surjective (place : Fin 3) :
    Function.Surjective (strongRationalSecantConstraint place) := by
  intro t
  exact ⟨strongRationalSecantConstraintSection place t,
    strongRationalSecantConstraint_section place t⟩

/-- The symmetry-complete rational secant space has dimension five. -/
theorem strongRationalSecantCoeffSpace_finrank (place : Fin 3) :
    Module.finrank F₂ (strongRationalSecantCoeffSpace place) = 5 := by
  have h := (strongRationalSecantConstraint place).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (strongRationalSecantConstraint place) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (strongRationalSecantConstraint_surjective place)
  rw [hrange] at h
  have h' : 4 + Module.finrank F₂
      (LinearMap.ker (strongRationalSecantConstraint place)) = 9 := by
    simpa [TargetCoeff] using h
  change Module.finrank F₂
    (LinearMap.ker (strongRationalSecantConstraint place)) = 5
  omega

/-- Regard one of the three rational labels as a label among all four closed
places. -/
def rationalPlaceLabel (place : Fin 3) : Fin 4 :=
  ⟨place.1, by omega⟩

/-- Applying both symmetry words carrying a rational place to zero exposes
four independent Pfaffian pivots. -/
theorem strongRational_normalizedLocalSecant_mem
    (place : Fin 3) (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (c : TargetCoeff)
    (hsecant : ∃ u v y z : LinearForm,
      closedPlaceLift (rationalPlaceLabel place) q + targetTwo c =
        squarefreeWedge u v + squarefreeWedge y z) :
    c ∈ strongRationalSecantCoeffSpace place := by
  fin_cases place
  · have hb := rationalZero_normalizedLocalSecant_mem q hq c hsecant
    have h₁ := transport_normalizedRationalSecant
      0 0 (by decide) q c hsecant
    have h₂ := transport_normalizedRationalSecant
      1 1 (by decide) q (rationalTargetCoeffChange 0 c) h₁
    have h₃ := transport_normalizedRationalSecant
      0 1 (by decide) q
        (rationalTargetCoeffChange 1 (rationalTargetCoeffChange 0 c)) h₂
    have he := rationalZero_normalizedLocalSecant_mem q hq
      (rationalTargetCoeffChange 0
        (rationalTargetCoeffChange 1 (rationalTargetCoeffChange 0 c))) h₃
    change rationalZeroSecantConstraint c = 0 at hb
    change rationalZeroSecantConstraint
      (rationalTargetCoeffChange 0
        (rationalTargetCoeffChange 1 (rationalTargetCoeffChange 0 c))) = 0 at he
    change strongRationalSecantConstraint 0 c = 0
    ext i
    fin_cases i
    · simpa [strongRationalSecantConstraint,
        rationalZeroSecantConstraint] using congrFun hb 0
    · simpa [strongRationalSecantConstraint,
        rationalZeroSecantConstraint] using congrFun hb 1
    · simpa [strongRationalSecantConstraint,
        rationalZeroSecantConstraint] using congrFun hb 2
    · have h := congrFun he 2
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 4 + c 5 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.three_eq_one_f2,
        N3Certificate.four_eq_zero_f2,
        N3Certificate.six_eq_zero_f2,
        N3Certificate.eight_eq_zero_f2,
        show (9 : F₂) = 1 by decide,
        show (18 : F₂) = 0 by decide] using h
  · have h₁ := transport_normalizedRationalSecant
      0 1 (by decide) q c hsecant
    have hb := rationalZero_normalizedLocalSecant_mem q hq
      (rationalTargetCoeffChange 0 c) h₁
    have h₂ := transport_normalizedRationalSecant
      1 1 (by decide) q c hsecant
    have h₃ := transport_normalizedRationalSecant
      0 1 (by decide) q (rationalTargetCoeffChange 1 c) h₂
    have he := rationalZero_normalizedLocalSecant_mem q hq
      (rationalTargetCoeffChange 0 (rationalTargetCoeffChange 1 c)) h₃
    change rationalZeroSecantConstraint (rationalTargetCoeffChange 0 c) = 0 at hb
    change rationalZeroSecantConstraint
      (rationalTargetCoeffChange 0 (rationalTargetCoeffChange 1 c)) = 0 at he
    change strongRationalSecantConstraint 1 c = 0
    ext i
    fin_cases i
    · have h := congrFun hb 0
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 2 + c 3 + c 4 + c 5 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2] using h
    · have h := congrFun hb 1
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 2 + c 6 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2] using h
    · have h := congrFun hb 2
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 3 + c 7 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2] using h
    · have h := congrFun he 2
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 1 + c 5 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2] using h
  · have h₁ := transport_normalizedRationalSecant
      1 2 (by decide) q c hsecant
    have hb := rationalZero_normalizedLocalSecant_mem q hq
      (rationalTargetCoeffChange 1 c) h₁
    have h₂ := transport_normalizedRationalSecant
      0 2 (by decide) q c hsecant
    have h₃ := transport_normalizedRationalSecant
      1 2 (by decide) q (rationalTargetCoeffChange 0 c) h₂
    have he := rationalZero_normalizedLocalSecant_mem q hq
      (rationalTargetCoeffChange 1 (rationalTargetCoeffChange 0 c)) h₃
    change rationalZeroSecantConstraint (rationalTargetCoeffChange 1 c) = 0 at hb
    change rationalZeroSecantConstraint
      (rationalTargetCoeffChange 1 (rationalTargetCoeffChange 0 c)) = 0 at he
    change strongRationalSecantConstraint 2 c = 0
    ext i
    fin_cases i
    · have h := congrFun hb 0
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 3 + c 5 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2] using h
    · have h := congrFun hb 1
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 2 + c 4 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2] using h
    · have h := congrFun hb 2
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 1 + c 2 + c 3 + c 4 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2] using h
    · have h := congrFun he 2
      simp [rationalZeroSecantConstraint, rationalTargetCoeffChange] at h
      change c 3 + c 4 = 0
      ring_nf at h ⊢
      simpa [N3Certificate.two_eq_zero_f2,
        N3Certificate.four_eq_zero_f2] using h

/-- The common rational evaluation block and the selected first jet. -/
def strongRationalLocalCoeffDirection (place : Fin 3) :
    Fin 4 → TargetCoeff :=
  match place with
  | 0 => rationalZeroLocalCoeffDirection
  | 1 => transformedRationalLocalCoeffDirection 0
  | 2 => transformedRationalLocalCoeffDirection 1

def strongRationalLocalCoeffSpace (place : Fin 3) :
    Submodule F₂ TargetCoeff :=
  Submodule.span F₂ (Set.range (strongRationalLocalCoeffDirection place))

theorem strongRationalLocalCoeffSpace_finrank (place : Fin 3) :
    Module.finrank F₂ (strongRationalLocalCoeffSpace place) = 4 := by
  fin_cases place
  · exact rationalZeroLocalCoeffSpace_finrank
  · exact transformedRationalLocalCoeffSpace_finrank 0
  · exact transformedRationalLocalCoeffSpace_finrank 1

theorem strongRationalLocalCoeffSpace_le_secant (place : Fin 3) :
    strongRationalLocalCoeffSpace place ≤
      strongRationalSecantCoeffSpace place := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change strongRationalSecantConstraint place
      (strongRationalLocalCoeffDirection place i) = 0
  fin_cases place <;> fin_cases i <;> ext k <;> fin_cases k <;>
    decide

theorem strongRationalLocalCoeffSpace_le_localDisplacementCoeffSpace
    (Q : Submodule F₂ QuadraticQuotient) (place : Fin 3)
    (hplace : IsRepresentedPlace Q (rationalPlaceLabel place)) :
    strongRationalLocalCoeffSpace place ≤ localDisplacementCoeffSpace Q := by
  fin_cases place
  · exact rationalZeroLocalCoeffSpace_le_localDisplacementCoeffSpace Q hplace
  · exact transformedRationalLocalCoeffSpace_le_localDisplacementCoeffSpace
      Q 0 hplace
  · exact transformedRationalLocalCoeffSpace_le_localDisplacementCoeffSpace
      Q 1 hplace

/-- Every pointed Fano-line gift through a rational point satisfies all four
symmetry-complete secant pivots. -/
theorem fanoLine_strongRational_gift_mem
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support)
    (place : Fin 3) (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint (rationalPlaceLabel place) q) :
    sparseRelationGiftCoeff Q r.1 ∈
      strongRationalSecantCoeffSpace place := by
  let g := sparseRelationGiftCoeff Q r.1
  have hxProjection : quadraticQuotientProjection (populatedLift x) =
      closedPlaceQuotientPoint (rationalPlaceLabel place) q :=
    (populatedLift_projection x).trans hxPoint
  rcases exists_closedPlaceLift_add_target_of_projection_eq
      (rationalPlaceLabel place) q (populatedLift x) hxProjection with ⟨a, ha⟩
  have haSecant : ∃ u v y z : LinearForm,
      closedPlaceLift (rationalPlaceLabel place) q + targetTwo a =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases (populatedLift_mem_fiber x).1 with ⟨u, v, huv⟩
    refine ⟨u, v, 0, 0, ?_⟩
    rw [← ha, huv]
    simp
  have haMem : a ∈ strongRationalSecantCoeffSpace place :=
    strongRational_normalizedLocalSecant_mem place q hq a haSecant
  have hagSecant : ∃ u v y z : LinearForm,
      closedPlaceLift (rationalPlaceLabel place) q + targetTwo (a + g) =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases fanoLine_gift_has_two_wedge_secant Q r x hx with
      ⟨u, v, y, z, hline⟩
    refine ⟨u, v, y, z, ?_⟩
    change closedPlaceLift (rationalPlaceLabel place) q +
      targetTwoLinear (a + g) = _
    rw [targetTwoLinear.map_add, ← add_assoc]
    change populatedLift x =
      closedPlaceLift (rationalPlaceLabel place) q + targetTwoLinear a at ha
    rw [← ha]
    change populatedLift x +
      targetTwoLinear (sparseRelationGiftCoeff Q r.1) = _ at hline
    simpa only [g] using hline
  have hagMem : a + g ∈ strongRationalSecantCoeffSpace place :=
    strongRational_normalizedLocalSecant_mem
      place q hq (a + g) hagSecant
  have hsum := (strongRationalSecantCoeffSpace place).add_mem hagMem haMem
  have hcancel : (a + g) + a = g := by
    funext i
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  rw [hcancel] at hsum
  exact hsum

theorem fanoLineGiftCoeffSpaceThrough_strongRational_le
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q)
    (place : Fin 3) (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint (rationalPlaceLabel place) q) :
    fanoLineGiftCoeffSpaceThrough Q x ≤
      strongRationalSecantCoeffSpace place := by
  apply Submodule.span_le.mpr
  rintro c ⟨r, hx, rfl⟩
  exact fanoLine_strongRational_gift_mem
    Q r x hx place q hq hxPoint

/-- After intrinsic rational displacement is removed, pointed line gifts
span at most one dimension. -/
theorem fanoLineGiftCoeffSpaceThrough_strongRational_quotientRank_le_one
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q)
    (place : Fin 3) (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint (rationalPlaceLabel place) q)
    (hplace : IsRepresentedPlace Q (rationalPlaceLabel place)) :
    Module.finrank F₂ (LinearMap.range
        ((Submodule.mkQ (localDisplacementCoeffSpace Q)).domRestrict
          (fanoLineGiftCoeffSpaceThrough Q x))) ≤ 1 := by
  refine (finrank_range_mkQ_domRestrict_mono
    (fanoLineGiftCoeffSpaceThrough Q x)
    (strongRationalSecantCoeffSpace place)
    (localDisplacementCoeffSpace Q)
    (fanoLineGiftCoeffSpaceThrough_strongRational_le
      Q x place q hq hxPoint)).trans ?_
  have h := finrank_range_mkQ_domRestrict_le_sub
    (strongRationalLocalCoeffSpace place)
    (strongRationalSecantCoeffSpace place)
    (localDisplacementCoeffSpace Q)
    (strongRationalLocalCoeffSpace_le_secant place)
    (strongRationalLocalCoeffSpace_le_localDisplacementCoeffSpace
      Q place hplace)
  rw [strongRationalSecantCoeffSpace_finrank,
    strongRationalLocalCoeffSpace_finrank] at h
  exact h

/-- Every Fano-line gift through a rational point at place one or infinity
lies in the corresponding transported secant space. -/
theorem fanoLine_transformedRational_gift_mem
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation (populatedQuotientPoint (Q := Q)))
    (x : PopulatedPoint Q) (hx : x ∈ r.support)
    (θ : Fin 2) (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint (rationalPlacePerm θ 0) q) :
    sparseRelationGiftCoeff Q r.1 ∈
      transformedRationalSecantCoeffSpace θ := by
  let place := rationalPlacePerm θ 0
  let g := sparseRelationGiftCoeff Q r.1
  have hplace : place ≠ 3 := by
    fin_cases θ <;> decide
  have hperm : rationalPlacePerm θ place = 0 := by
    fin_cases θ <;> decide
  have hxProjection : quadraticQuotientProjection (populatedLift x) =
      closedPlaceQuotientPoint place q :=
    (populatedLift_projection x).trans hxPoint
  rcases exists_closedPlaceLift_add_target_of_projection_eq
      place q (populatedLift x) hxProjection with ⟨a, ha⟩
  have haSecant : ∃ u v y z : LinearForm,
      closedPlaceLift place q + targetTwo a =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases (populatedLift_mem_fiber x).1 with ⟨u, v, huv⟩
    refine ⟨u, v, 0, 0, ?_⟩
    rw [← ha, huv]
    simp
  have haMem : rationalTargetCoeffChange θ a ∈
      rationalZeroSecantCoeffSpace :=
    transformed_normalizedRationalSecant_mem
      θ place hplace hperm q hq a haSecant
  have hagSecant : ∃ u v y z : LinearForm,
      closedPlaceLift place q + targetTwo (a + g) =
        squarefreeWedge u v + squarefreeWedge y z := by
    rcases fanoLine_gift_has_two_wedge_secant Q r x hx with
      ⟨u, v, y, z, hline⟩
    refine ⟨u, v, y, z, ?_⟩
    change closedPlaceLift place q + targetTwoLinear (a + g) = _
    rw [targetTwoLinear.map_add, ← add_assoc]
    change populatedLift x =
      closedPlaceLift place q + targetTwoLinear a at ha
    rw [← ha]
    change populatedLift x +
      targetTwoLinear (sparseRelationGiftCoeff Q r.1) = _ at hline
    simpa only [g] using hline
  have hagMem : rationalTargetCoeffChange θ (a + g) ∈
      rationalZeroSecantCoeffSpace :=
    transformed_normalizedRationalSecant_mem
      θ place hplace hperm q hq (a + g) hagSecant
  have hsum := rationalZeroSecantCoeffSpace.add_mem hagMem haMem
  have hcancel : rationalTargetCoeffChange θ (a + g) +
      rationalTargetCoeffChange θ a = rationalTargetCoeffChange θ g := by
    rw [show rationalTargetCoeffChange θ (a + g) =
        rationalTargetCoeffChange θ a + rationalTargetCoeffChange θ g by
      exact (rationalTargetCoeffLinear θ).map_add a g]
    funext i
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  rw [hcancel] at hsum
  exact hsum

theorem fanoLineGiftCoeffSpaceThrough_transformedRational_le
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q)
    (θ : Fin 2) (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint (rationalPlacePerm θ 0) q) :
    fanoLineGiftCoeffSpaceThrough Q x ≤
      transformedRationalSecantCoeffSpace θ := by
  apply Submodule.span_le.mpr
  rintro c ⟨r, hx, rfl⟩
  exact fanoLine_transformedRational_gift_mem
    Q r x hx θ q hq hxPoint

theorem fanoLineGiftCoeffSpaceThrough_transformedRational_quotientRank_le_two
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q)
    (θ : Fin 2) (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x =
      closedPlaceQuotientPoint (rationalPlacePerm θ 0) q)
    (hplace : IsRepresentedPlace Q (rationalPlacePerm θ 0)) :
    Module.finrank F₂ (LinearMap.range
        ((Submodule.mkQ (localDisplacementCoeffSpace Q)).domRestrict
          (fanoLineGiftCoeffSpaceThrough Q x))) ≤ 2 := by
  refine (finrank_range_mkQ_domRestrict_mono
    (fanoLineGiftCoeffSpaceThrough Q x)
    (transformedRationalSecantCoeffSpace θ)
    (localDisplacementCoeffSpace Q)
    (fanoLineGiftCoeffSpaceThrough_transformedRational_le
      Q x θ q hq hxPoint)).trans ?_
  have h := finrank_range_mkQ_domRestrict_le_sub
    (transformedRationalLocalCoeffSpace θ)
    (transformedRationalSecantCoeffSpace θ)
    (localDisplacementCoeffSpace Q)
    (transformedRationalLocalCoeffSpace_le_secant θ)
    (transformedRationalLocalCoeffSpace_le_localDisplacementCoeffSpace
      Q θ hplace)
  rw [transformedRationalSecantCoeffSpace_finrank,
    transformedRationalLocalCoeffSpace_finrank] at h
  exact h

end

end N5
end UnrestrictedBooleanMul
