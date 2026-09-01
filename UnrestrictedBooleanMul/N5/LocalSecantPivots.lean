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

/-- The actual zero-place target-plane translation is among the four local
rational directions used in the quotient pivot. -/
theorem closedPlaceTargetCoeff_zero_mem_rationalZeroLocalCoeffSpace
    (z : LocalTargetParam) :
    closedPlaceTargetCoeff 0 z ∈ rationalZeroLocalCoeffSpace := by
  have h0 : rZeroCoeff ∈ rationalZeroLocalCoeffSpace := by
    have h := Submodule.subset_span
      (R := F₂) (s := Set.range rationalZeroLocalCoeffDirection)
      (Set.mem_range_self (0 : Fin 4))
    change rZeroCoeff ∈
      Submodule.span F₂ (Set.range rationalZeroLocalCoeffDirection)
    simpa [rationalZeroLocalCoeffDirection, closedPlaceDirections] using h
  have h1 : outsideHankelWord 0 ∈ rationalZeroLocalCoeffSpace := by
    have h := Submodule.subset_span
      (R := F₂) (s := Set.range rationalZeroLocalCoeffDirection)
      (Set.mem_range_self (3 : Fin 4))
    change outsideHankelWord 0 ∈
      Submodule.span F₂ (Set.range rationalZeroLocalCoeffDirection)
    simpa [rationalZeroLocalCoeffDirection, closedPlaceDirections,
      outsideHankelWord, rankTwoHankelWord] using h
  simpa [closedPlaceTargetCoeff] using
    rationalZeroLocalCoeffSpace.add_mem
      (rationalZeroLocalCoeffSpace.smul_mem (z 0) h0)
      (rationalZeroLocalCoeffSpace.smul_mem (z 1) h1)

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

/-- Move the local target translation into the single target-coefficient
correction.  This is the coefficient normal form used by the symbolic
Pfaffian certificates below. -/
theorem localSecantCandidate_eq_lift_add_target
    (place : Fin 4) (q : LocalKleinParam)
    (z : LocalTargetParam) (c : TargetCoeff) :
    localSecantCandidate place q z c =
      closedPlaceLift place q +
        targetTwo (closedPlaceTargetCoeff place z + c) := by
  rw [localSecantCandidate, localTwoForm_closedPlaceLocalPoint]
  change closedPlaceLift place q +
      targetTwoLinear (closedPlaceTargetCoeff place z) + targetTwoLinear c =
    closedPlaceLift place q +
      targetTwoLinear (closedPlaceTargetCoeff place z + c)
  rw [targetTwoLinear.map_add]
  exact add_assoc _ _ _

/-- Off-diagonal coefficient of a normalized local secant candidate. -/
theorem ambientTwoCoeff_localSecantCandidate
    (place : Fin 4) (q : LocalKleinParam)
    (z : LocalTargetParam) (c : TargetCoeff)
    (i j : Fin 10) (hij : i ≠ j) :
    ambientTwoCoeff (localSecantCandidate place q z c) i j =
      explicitLocalLiftCoeff place q i j +
        explicitTargetCoeff (closedPlaceTargetCoeff place z + c) i j := by
  rw [localSecantCandidate_eq_lift_add_target, ambientTwoCoeff_add]
  simp [ambientTwoCoeff, hij,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff]

/-- Pfaffian equation for a canonical local lift plus one target word. -/
def normalizedLocalSecantEquation
    (place : Fin 4) (q : LocalKleinParam) (c : TargetCoeff)
    (i j k l m n : Fin 10) : F₂ :=
  secantPfaffianValue (closedPlaceLift place q + targetTwo c)
    i j k l m n

/-- A normalized two-wedge presentation annihilates every selected
six-coordinate equation. -/
theorem normalizedLocalSecantEquation_eq_zero
    (place : Fin 4) (q : LocalKleinParam) (c : TargetCoeff)
    (i j k l m n : Fin 10)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift place q + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    normalizedLocalSecantEquation place q c i j k l m n = 0 := by
  unfold normalizedLocalSecantEquation
  exact secantPfaffianValue_eq_zero_of_two_decomposable
    (closedPlaceLift place q + targetTwo c) i j k l m n hsecant

/-- Any lift with the named closed-place quotient differs from the canonical
local lift by a unique target word. -/
theorem exists_closedPlaceLift_add_target_of_projection_eq
    (place : Fin 4) (q : LocalKleinParam) (p : TwoForm)
    (hp : quadraticQuotientProjection p =
      closedPlaceQuotientPoint place q) :
    ∃ c : TargetCoeff,
      p = closedPlaceLift place q + targetTwo c := by
  have hzero : quadraticQuotientProjection
      (p - closedPlaceLift place q) = 0 := by
    rw [map_sub, hp]
    simp [closedPlaceQuotientPoint]
  have htarget : p - closedPlaceLift place q ∈ targetTwoSpace :=
    (quadraticQuotientProjection_eq_zero_iff _).1 hzero
  rcases htarget with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  change p = closedPlaceLift place q + targetTwoLinear c
  rw [hc]
  module

private theorem secant_pow_three_f2 (x : F₂) : x ^ 3 = x := by
  rw [show 3 = 2 + 1 by omega, pow_succ, N3Certificate.pow_two_f2,
    N3Certificate.mul_self_f2]

private theorem secant_pow_four_f2 (x : F₂) : x ^ 4 = x := by
  rw [show 4 = 3 + 1 by omega, pow_succ, secant_pow_three_f2,
    N3Certificate.mul_self_f2]

private theorem secant_five_eq_one_f2 : (5 : F₂) = 1 := by decide
private theorem secant_three_eq_one_f2 : (3 : F₂) = 1 := by decide
private theorem secant_ten_eq_zero_f2 : (10 : F₂) = 0 := by decide
private theorem secant_twelve_eq_zero_f2 : (12 : F₂) = 0 := by decide
private theorem secant_thirteen_eq_one_f2 : (13 : F₂) = 1 := by decide
private theorem secant_fourteen_eq_zero_f2 : (14 : F₂) = 0 := by decide
private theorem secant_sixteen_eq_zero_f2 : (16 : F₂) = 0 := by decide
private theorem secant_eighteen_eq_zero_f2 : (18 : F₂) = 0 := by decide
private theorem secant_twenty_eq_zero_f2 : (20 : F₂) = 0 := by decide
private theorem secant_twenty_two_eq_zero_f2 : (22 : F₂) = 0 := by decide
private theorem secant_twenty_four_eq_zero_f2 : (24 : F₂) = 0 := by decide
private theorem secant_twenty_eight_eq_zero_f2 : (28 : F₂) = 0 := by decide
private theorem secant_thirty_eq_zero_f2 : (30 : F₂) = 0 := by decide
private theorem secant_thirty_two_eq_zero_f2 : (32 : F₂) = 0 := by decide
private theorem secant_forty_eq_zero_f2 : (40 : F₂) = 0 := by decide
private theorem secant_forty_four_eq_zero_f2 : (44 : F₂) = 0 := by decide
private theorem secant_fifty_two_eq_zero_f2 : (52 : F₂) = 0 := by decide

set_option maxRecDepth 10000 in
/-- The first rational secant constraint on the `q₂=1` effectiveness
chart. -/
theorem rationalA_secant_constraint_zero_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) :
    c 3 + c 5 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 0
        (rationalEffectiveA q0 q1 q3) c i j k l m n
      c 6 * E 0 1 2 5 8 9 +
      c 1 * E 0 1 2 6 7 9 +
      c 7 * E 0 1 3 5 7 8 +
      c 6 * E 0 1 3 5 7 9 +
      c 1 * E 0 1 3 6 7 8 +
      c 7 * E 0 1 3 6 7 8 +
      E 0 1 3 6 7 9 +
      E 0 1 3 6 8 9 +
      c 4 * E 0 1 3 6 8 9 +
      c 5 * E 0 1 3 6 8 9 +
      E 0 1 4 6 7 8 +
      c 6 * E 0 1 4 6 7 8 +
      c 4 * E 0 2 3 5 8 9 +
      c 5 * E 0 2 3 6 7 8 +
      E 1 2 3 5 6 7 +
      c 2 * E 1 2 3 5 7 9 +
      c 3 * E 1 2 3 5 8 9 +
      c 2 * E 1 2 3 6 7 8 +
      E 1 2 3 7 8 9 +
      c 3 * E 1 2 3 7 8 9 +
      c 4 * E 1 2 4 6 7 8 +
      c 2 * E 1 3 4 5 6 8 +
      c 5 * E 2 3 4 5 6 7 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    rationalEffectiveA, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- The middle rational secant constraint on the `q₂=1` effectiveness
chart, as a compact Boolean-ideal combination of eleven Pfaffians. -/
theorem rationalA_secant_constraint_one_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) :
    c 4 + c 6 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 0
        (rationalEffectiveA q0 q1 q3) c i j k l m n
      c 7 * E 0 1 2 6 7 9 +
      c 2 * E 0 1 2 7 8 9 +
      c 5 * E 0 1 2 7 8 9 +
      c 8 * E 0 1 2 7 8 9 +
      c 6 * E 0 1 4 6 7 8 +
      c 4 * E 0 2 3 6 8 9 +
      c 2 * E 1 2 3 6 7 8 +
      c 8 * E 1 2 3 6 7 8 +
      E 2 3 4 5 6 7 +
      c 2 * E 2 3 4 6 7 8 +
      E 2 3 4 7 8 9 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    rationalEffectiveA, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- The third rational secant constraint on the `q₂=1` effectiveness
chart. -/
theorem rationalA_secant_constraint_two_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) :
    c 4 + c 5 + c 6 + c 7 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 0
        (rationalEffectiveA q0 q1 q3) c i j k l m n
      c 8 * E 0 1 2 6 7 8 +
      E 0 1 2 6 7 9 +
      c 8 * E 0 1 2 7 8 9 +
      E 0 1 3 6 7 8 +
      c 6 * E 0 1 3 6 7 9 +
      c 4 * E 0 2 3 6 8 9 +
      c 2 * E 0 2 3 7 8 9 +
      c 3 * E 0 2 3 7 8 9 +
      E 0 3 4 7 8 9 +
      c 5 * E 1 2 3 5 8 9 +
      c 5 * E 1 2 3 6 7 8 +
      c 5 * E 1 2 3 6 7 9 +
      c 6 * E 1 2 3 6 7 9 +
      c 7 * E 1 2 3 6 8 9 +
      c 2 * E 1 2 3 7 8 9 +
      c 4 * E 1 2 4 6 7 8 +
      c 6 * E 1 2 4 6 7 9 +
      c 6 * E 1 2 4 7 8 9 +
      c 6 * E 1 3 4 5 6 7 +
      c 4 * E 1 3 4 5 6 9 +
      c 5 * E 1 3 4 5 7 8 +
      c 3 * E 1 3 4 5 7 9 +
      c 2 * E 1 3 4 6 7 8 +
      E 1 3 4 6 8 9 +
      c 6 * E 1 3 4 6 8 9 +
      c 6 * E 2 3 4 5 6 8 +
      c 2 * E 2 3 4 5 7 9 +
      c 6 * E 2 3 4 5 8 9 +
      c 3 * E 2 3 4 6 7 8 +
      c 7 * E 2 3 4 6 7 8 +
      q1 * E 2 3 4 6 7 9 +
      c 5 * E 2 3 4 6 7 9 +
      c 4 * E 2 3 4 7 8 9 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    rationalEffectiveA, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- The first rational secant constraint on the `q₁=1,q₂=0` chart. -/
theorem rationalD_secant_constraint_zero_identity
    (q0 q3 : F₂) (c : TargetCoeff) :
    c 3 + c 5 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 0
        (rationalEffectiveD q0 q3) c i j k l m n
      c 5 * E 0 1 2 5 6 9 +
      c 3 * E 0 1 2 5 8 9 +
      c 1 * E 0 1 3 5 6 9 +
      c 5 * E 0 1 3 5 8 9 +
      c 5 * E 0 1 4 5 6 7 +
      c 1 * E 0 1 4 5 6 8 +
      c 3 * E 0 2 3 5 6 9 +
      c 5 * E 0 2 3 6 7 8 +
      c 3 * E 0 2 4 5 6 8 +
      c 6 * E 0 3 4 5 6 7 +
      c 4 * E 0 3 4 5 7 8 +
      E 1 2 3 5 6 7 +
      c 4 * E 1 2 3 5 7 9 +
      c 1 * E 2 3 4 6 7 8 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    rationalEffectiveD, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- The middle rational secant constraint on the `q₁=1,q₂=0` chart. -/
theorem rationalD_secant_constraint_one_identity
    (q0 q3 : F₂) (c : TargetCoeff) :
    c 4 + c 6 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 0
        (rationalEffectiveD q0 q3) c i j k l m n
      c 2 * E 0 1 2 6 8 9 +
      c 8 * E 0 1 2 6 8 9 +
      c 5 * E 0 1 3 6 7 9 +
      c 2 * E 1 2 3 5 7 8 +
      E 1 2 3 6 7 8 +
      c 5 * E 1 2 4 5 6 8 +
      E 1 2 4 6 8 9 +
      c 8 * E 1 3 4 5 6 7 +
      E 2 3 4 5 7 9 +
      E 2 3 4 7 8 9 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    rationalEffectiveD, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- The third rational secant constraint on the `q₁=1,q₂=0` chart. -/
theorem rationalD_secant_constraint_two_identity
    (q0 q3 : F₂) (c : TargetCoeff) :
    c 4 + c 5 + c 6 + c 7 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 0
        (rationalEffectiveD q0 q3) c i j k l m n
      c 7 * E 0 1 2 6 7 8 +
      c 2 * E 0 1 3 6 7 9 +
      E 0 1 3 7 8 9 +
      c 2 * E 0 1 4 6 7 8 +
      c 5 * E 0 1 4 7 8 9 +
      c 6 * E 0 3 4 6 7 8 +
      c 5 * E 0 3 4 6 7 9 +
      c 8 * E 0 3 4 6 7 9 +
      c 7 * E 0 3 4 6 8 9 +
      c 3 * E 1 2 3 5 8 9 +
      c 6 * E 1 2 3 5 8 9 +
      c 3 * E 1 2 3 6 8 9 +
      E 1 2 3 7 8 9 +
      c 2 * E 1 2 3 7 8 9 +
      c 6 * E 1 2 4 5 6 7 +
      c 8 * E 1 2 4 5 6 8 +
      c 7 * E 1 2 4 5 6 9 +
      c 2 * E 1 3 4 5 6 7 +
      c 4 * E 1 3 4 5 6 8 +
      c 8 * E 1 3 4 5 7 9 +
      c 7 * E 1 3 4 5 8 9 +
      c 6 * E 2 3 4 5 6 7 +
      c 6 * E 2 3 4 5 6 8 +
      c 8 * E 2 3 4 5 6 9 +
      E 2 3 4 5 7 8 +
      c 5 * E 2 3 4 5 7 8 +
      c 3 * E 2 3 4 6 7 9 := by
  simp [normalizedLocalSecantEquation, secantPfaffianValue,
    ambientTwoCoeff,
    closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
    targetTwo_pair_eq_explicitTargetCoeff,
    explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
    explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
    rationalEffectiveD, localKleinPair, Fin.sum_univ_succ]
  ring_nf
  simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
    secant_pow_four_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.four_eq_zero_f2,
    N3Certificate.six_eq_zero_f2,
    N3Certificate.eight_eq_zero_f2]

/-- On the principal rational effectiveness chart, every normalized
rank-four secant correction satisfies the three rational pivot equations. -/
theorem rationalA_normalizedLocalSecant_mem
    (q0 q1 q3 : F₂) (c : TargetCoeff)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift 0 (rationalEffectiveA q0 q1 q3) + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ rationalZeroSecantCoeffSpace := by
  have hE (i j k l m n : Fin 10) :
      normalizedLocalSecantEquation 0
        (rationalEffectiveA q0 q1 q3) c i j k l m n = 0 :=
    normalizedLocalSecantEquation_eq_zero 0
      (rationalEffectiveA q0 q1 q3) c i j k l m n hsecant
  change rationalZeroSecantConstraint c = 0
  ext t
  fin_cases t
  · change c 3 + c 5 = 0
    have hid := rationalA_secant_constraint_zero_identity q0 q1 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 4 + c 6 = 0
    have hid := rationalA_secant_constraint_one_identity q0 q1 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 4 + c 5 + c 6 + c 7 = 0
    have hid := rationalA_secant_constraint_two_identity q0 q1 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid

/-- The companion rational effectiveness chart satisfies the same three
rank-four secant pivots. -/
theorem rationalD_normalizedLocalSecant_mem
    (q0 q3 : F₂) (c : TargetCoeff)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift 0 (rationalEffectiveD q0 q3) + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ rationalZeroSecantCoeffSpace := by
  have hE (i j k l m n : Fin 10) :
      normalizedLocalSecantEquation 0
        (rationalEffectiveD q0 q3) c i j k l m n = 0 :=
    normalizedLocalSecantEquation_eq_zero 0
      (rationalEffectiveD q0 q3) c i j k l m n hsecant
  change rationalZeroSecantConstraint c = 0
  ext t
  fin_cases t
  · change c 3 + c 5 = 0
    have hid := rationalD_secant_constraint_zero_identity q0 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 4 + c 6 = 0
    have hid := rationalD_secant_constraint_one_identity q0 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 4 + c 5 + c 6 + c 7 = 0
    have hid := rationalD_secant_constraint_two_identity q0 q3 c
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid

/-- Algebraic rational-place pivot: effectiveness and a normalized
two-wedge presentation force the correction into the codimension-three
rational secant coefficient space. -/
theorem rationalZero_normalizedLocalSecant_mem
    (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (c : TargetCoeff)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift 0 q + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ rationalZeroSecantCoeffSpace := by
  rcases rationalLocalEffective_cases q hq with
    ⟨q0, q1, q3, rfl⟩ | ⟨q0, q3, _hq03, rfl⟩
  · exact rationalA_normalizedLocalSecant_mem q0 q1 q3 c hsecant
  · exact rationalD_normalizedLocalSecant_mem q0 q3 c hsecant

/-- Rational-place local pivot in the original affine coordinates: the
target correction itself lies in the six-dimensional secant space. -/
theorem rationalZero_localSecantCorrection_mem
    (q : LocalKleinParam) (hq : RationalLocalEffective q)
    (z : LocalTargetParam) (c : TargetCoeff)
    (hsecant : ∃ u v x y : LinearForm,
      localSecantCandidate 0 q z c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ rationalZeroSecantCoeffSpace := by
  let d := closedPlaceTargetCoeff 0 z + c
  have hnormalized : ∃ u v x y : LinearForm,
      closedPlaceLift 0 q + targetTwo d =
        squarefreeWedge u v + squarefreeWedge x y := by
    simpa only [d, localSecantCandidate_eq_lift_add_target] using hsecant
  have hd : d ∈ rationalZeroSecantCoeffSpace :=
    rationalZero_normalizedLocalSecant_mem q hq d hnormalized
  have hz : closedPlaceTargetCoeff 0 z ∈ rationalZeroSecantCoeffSpace :=
    rationalZeroLocalCoeffSpace_le_secant
      (closedPlaceTargetCoeff_zero_mem_rationalZeroLocalCoeffSpace z)
  have hsum := rationalZeroSecantCoeffSpace.add_mem hd hz
  have hcancel : d + closedPlaceTargetCoeff 0 z = c := by
    funext i
    simp only [d, Pi.add_apply]
    simp [add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero]
  rw [hcancel] at hsum
  exact hsum

/-! ## Degree-two local secant equations -/

/-- The principal degree-two effectiveness chart, retaining both possible
same-side coefficients.  Effectiveness on this chart is the single equation
`q0*q3=0`. -/
def degreeEffectiveQ2 (q0 q1 q3 : F₂) : LocalKleinParam :=
  ![q0, q1, 1, q3]

set_option maxRecDepth 10000 in
/-- First degree-two secant pivot on the `q₂=1` chart. -/
theorem degreeQ2_secant_constraint_zero_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) (hq : q0 * q3 = 0) :
    c 1 + c 2 + c 4 + c 5 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveQ2 q0 q1 q3) c i j k l m n
      E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 7 +
      c 4 * E 0 1 2 5 6 7 +
      c 6 * E 0 1 2 5 6 7 +
      c 7 * E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 8 +
      c 3 * E 0 1 2 5 6 8 +
      q1 * E 0 1 2 5 6 9 +
      E 0 1 2 5 7 8 +
      c 2 * E 0 1 2 5 7 8 +
      c 2 * E 0 1 2 5 7 9 +
      c 3 * E 0 1 2 5 8 9 +
      c 3 * E 0 1 2 6 7 8 +
      c 3 * E 0 1 2 6 7 9 +
      E 0 1 2 6 8 9 +
      c 2 * E 0 1 2 6 8 9 +
      c 4 * E 0 1 2 6 8 9 +
      c 0 * E 0 1 2 7 8 9 +
      c 2 * E 0 1 3 5 6 7 +
      c 4 * E 0 1 3 5 6 7 +
      c 6 * E 0 1 3 5 6 7 +
      q1 * E 0 1 3 5 6 8 +
      E 0 1 3 5 6 9 +
      c 2 * E 0 1 3 5 6 9 +
      E 0 1 3 5 7 8 +
      c 2 * E 0 1 3 5 7 8 +
      E 0 1 3 5 7 9 +
      E 0 1 3 5 8 9 +
      c 3 * E 0 1 3 6 7 9 +
      E 0 1 3 6 8 9 +
      q1 * E 0 1 3 6 8 9 +
      c 3 * E 0 1 3 6 8 9 +
      c 0 * E 0 1 3 7 8 9 +
      E 0 2 3 5 6 8 +
      E 0 2 3 5 7 8 +
      c 3 * E 0 2 3 5 7 8 +
      c 3 * E 0 2 4 6 7 8 +
      E 1 2 3 6 7 8 := by
  rcases mul_eq_zero.mp hq with hq0 | hq3
  · subst q0
    simp [normalizedLocalSecantEquation, secantPfaffianValue,
      ambientTwoCoeff,
      closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
      targetTwo_pair_eq_explicitTargetCoeff,
      explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
      explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
      degreeEffectiveQ2, localKleinPair, Fin.sum_univ_succ]
    ring_nf
    simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
      secant_pow_four_f2]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, secant_five_eq_one_f2,
      secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
      secant_thirteen_eq_one_f2,
      secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
      secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
      secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
      secant_twenty_eight_eq_zero_f2]
  · subst q3
    simp [normalizedLocalSecantEquation, secantPfaffianValue,
      ambientTwoCoeff,
      closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
      targetTwo_pair_eq_explicitTargetCoeff,
      explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
      explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
      degreeEffectiveQ2, localKleinPair, Fin.sum_univ_succ]
    ring_nf
    simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
      secant_pow_four_f2]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, secant_five_eq_one_f2,
      secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
      secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
      secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
      secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
      secant_twenty_eight_eq_zero_f2]

set_option maxRecDepth 10000 in
/-- Second degree-two secant pivot on the `q₂=1` chart. -/
theorem degreeQ2_secant_constraint_one_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) (hq : q0 * q3 = 0) :
    c 1 + c 3 + c 4 + c 6 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveQ2 q0 q1 q3) c i j k l m n
      c 2 * E 0 1 2 5 6 7 +
      c 3 * E 0 1 2 5 6 7 +
      c 4 * E 0 1 2 5 6 7 +
      c 2 * E 0 1 2 5 6 8 +
      E 0 1 2 5 6 9 +
      c 4 * E 0 1 2 5 6 9 +
      c 5 * E 0 1 2 5 6 9 +
      c 7 * E 0 1 2 5 6 9 +
      c 2 * E 0 1 2 5 7 8 +
      c 5 * E 0 1 2 5 7 8 +
      c 6 * E 0 1 2 5 7 9 +
      c 7 * E 0 1 2 5 7 9 +
      c 2 * E 0 1 2 5 8 9 +
      c 3 * E 0 1 2 5 8 9 +
      E 0 1 2 6 7 8 +
      c 4 * E 0 1 2 6 7 8 +
      c 6 * E 0 1 2 6 7 9 +
      c 7 * E 0 1 2 6 7 9 +
      c 5 * E 0 1 2 6 8 9 +
      c 6 * E 0 1 2 6 8 9 +
      c 3 * E 0 1 3 5 6 7 +
      E 0 1 3 5 6 8 +
      q1 * E 0 1 3 5 6 8 +
      c 2 * E 0 1 3 5 6 8 +
      c 5 * E 0 1 3 5 6 8 +
      c 7 * E 0 1 3 5 6 8 +
      E 0 1 3 5 6 9 +
      q1 * E 0 1 3 5 7 8 +
      c 3 * E 0 1 3 5 7 8 +
      c 6 * E 0 1 3 5 7 8 +
      c 7 * E 0 1 3 5 7 8 +
      c 7 * E 0 1 3 5 7 9 +
      c 4 * E 0 1 3 5 8 9 +
      c 7 * E 0 1 3 6 7 8 +
      q1 * E 0 1 3 6 7 9 +
      c 1 * E 0 1 3 6 7 9 +
      c 5 * E 0 1 3 6 7 9 +
      c 7 * E 0 1 3 6 7 9 +
      q1 * E 0 1 3 6 8 9 +
      c 5 * E 0 1 3 6 8 9 +
      c 6 * E 0 1 3 6 8 9 +
      c 7 * E 0 1 3 6 8 9 +
      c 6 * E 0 1 3 7 8 9 +
      E 0 1 4 5 7 8 +
      E 0 1 4 6 7 8 +
      c 5 * E 0 2 3 5 6 9 +
      c 3 * E 0 2 3 5 7 8 +
      E 0 2 3 5 7 9 +
      E 0 2 3 5 8 9 +
      c 6 * E 0 2 3 6 7 9 +
      c 7 * E 0 2 3 6 7 9 +
      E 0 2 3 6 8 9 +
      c 6 * E 1 2 3 6 7 8 +
      c 7 * E 1 2 3 6 7 8 +
      E 1 2 3 6 8 9 := by
  rcases mul_eq_zero.mp hq with hq0 | hq3 <;> subst_vars
  all_goals
    simp [normalizedLocalSecantEquation, secantPfaffianValue,
      ambientTwoCoeff,
      closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
      targetTwo_pair_eq_explicitTargetCoeff,
      explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
      explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
      degreeEffectiveQ2, localKleinPair, Fin.sum_univ_succ]
    ring_nf
    simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
      secant_pow_four_f2]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, secant_five_eq_one_f2,
      secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
      secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
      secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
      secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
      secant_twenty_eight_eq_zero_f2]
    simpa [secant_three_eq_one_f2, secant_thirteen_eq_one_f2,
      secant_thirty_eq_zero_f2, secant_thirty_two_eq_zero_f2,
      secant_forty_eq_zero_f2, secant_forty_four_eq_zero_f2,
      secant_fifty_two_eq_zero_f2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Third degree-two secant pivot on the `q₂=1` chart. -/
theorem degreeQ2_secant_constraint_two_identity
    (q0 q1 q3 : F₂) (c : TargetCoeff) (hq : q0 * q3 = 0) :
    c 1 + c 7 =
      let E := fun i j k l m n => normalizedLocalSecantEquation 3
        (degreeEffectiveQ2 q0 q1 q3) c i j k l m n
      E 0 1 2 5 6 7 +
      q1 * E 0 1 2 5 6 7 +
      c 3 * E 0 1 2 5 6 7 +
      E 0 1 2 5 6 8 +
      c 8 * E 0 1 2 5 6 8 +
      c 2 * E 0 1 2 5 7 8 +
      c 3 * E 0 1 2 5 7 8 +
      c 6 * E 0 1 2 5 7 8 +
      c 2 * E 0 1 2 5 7 9 +
      c 7 * E 0 1 2 5 7 9 +
      c 2 * E 0 1 2 5 8 9 +
      c 6 * E 0 1 2 5 8 9 +
      q1 * E 0 1 2 6 7 8 +
      c 4 * E 0 1 2 6 7 8 +
      c 1 * E 0 1 2 6 7 9 +
      c 2 * E 0 1 2 6 7 9 +
      c 5 * E 0 1 2 6 7 9 +
      c 8 * E 0 1 2 6 7 9 +
      E 0 1 2 6 8 9 +
      c 3 * E 0 1 2 6 8 9 +
      c 5 * E 0 1 2 6 8 9 +
      c 6 * E 0 1 2 6 8 9 +
      c 2 * E 0 1 3 5 6 7 +
      c 3 * E 0 1 3 5 6 7 +
      c 4 * E 0 1 3 5 6 7 +
      c 8 * E 0 1 3 5 6 7 +
      c 3 * E 0 1 3 5 6 8 +
      c 4 * E 0 1 3 5 6 8 +
      c 8 * E 0 1 3 5 6 8 +
      c 5 * E 0 1 3 5 6 9 +
      c 7 * E 0 1 3 5 6 9 +
      c 6 * E 0 1 3 5 7 8 +
      E 0 1 3 5 7 9 +
      c 3 * E 0 1 3 5 7 9 +
      c 4 * E 0 1 3 5 8 9 +
      c 5 * E 0 1 3 5 8 9 +
      c 6 * E 0 1 3 5 8 9 +
      c 8 * E 0 1 3 5 8 9 +
      E 0 1 3 6 7 8 +
      c 8 * E 0 1 3 6 7 8 +
      q1 * E 0 1 3 6 7 9 +
      c 2 * E 0 1 3 6 7 9 +
      c 5 * E 0 1 3 6 7 9 +
      c 7 * E 0 1 3 6 7 9 +
      E 0 1 3 6 8 9 +
      q1 * E 0 1 3 6 8 9 +
      c 7 * E 0 1 3 6 8 9 +
      c 4 * E 0 1 3 7 8 9 +
      c 6 * E 0 1 3 7 8 9 +
      c 8 * E 0 1 3 7 8 9 +
      c 2 * E 0 1 4 5 6 9 +
      c 4 * E 0 1 4 5 6 9 +
      c 6 * E 0 1 4 5 6 9 +
      c 8 * E 0 1 4 5 6 9 +
      E 0 1 4 5 7 9 +
      c 3 * E 0 1 4 5 7 9 +
      c 6 * E 0 1 4 5 7 9 +
      c 2 * E 0 1 4 5 8 9 +
      c 3 * E 0 1 4 5 8 9 +
      c 8 * E 0 1 4 5 8 9 +
      c 7 * E 0 1 4 6 7 9 +
      c 8 * E 0 1 4 6 7 9 +
      c 7 * E 0 1 4 7 8 9 +
      q1 * E 0 2 3 5 6 7 +
      c 7 * E 0 2 3 5 6 8 +
      c 7 * E 0 2 3 5 6 9 +
      c 8 * E 0 2 3 5 7 9 +
      E 0 2 3 5 8 9 +
      c 3 * E 0 2 3 5 8 9 +
      c 7 * E 0 2 3 5 8 9 +
      c 7 * E 0 2 3 6 7 9 +
      c 6 * E 0 2 3 6 8 9 +
      c 7 * E 0 2 3 6 8 9 +
      c 7 * E 0 2 3 7 8 9 +
      c 6 * E 0 2 4 5 6 9 +
      c 3 * E 0 2 4 5 7 9 +
      c 8 * E 0 2 4 6 7 9 +
      c 8 * E 0 3 4 5 7 8 +
      E 0 3 4 5 8 9 +
      E 0 3 4 6 8 9 +
      E 1 2 3 5 7 8 +
      c 8 * E 1 2 3 5 7 8 +
      c 1 * E 1 2 3 5 8 9 +
      E 1 2 3 6 7 8 +
      c 8 * E 1 2 3 6 7 8 +
      c 4 * E 1 2 4 5 7 8 +
      c 8 * E 1 2 4 5 7 8 +
      E 1 2 4 6 7 8 +
      c 8 * E 1 2 4 6 7 9 +
      E 1 3 4 6 8 9 +
      c 7 * E 2 3 4 5 6 7 := by
  rcases mul_eq_zero.mp hq with hq0 | hq3 <;> subst_vars
  all_goals
    simp [normalizedLocalSecantEquation, secantPfaffianValue,
      ambientTwoCoeff,
      closedPlaceLift_pair_eq_explicitLocalLiftCoeff,
      targetTwo_pair_eq_explicitTargetCoeff,
      explicitLocalLiftCoeff, explicitClosedPlaceCanonicalCoord,
      explicitClosedPlaceBasisCoeff, explicitTargetCoeff,
      degreeEffectiveQ2, localKleinPair, Fin.sum_univ_succ]
    ring_nf
    simp only [N3Certificate.pow_two_f2, secant_pow_three_f2,
      secant_pow_four_f2]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2,
      N3Certificate.four_eq_zero_f2,
      N3Certificate.six_eq_zero_f2,
      N3Certificate.eight_eq_zero_f2, secant_five_eq_one_f2,
      secant_ten_eq_zero_f2, secant_twelve_eq_zero_f2,
      secant_fourteen_eq_zero_f2, secant_sixteen_eq_zero_f2,
      secant_eighteen_eq_zero_f2, secant_twenty_eq_zero_f2,
      secant_twenty_two_eq_zero_f2, secant_twenty_four_eq_zero_f2,
      secant_twenty_eight_eq_zero_f2]
    simpa [secant_three_eq_one_f2, secant_thirteen_eq_one_f2,
      secant_thirty_eq_zero_f2, secant_thirty_two_eq_zero_f2,
      secant_forty_eq_zero_f2, secant_forty_four_eq_zero_f2,
      secant_fifty_two_eq_zero_f2]

/-- On the principal degree-two chart, every normalized two-wedge
presentation satisfies the three defining norm-block constraints. -/
theorem degreeQ2_normalizedLocalSecant_mem
    (q0 q1 q3 : F₂) (c : TargetCoeff) (hq : q0 * q3 = 0)
    (hsecant : ∃ u v x y : LinearForm,
      closedPlaceLift 3 (degreeEffectiveQ2 q0 q1 q3) + targetTwo c =
        squarefreeWedge u v + squarefreeWedge x y) :
    c ∈ degreeTwoSecantCoeffSpace := by
  have hE (i j k l m n : Fin 10) :
      normalizedLocalSecantEquation 3
        (degreeEffectiveQ2 q0 q1 q3) c i j k l m n = 0 :=
    normalizedLocalSecantEquation_eq_zero 3
      (degreeEffectiveQ2 q0 q1 q3) c i j k l m n hsecant
  change degreeTwoSecantConstraint c = 0
  ext t
  fin_cases t
  · change c 1 + c 2 + c 4 + c 5 = 0
    have hid := degreeQ2_secant_constraint_zero_identity q0 q1 q3 c hq
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 1 + c 3 + c 4 + c 6 = 0
    have hid := degreeQ2_secant_constraint_one_identity q0 q1 q3 c hq
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid
  · change c 1 + c 7 = 0
    have hid := degreeQ2_secant_constraint_two_identity q0 q1 q3 c hq
    dsimp only at hid
    simpa only [hE, mul_zero, add_zero] using hid

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
