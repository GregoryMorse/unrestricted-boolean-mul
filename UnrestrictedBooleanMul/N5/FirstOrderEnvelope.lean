import UnrestrictedBooleanMul.N5.RelationGiftPivots

/-!
# The first-order target envelope

The eight closed-place directions form the manuscript's first-order envelope
`U`.  This file identifies its single missing target coordinate, proves that
the entire target is the direct extension of `U` by that coordinate, and
shows that every defect of dimension at most one has its quadratic target
base inside `U`.

All arguments are linear algebra in the nine Hankel coefficients.  In
particular, the defect-one result uses the exact relation map and does not
enumerate quadratic forms or circuits.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The codimension-one coefficient envelope
`R + D_* + <j_0,j_1,j_infinity>`. -/
abbrev firstOrderEnvelopeCoeffSpace : Submodule F₂ TargetCoeff :=
  closedPlaceCoeffSpace

/-- The first-order envelope embedded in the ambient two-form space. -/
def firstOrderEnvelopeTwoSpace : Submodule F₂ TwoForm :=
  firstOrderEnvelopeCoeffSpace.map targetTwoLinear

/-- The sole linear coordinate omitted by the first-order envelope. -/
def firstOrderMissingFunctional : TargetCoeff →ₗ[F₂] F₂ where
  toFun c := c 2 + c 3 + c 5 + c 6
  map_add' c d := by
    simp only [Pi.add_apply]
    module
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_add]
    module

/-- The manuscript's missing target representative `tau = E_2`. -/
def firstOrderMissingCoeff : TargetCoeff :=
  ![0, 0, 1, 0, 0, 0, 0, 0, 0]

@[simp] theorem firstOrderMissingFunctional_missing :
    firstOrderMissingFunctional firstOrderMissingCoeff = 1 := by
  simp [firstOrderMissingFunctional, firstOrderMissingCoeff]

theorem firstOrderMissingFunctional_surjective :
    Function.Surjective firstOrderMissingFunctional := by
  intro a
  refine ⟨a • firstOrderMissingCoeff, ?_⟩
  simp

theorem firstOrderMissingFunctional_closedPlaceDirection (i : Fin 8) :
    firstOrderMissingFunctional (closedPlaceDirections i) = 0 := by
  fin_cases i <;>
    decide

theorem firstOrderEnvelopeCoeffSpace_le_missingKernel :
    firstOrderEnvelopeCoeffSpace ≤
      LinearMap.ker firstOrderMissingFunctional := by
  apply Submodule.span_le.mpr
  rintro c ⟨i, rfl⟩
  exact (LinearMap.mem_ker).2
    (firstOrderMissingFunctional_closedPlaceDirection i)

theorem firstOrderMissingKernel_finrank :
    Module.finrank F₂ (LinearMap.ker firstOrderMissingFunctional) = 8 := by
  have h := firstOrderMissingFunctional.finrank_range_add_finrank_ker
  have hrange : LinearMap.range firstOrderMissingFunctional = ⊤ :=
    LinearMap.range_eq_top.mpr firstOrderMissingFunctional_surjective
  rw [hrange] at h
  have h' : 1 + Module.finrank F₂
      (LinearMap.ker firstOrderMissingFunctional) = 9 := by
    simpa [TargetCoeff] using h
  omega

/-- Intrinsic equation of the first-order envelope. -/
theorem firstOrderEnvelopeCoeffSpace_eq_missingKernel :
    firstOrderEnvelopeCoeffSpace =
      LinearMap.ker firstOrderMissingFunctional := by
  apply Submodule.eq_of_le_of_finrank_eq
    firstOrderEnvelopeCoeffSpace_le_missingKernel
  rw [closedPlaceCoeffSpace_finrank, firstOrderMissingKernel_finrank]

theorem mem_firstOrderEnvelopeCoeffSpace (c : TargetCoeff) :
    c ∈ firstOrderEnvelopeCoeffSpace ↔
      firstOrderMissingFunctional c = 0 := by
  rw [firstOrderEnvelopeCoeffSpace_eq_missingKernel,
    LinearMap.mem_ker]

/-- The first-order envelope has dimension eight. -/
theorem firstOrderEnvelopeTwoSpace_finrank :
    Module.finrank F₂ firstOrderEnvelopeTwoSpace = 8 := by
  let f : firstOrderEnvelopeCoeffSpace →ₗ[F₂] TwoForm :=
    targetTwoLinear.domRestrict firstOrderEnvelopeCoeffSpace
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    exact targetTwoLinear_injective hcd
  have hrange : LinearMap.range f = firstOrderEnvelopeTwoSpace := by
    ext p
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hf,
    closedPlaceCoeffSpace_finrank]

theorem firstOrderEnvelopeTwoSpace_le_targetTwoSpace :
    firstOrderEnvelopeTwoSpace ≤ targetTwoSpace := by
  rintro p ⟨c, hc, rfl⟩
  exact ⟨c, rfl⟩

/-- The missing coefficient really represents the unique target coset
outside the first-order envelope. -/
theorem firstOrderMissingCoeff_not_mem :
    firstOrderMissingCoeff ∉ firstOrderEnvelopeCoeffSpace := by
  rw [mem_firstOrderEnvelopeCoeffSpace]
  simp

theorem targetTwo_firstOrderMissingCoeff_not_mem :
    targetTwo firstOrderMissingCoeff ∉ firstOrderEnvelopeTwoSpace := by
  rintro ⟨c, hc, htarget⟩
  have hcoeff : c = firstOrderMissingCoeff :=
    targetTwoLinear_injective htarget
  exact firstOrderMissingCoeff_not_mem (hcoeff ▸ hc)

/-- The missing coefficient complements the envelope to the full
nine-dimensional target coefficient space. -/
theorem firstOrderEnvelopeCoeffSpace_sup_missing_eq_top :
    firstOrderEnvelopeCoeffSpace ⊔
        Submodule.span F₂ ({firstOrderMissingCoeff} : Set TargetCoeff) = ⊤ := by
  apply top_unique
  intro c _
  let a : F₂ := firstOrderMissingFunctional c
  have hkernel : c + a • firstOrderMissingCoeff ∈
      firstOrderEnvelopeCoeffSpace := by
    rw [mem_firstOrderEnvelopeCoeffSpace]
    simp [a, CharTwo.add_self_eq_zero]
  have hmissing : a • firstOrderMissingCoeff ∈
      Submodule.span F₂ ({firstOrderMissingCoeff} : Set TargetCoeff) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hsum := Submodule.add_mem
    (firstOrderEnvelopeCoeffSpace ⊔
      Submodule.span F₂ ({firstOrderMissingCoeff} : Set TargetCoeff))
    ((le_sup_left : firstOrderEnvelopeCoeffSpace ≤ _) hkernel)
    ((le_sup_right :
      Submodule.span F₂ ({firstOrderMissingCoeff} : Set TargetCoeff) ≤ _) hmissing)
  have hcancel : a • firstOrderMissingCoeff +
      a • firstOrderMissingCoeff = 0 := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  have heq : (c + a • firstOrderMissingCoeff) +
      a • firstOrderMissingCoeff = c := by
    rw [add_assoc, hcancel, add_zero]
  rwa [heq] at hsum

/-- Every intrinsic displacement direction is first-order. -/
theorem localDisplacementCoeffSpace_le_firstOrderEnvelope
    (Q : Submodule F₂ QuadraticQuotient) :
    localDisplacementCoeffSpace Q ≤ firstOrderEnvelopeCoeffSpace := by
  rw [localDisplacementCoeffSpace_eq_active,
    activeDisplacementCoeffSpace]
  apply Submodule.span_le.mpr
  rintro c ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i.1, rfl⟩

theorem localDisplacementSpace_le_firstOrderEnvelope
    (Q : Submodule F₂ QuadraticQuotient) :
    localDisplacementSpace Q ≤ firstOrderEnvelopeTwoSpace := by
  rw [localDisplacementSpace_eq_activeDisplacementTwoSpace,
    ← activeDisplacementCoeffSpace_map_targetTwo]
  have hactive : activeDisplacementCoeffSpace Q ≤
      firstOrderEnvelopeCoeffSpace := by
    rw [← localDisplacementCoeffSpace_eq_active]
    exact localDisplacementCoeffSpace_le_firstOrderEnvelope Q
  exact Submodule.map_mono hactive

/-- A defect of dimension at most one has no additive relation among its
populated nonzero quotient points. -/
theorem populatedRelationKernel_finrank_eq_zero_of_finrank_le_one
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 1) :
    Module.finrank F₂
      ↑(relationKernel (populatedQuotientPoint (Q := Q))) = 0 := by
  let q := populatedQuotientPoint (Q := Q)
  let S : Submodule F₂ QuadraticQuotient :=
    Submodule.span F₂ (Set.range q)
  change Module.finrank F₂ ↑(relationKernel q) = 0
  have hSle : S ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact x.1.2
  have hSrank : Module.finrank F₂ S ≤ 1 :=
    (Submodule.finrank_mono hSle).trans hQ
  have hcard : Fintype.card (PopulatedPoint Q) + 1 ≤
      2 ^ Module.finrank F₂ S := by
    exact card_add_one_le_pow_finrank_span q
      (populatedQuotientPoint_injective Q) (fun x ↦ x.2.1)
  have hkernel := relationKernel_finrank_add_span q
  change Module.finrank F₂ ↑(relationKernel q) +
      Module.finrank F₂ S = Fintype.card (PopulatedPoint Q) at hkernel
  have hScases : Module.finrank F₂ S = 0 ∨
      Module.finrank F₂ S = 1 := by omega
  rcases hScases with hS | hS
  · have hcardzero : Fintype.card (PopulatedPoint Q) = 0 := by
      norm_num [hS] at hcard
      omega
    have hk : Module.finrank F₂ ↑(relationKernel q) + 0 = 0 := by
      simpa only [hS, hcardzero] using hkernel
    omega
  · have hcardone : Fintype.card (PopulatedPoint Q) = 1 := by
      norm_num [hS] at hcard
      have hpositive : 1 ≤ Fintype.card (PopulatedPoint Q) := by
        omega
      omega
    have hk : Module.finrank F₂ ↑(relationKernel q) + 1 = 1 := by
      simpa only [hS, hcardone] using hkernel
    omega

theorem relationGiftRank_eq_zero_of_finrank_le_one
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 1) :
    relationGiftRank Q = 0 := by
  have hgift := relationGiftRank_le_relationKernel Q
  rw [populatedRelationKernel_finrank_eq_zero_of_finrank_le_one Q hQ]
    at hgift
  omega

/-- If the relation map has zero-dimensional domain, the target portion of
the capacity span is already intrinsic displacement. -/
theorem targetCapacitySpace_le_localDisplacement_of_relationKernel_zero
    (Q : Submodule F₂ QuadraticQuotient)
    (hkernel : Module.finrank F₂
      ↑(relationKernel (populatedQuotientPoint (Q := Q))) = 0) :
    targetTwoSpace ⊓ defectCapacitySpan Q ≤ localDisplacementSpace Q := by
  let K := relationKernel (populatedQuotientPoint (Q := Q))
  haveI : Subsingleton K := Module.finrank_zero_iff.mp hkernel
  have hrange : LinearMap.range (defectRelationMap Q) = ⊥ := by
    apply le_antisymm
    · rintro y ⟨a, rfl⟩
      have ha : a = 0 := Subsingleton.elim _ _
      simp [ha]
    · exact bot_le
  have hexact := relationMap_exact
    (localDisplacementSpace Q) (defectCapacitySpan Q)
    (populatedLift (Q := Q)) (populatedQuotientPoint (Q := Q))
    (localDisplacementSpace_le_targetTwoSpace Q)
    populatedLift_projection rfl
  change Submodule.map (Submodule.mkQ (localDisplacementSpace Q))
      (targetTwoSpace ⊓ defectCapacitySpan Q) =
        LinearMap.range (defectRelationMap Q) at hexact
  rw [hrange] at hexact
  intro t ht
  have htmap : (Submodule.mkQ (localDisplacementSpace Q)) t ∈
      Submodule.map (Submodule.mkQ (localDisplacementSpace Q))
        (targetTwoSpace ⊓ defectCapacitySpan Q) :=
    ⟨t, ht, rfl⟩
  rw [hexact] at htmap
  exact (Submodule.Quotient.mk_eq_zero (localDisplacementSpace Q)).1 htmap

/-- Manuscript Section 11 base-envelope assertion: every quadratic target
base of quotient-defect dimension at most one lies in `U`. -/
theorem targetCapacitySpace_le_firstOrderEnvelope_of_finrank_le_one
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 1) :
    targetTwoSpace ⊓ defectCapacitySpan Q ≤
      firstOrderEnvelopeTwoSpace :=
  (targetCapacitySpace_le_localDisplacement_of_relationKernel_zero Q
    (populatedRelationKernel_finrank_eq_zero_of_finrank_le_one Q hQ)).trans
      (localDisplacementSpace_le_firstOrderEnvelope Q)

theorem targetCapacity_le_eight_of_finrank_le_one
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 1) :
    targetCapacity Q ≤ 8 := by
  unfold targetCapacity
  rw [← firstOrderEnvelopeTwoSpace_finrank]
  exact Submodule.finrank_mono
    (targetCapacitySpace_le_firstOrderEnvelope_of_finrank_le_one Q hQ)

/-- Algebraic missing-coset rigidity: no translate `tau + u`, with `u` in
the first-order envelope, satisfies the rank-at-most-two Hankel equations. -/
theorem missingCoset_not_rankTwoHankel
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    ¬ HankelRankLETwo (firstOrderMissingCoeff + u) := by
  intro hrank
  have hmem : firstOrderMissingCoeff + u ∈
      firstOrderEnvelopeCoeffSpace := rankTwoHankel_support hrank
  have htau : firstOrderMissingCoeff ∈
      firstOrderEnvelopeCoeffSpace := by
    have := firstOrderEnvelopeCoeffSpace.sub_mem hmem hu
    simpa using this
  exact firstOrderMissingCoeff_not_mem htau

end

end N5
end UnrestrictedBooleanMul
