import UnrestrictedBooleanMul.N5.LowProductShadow

/-!
# Rank-one low-product shadow rigidity

This module closes the rank-one part of the equal-factor-plane argument in
manuscript Lemma 11.2.  It uses Boolean idempotence algebraically: if a vector
annihilates a quadratic two-form, the Boolean contraction along that vector
is the old two-form plus a decomposable correction.  Consequently the
difference of two equal-high rank-one low products is, modulo the old
quadratic envelope, a sum of two decomposable forms and cannot represent the
missing target coset.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Coordinatewise product supplying the diagonal term removed by the
squarefree exterior projection. -/
def ambientDiagonalProduct (u v : LinearForm) : LinearForm :=
  fun i => u i * v i

@[simp] theorem ambientTwoCoeff_zero (i j : Fin 10) :
    ambientTwoCoeff (0 : TwoForm) i j = 0 := by
  by_cases hij : i = j <;> simp [ambientTwoCoeff, hij]

/-- Boolean idempotence for a contraction along one factor of a decomposable
two-form. -/
theorem ambientBooleanContraction_squarefreeWedge_left
    (u v : LinearForm) :
    ambientBooleanContraction u (squarefreeWedge u v) =
      squarefreeWedge u v +
        squarefreeWedge u (ambientDiagonalProduct u v) := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [ambientBooleanContraction, squarefreeWedge_pair,
    Pi.add_apply]
  simp [quadraticPair, hij, ambientDiagonalProduct]
  ring_nf
  simp [N3Certificate.pow_two_f2]

/-- If `u` is nonzero and `u ∧ d = 0`, contraction by `u` is `d` plus
one decomposable correction. -/
theorem ambientBooleanContraction_of_vectorWedge_zero
    (u : LinearForm) (d : TwoForm) (hu : u ≠ 0)
    (hzero : ambientVectorWedgeTwo u d = 0) :
    ∃ v : LinearForm,
      d = squarefreeWedge u v ∧
      ambientBooleanContraction u d =
        d + squarefreeWedge u (ambientDiagonalProduct u v) := by
  rcases eq_squarefreeWedge_of_ambientVectorWedgeTwo_eq_zero
      d u hu hzero with ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  rw [hv, ambientBooleanContraction_squarefreeWedge_left]

@[simp] theorem factorPlaneCubic_zero_left
    (ell m : LinearForm) (d : TwoForm) :
    factorPlaneCubic ell m 0 d = ambientVectorWedgeTwo ell d := by
  funext i j k
  simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN]

@[simp] theorem factorPlaneCubic_zero_right
    (ell m : LinearForm) (d : TwoForm) :
    factorPlaneCubic ell m d 0 = ambientVectorWedgeTwo m d := by
  funext i j k
  simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN]

/-- Difference formula when only the right factor has a nonzero quadratic
direction. -/
theorem lowProductQuadraticShadow_zero_left_sum
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (d : TwoForm) :
    lowProductQuadraticShadow a b ell m 0 d +
        lowProductQuadraticShadow a' b' ell' m' 0 d =
      (a + a') • d +
        (squarefreeWedge ell m + squarefreeWedge ell' m') +
          ambientBooleanContraction (ell + ell') d := by
  funext s
  simp only [lowProductQuadraticShadow, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp [ambientBooleanContraction, ambientTwoHadamard,
    Finset.sum_add_distrib]
  ring

/-- Elementary reassociation of two decomposable shadows. -/
theorem squarefreeWedge_pair_sum_reassociate
    (ell m ell' m' : LinearForm) :
    squarefreeWedge ell m + squarefreeWedge ell' m' =
      squarefreeWedge ell (m + m') +
        squarefreeWedge (ell + ell') m' := by
  rw [squarefreeWedge_add_right, squarefreeWedge_add_left]
  funext s
  simp only [Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Rank-one shadow decomposition with the quadratic direction on the right.
The entire difference is an old-envelope term plus at most two decomposable
two-forms. -/
theorem rankOneShadow_zero_left_decomposition
    (W : Submodule F₂ TwoForm)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (d : TwoForm)
    (hd : d ∈ W)
    (hcubic : factorPlaneCubic ell m 0 d =
      factorPlaneCubic ell' m' 0 d) :
    ∃ r ∈ W, ∃ u v x y : LinearForm,
      lowProductQuadraticShadow a b ell m 0 d +
          lowProductQuadraticShadow a' b' ell' m' 0 d =
        r + squarefreeWedge u v + squarefreeWedge x y := by
  by_cases hx : ell + ell' = 0
  · have hell : ell = ell' := by
      funext i
      have hi := congrFun hx i
      simp only [Pi.add_apply, Pi.zero_apply] at hi
      rw [← CharTwo.sub_eq_add] at hi
      exact sub_eq_zero.mp hi
    subst ell'
    refine ⟨(a + a') • d, W.smul_mem _ hd,
      ell, m + m', 0, 0, ?_⟩
    rw [lowProductQuadraticShadow_zero_left_sum]
    rw [hx, ambientBooleanContraction_zero_left,
      squarefreeWedge_add_right]
    simp
  · have hkernel : ambientVectorWedgeTwo (ell + ell') d = 0 := by
      have hcubic' : ambientVectorWedgeTwo ell d =
          ambientVectorWedgeTwo ell' d := by simpa using hcubic
      change (ambientVectorWedgeMap d) (ell + ell') = 0
      rw [map_add]
      change ambientVectorWedgeTwo ell d +
        ambientVectorWedgeTwo ell' d = 0
      rw [hcubic']
      funext i j k
      exact @CharTwo.add_self_eq_zero F₂ _ _
        (ambientVectorWedgeTwo ell' d i j k)
    rcases ambientBooleanContraction_of_vectorWedge_zero
        (ell + ell') d hx hkernel with ⟨v, hdv, hcontraction⟩
    refine ⟨(a + a' + 1) • d, W.smul_mem _ hd,
      ell, m + m', ell + ell',
      m' + ambientDiagonalProduct (ell + ell') v, ?_⟩
    rw [lowProductQuadraticShadow_zero_left_sum,
      squarefreeWedge_pair_sum_reassociate, hcontraction,
      squarefreeWedge_add_right (ell + ell') m'
        (ambientDiagonalProduct (ell + ell') v)]
    simp only [add_smul, one_smul]
    module

/-- Move one target-envelope summand across an equality in characteristic
two.  Keeping this coordinate cancellation separate prevents the surrounding
missing-coset theorem from becoming an expensive elaboration problem. -/
theorem move_targetEnvelope_across_missingCoset
    (c u : TargetCoeff) (w : TwoForm)
    (heq : targetTwoLinear c + w =
      targetTwo (firstOrderMissingCoeff + u)) :
    targetTwo (firstOrderMissingCoeff + (u + c)) = w := by
  change targetTwoLinear (firstOrderMissingCoeff + (u + c)) = w
  have hcanc : firstOrderMissingCoeff + (u + c) =
      (firstOrderMissingCoeff + u) + c := by module
  rw [hcanc, targetTwoLinear.map_add]
  change targetTwoLinear c + w =
      targetTwoLinear (firstOrderMissingCoeff + u) at heq
  rw [← heq]
  funext s
  simp only [Pi.add_apply]
  let z : F₂ := targetTwoLinear c s
  change (z + w s) + z = w s
  calc
    (z + w s) + z = z + (w s + z) := add_assoc z (w s) z
    _ = z + (z + w s) := by rw [add_comm (w s) z]
    _ = (z + z) + w s := (add_assoc z z (w s)).symm
    _ = w s := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- Adding an old-envelope form to two decomposable forms still cannot land
in the affine missing target coset. -/
theorem firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    (r : TwoForm) (hr : r ∈ firstOrderEnvelopeTwoSpace)
    (p q x y : LinearForm) (u : TargetCoeff)
    (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    r + squarefreeWedge p q + squarefreeWedge x y ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro heq
  rcases hr with ⟨c, hc, rfl⟩
  have huc : u + c ∈ firstOrderEnvelopeCoeffSpace :=
    firstOrderEnvelopeCoeffSpace.add_mem hu hc
  apply missingCoset_not_sum_two_decomposable (u + c) huc
  refine ⟨p, q, x, y, ?_⟩
  apply move_targetEnvelope_across_missingCoset c u
    (squarefreeWedge p q + squarefreeWedge x y)
  simpa only [add_assoc] using heq

/-- A rank-one equal-high comparison cannot realize the affine missing target
coset when its single quadratic direction is already in the old envelope. -/
theorem rankOneShadow_zero_left_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (d : TwoForm)
    (hd : d ∈ firstOrderEnvelopeTwoSpace)
    (hcubic : factorPlaneCubic ell m 0 d =
      factorPlaneCubic ell' m' 0 d)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m 0 d +
        lowProductQuadraticShadow a' b' ell' m' 0 d ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  rcases rankOneShadow_zero_left_decomposition
      firstOrderEnvelopeTwoSpace a b a' b' ell m ell' m' d hd hcubic with
    ⟨r, hr, p, q, x, y, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q x y u hu
  exact hdecomp.symm.trans hmissing

/-- Symmetric decomposition when the single quadratic direction occurs in
the left factor. -/
theorem rankOneShadow_zero_right_decomposition
    (W : Submodule F₂ TwoForm)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (d : TwoForm)
    (hd : d ∈ W)
    (hcubic : factorPlaneCubic ell m d 0 =
      factorPlaneCubic ell' m' d 0) :
    ∃ r ∈ W, ∃ u v x y : LinearForm,
      lowProductQuadraticShadow a b ell m d 0 +
          lowProductQuadraticShadow a' b' ell' m' d 0 =
        r + squarefreeWedge u v + squarefreeWedge x y := by
  have hcubic' : factorPlaneCubic m ell 0 d =
      factorPlaneCubic m' ell' 0 d := by simpa using hcubic
  simpa only [lowProductQuadraticShadow_swap] using
    rankOneShadow_zero_left_decomposition W b a b' a'
      m ell m' ell' d hd hcubic'

/-- Symmetric missing-coset exclusion for a left quadratic direction. -/
theorem rankOneShadow_zero_right_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (d : TwoForm)
    (hd : d ∈ firstOrderEnvelopeTwoSpace)
    (hcubic : factorPlaneCubic ell m d 0 =
      factorPlaneCubic ell' m' d 0)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m d 0 +
        lowProductQuadraticShadow a' b' ell' m' d 0 ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  rcases rankOneShadow_zero_right_decomposition
      firstOrderEnvelopeTwoSpace a b a' b' ell m ell' m' d hd hcubic with
    ⟨r, hr, p, q, x, y, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q x y u hu
  exact hdecomp.symm.trans hmissing

/-- When both quadratic directions coincide, the cubic part is exterior
multiplication by the sum of the two linear parts. -/
theorem factorPlaneCubic_same_direction
    (ell m : LinearForm) (d : TwoForm) :
    factorPlaneCubic ell m d d =
      ambientVectorWedgeTwo (ell + m) d := by
  change ambientVectorWedgeTwo ell d + ambientVectorWedgeTwo m d =
    (ambientVectorWedgeMap d) (ell + m)
  rw [map_add]
  rfl

/-- Difference formula when both factors use the same quadratic direction. -/
theorem lowProductQuadraticShadow_same_direction_sum
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (d : TwoForm) :
    lowProductQuadraticShadow a b ell m d d +
        lowProductQuadraticShadow a' b' ell' m' d d =
      (a + b + a' + b') • d +
        (squarefreeWedge ell m + squarefreeWedge ell' m') +
          ambientBooleanContraction
            ((ell + m) + (ell' + m')) d := by
  funext s
  simp only [lowProductQuadraticShadow, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp [ambientBooleanContraction, ambientTwoHadamard,
    Finset.sum_add_distrib, N3Certificate.mul_self_f2]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Reassociate the two original decomposable shadows and the correction
along the total changed linear direction into two decomposable forms. -/
theorem squarefreeWedge_pair_sum_add_total
    (ell m ell' m' z : LinearForm) :
    (squarefreeWedge ell m + squarefreeWedge ell' m') +
        squarefreeWedge ((ell + m) + (ell' + m')) z =
      squarefreeWedge (m + m') (ell + z) +
        squarefreeWedge (ell + ell') (m' + z) := by
  have htotal : (ell + m) + (ell' + m') =
      (ell + ell') + (m + m') := by
    funext i
    simp only [Pi.add_apply]
    ac_rfl
  rw [squarefreeWedge_pair_sum_reassociate, htotal,
    squarefreeWedge_add_left (ell + ell') (m + m') z,
    squarefreeWedge_add_right (m + m') ell z,
    squarefreeWedge_add_right (ell + ell') m' z,
    squarefreeWedge_comm_f2 ell (m + m')]
  module

/-- Small additive reassociation used to keep the rank-one proof below from
asking normalization tactics to unfold the 45-coordinate two-form type. -/
theorem twoForm_add_pair_reassociate (A B C D : TwoForm) :
    A + B + (C + D) = (A + C) + (B + D) := by
  funext s
  simp only [Pi.add_apply]
  ac_rfl

/-- Rank-one decomposition for the third projective presentation `(d,d)`. -/
theorem rankOneShadow_same_direction_decomposition
    (W : Submodule F₂ TwoForm)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (d : TwoForm)
    (hd : d ∈ W)
    (hcubic : factorPlaneCubic ell m d d =
      factorPlaneCubic ell' m' d d) :
    ∃ r ∈ W, ∃ u v x y : LinearForm,
      lowProductQuadraticShadow a b ell m d d +
          lowProductQuadraticShadow a' b' ell' m' d d =
        r + squarefreeWedge u v + squarefreeWedge x y := by
  let t : LinearForm := (ell + m) + (ell' + m')
  by_cases ht : t = 0
  · refine ⟨(a + b + a' + b') • d, W.smul_mem _ hd,
      ell, m + m', ell + ell', m', ?_⟩
    rw [lowProductQuadraticShadow_same_direction_sum]
    change (a + b + a' + b') • d +
        (squarefreeWedge ell m + squarefreeWedge ell' m') +
          ambientBooleanContraction t d = _
    rw [ht, ambientBooleanContraction_zero_left,
      squarefreeWedge_pair_sum_reassociate]
    module
  · have hcubic' : ambientVectorWedgeTwo (ell + m) d =
        ambientVectorWedgeTwo (ell' + m') d := by
      simpa only [factorPlaneCubic_same_direction] using hcubic
    have hkernel : ambientVectorWedgeTwo t d = 0 := by
      change (ambientVectorWedgeMap d)
        ((ell + m) + (ell' + m')) = 0
      rw [map_add]
      change ambientVectorWedgeTwo (ell + m) d +
        ambientVectorWedgeTwo (ell' + m') d = 0
      rw [hcubic']
      funext i j k
      exact @CharTwo.add_self_eq_zero F₂ _ _
        (ambientVectorWedgeTwo (ell' + m') d i j k)
    rcases ambientBooleanContraction_of_vectorWedge_zero
        t d ht hkernel with ⟨v, _hdv, hcontraction⟩
    refine ⟨(a + b + a' + b' + 1) • d, W.smul_mem _ hd,
      m + m', ell + ambientDiagonalProduct t v,
      ell + ell', m' + ambientDiagonalProduct t v, ?_⟩
    rw [lowProductQuadraticShadow_same_direction_sum]
    change (a + b + a' + b') • d +
        (squarefreeWedge ell m + squarefreeWedge ell' m') +
          ambientBooleanContraction t d = _
    rw [hcontraction, twoForm_add_pair_reassociate]
    have hscalar : (a + b + a' + b') • d + d =
        (a + b + a' + b' + 1) • d := by
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hscalar]
    have hwedge :
        (squarefreeWedge ell m + squarefreeWedge ell' m') +
            squarefreeWedge t (ambientDiagonalProduct t v) =
          squarefreeWedge (m + m')
              (ell + ambientDiagonalProduct t v) +
            squarefreeWedge (ell + ell')
              (m' + ambientDiagonalProduct t v) := by
      change (squarefreeWedge ell m + squarefreeWedge ell' m') +
          squarefreeWedge ((ell + m) + (ell' + m'))
            (ambientDiagonalProduct t v) = _
      exact squarefreeWedge_pair_sum_add_total ell m ell' m'
        (ambientDiagonalProduct t v)
    rw [hwedge]
    exact (add_assoc _ _ _).symm

/-- Missing-coset exclusion for the equal nonzero rank-one presentation. -/
theorem rankOneShadow_same_direction_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (d : TwoForm)
    (hd : d ∈ firstOrderEnvelopeTwoSpace)
    (hcubic : factorPlaneCubic ell m d d =
      factorPlaneCubic ell' m' d d)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m d d +
        lowProductQuadraticShadow a' b' ell' m' d d ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  rcases rankOneShadow_same_direction_decomposition
      firstOrderEnvelopeTwoSpace a b a' b' ell m ell' m' d hd hcubic with
    ⟨r, hr, p, q, x, y, hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr p q x y u hu
  exact hdecomp.symm.trans hmissing

/-- Over `F₂`, two quadratic directions are dependent exactly in the three
projective cases used above. -/
theorem quadraticPlaneDirections_dependent_classification
    (q c : TwoForm)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    q = 0 ∨ c = 0 ∨ q = c := by
  by_cases hq : q = 0
  · exact Or.inl hq
  by_cases hc : c = 0
  · exact Or.inr (Or.inl hc)
  by_cases hqc : q = c
  · exact Or.inr (Or.inr hqc)
  exfalso
  apply hdep
  rw [linearIndependent_fin2]
  change q ≠ 0 ∧ ∀ a : F₂, a • q ≠ c
  refine ⟨hq, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hc
  · simpa using hqc

/-- Complete rank-one equal-plane shadow exclusion.  No choice of the three
nonzero projective presentations of one quadratic direction can represent
the missing target coset. -/
theorem rankOneShadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (q c : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q c)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q c ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases quadraticPlaneDirections_dependent_classification q c hdep with
    hq0 | hc0 | hqc
  · subst q
    exact rankOneShadow_zero_left_not_missingCoset
      a b a' b' ell m ell' m' c hc hcubic u hu
  · subst c
    exact rankOneShadow_zero_right_not_missingCoset
      a b a' b' ell m ell' m' q hq hcubic u hu
  · subst c
    exact rankOneShadow_same_direction_not_missingCoset
      a b a' b' ell m ell' m' q hq hcubic u hu

end
end N5
end UnrestrictedBooleanMul
