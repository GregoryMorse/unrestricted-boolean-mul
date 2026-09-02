import UnrestrictedBooleanMul.N5.EnvelopeOneRotation

/-!
# Distinct rational local planes

The rational zero and infinity two-jets live on disjoint four-dimensional
coordinate blocks.  A cubic in the image of either local factor plane has at
least two indices in its own block.  A three-index coefficient cannot have
two indices in both disjoint blocks, so the two cubic images intersect only
at zero.  Rational-place symmetries transport this separation to every pair
of distinct rational places.

This is a support argument followed by linear symmetry transport; it does not
enumerate Boolean assignments or circuit states.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private def IsZeroJetCoord (i : Fin 10) : Prop :=
  i = aCoord 0 ∨ i = aCoord 1 ∨ i = bCoord 0 ∨ i = bCoord 1

private def IsInfinityJetCoord (i : Fin 10) : Prop :=
  i = aCoord 3 ∨ i = aCoord 4 ∨ i = bCoord 3 ∨ i = bCoord 4

private theorem zeroJetCoord_not_infinityJetCoord (i : Fin 10) :
    ¬ (IsZeroJetCoord i ∧ IsInfinityJetCoord i) := by
  rintro ⟨hi, hj⟩
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with h | h | h | h <;>
    simp [aCoord, bCoord] at h

private theorem rationalZeroValueTwo_support
    (i j : Fin 10) (h : ¬ (IsZeroJetCoord i ∧ IsZeroJetCoord j)) :
    ambientTwoCoeff rationalZeroValueTwo i j = 0 := by
  rw [rationalZeroValueTwo, targetPairTwo,
    ambientTwoCoeff_squarefreeWedge]
  simp only [aLinear, bLinear, Pi.basisFun_apply]
  by_cases hi : i = aCoord 0 <;> by_cases hj : j = aCoord 0 <;>
    by_cases hi' : i = bCoord 0 <;> by_cases hj' : j = bCoord 0 <;>
    simp_all [IsZeroJetCoord]

private theorem rationalZeroJetTwo_support
    (i j : Fin 10) (h : ¬ (IsZeroJetCoord i ∧ IsZeroJetCoord j)) :
    ambientTwoCoeff rationalZeroJetTwo i j = 0 := by
  simp only [rationalZeroJetTwo, ambientTwoCoeff_add, targetPairTwo,
    ambientTwoCoeff_squarefreeWedge]
  simp only [aLinear, bLinear, Pi.basisFun_apply]
  by_cases hi0 : i = aCoord 0 <;> by_cases hi1 : i = aCoord 1 <;>
    by_cases hj0 : j = aCoord 0 <;> by_cases hj1 : j = aCoord 1 <;>
    by_cases hib0 : i = bCoord 0 <;> by_cases hib1 : i = bCoord 1 <;>
    by_cases hjb0 : j = bCoord 0 <;> by_cases hjb1 : j = bCoord 1 <;>
    simp_all [IsZeroJetCoord]

private theorem rationalInfinityValueTwo_support
    (i j : Fin 10)
    (h : ¬ (IsInfinityJetCoord i ∧ IsInfinityJetCoord j)) :
    ambientTwoCoeff rationalInfinityValueTwo i j = 0 := by
  rw [rationalInfinityValueTwo, targetPairTwo,
    ambientTwoCoeff_squarefreeWedge]
  simp only [aLinear, bLinear, Pi.basisFun_apply]
  by_cases hi : i = aCoord 4 <;> by_cases hj : j = aCoord 4 <;>
    by_cases hi' : i = bCoord 4 <;> by_cases hj' : j = bCoord 4 <;>
    simp_all [IsInfinityJetCoord]

private theorem rationalInfinityJetTwo_support
    (i j : Fin 10)
    (h : ¬ (IsInfinityJetCoord i ∧ IsInfinityJetCoord j)) :
    ambientTwoCoeff rationalInfinityJetTwo i j = 0 := by
  simp only [rationalInfinityJetTwo, ambientTwoCoeff_add, targetPairTwo,
    ambientTwoCoeff_squarefreeWedge]
  simp only [aLinear, bLinear, Pi.basisFun_apply]
  by_cases hi3 : i = aCoord 3 <;> by_cases hi4 : i = aCoord 4 <;>
    by_cases hj3 : j = aCoord 3 <;> by_cases hj4 : j = aCoord 4 <;>
    by_cases hib3 : i = bCoord 3 <;> by_cases hib4 : i = bCoord 4 <;>
    by_cases hjb3 : j = bCoord 3 <;> by_cases hjb4 : j = bCoord 4 <;>
    simp_all [IsInfinityJetCoord]

private theorem factorPlaneCubic_rationalZero_eq_zero_of_sparse
    (ell m : LinearForm) (i j k : Fin 10)
    (hij : ¬ (IsZeroJetCoord i ∧ IsZeroJetCoord j))
    (hik : ¬ (IsZeroJetCoord i ∧ IsZeroJetCoord k))
    (hjk : ¬ (IsZeroJetCoord j ∧ IsZeroJetCoord k)) :
    factorPlaneCubic ell m rationalZeroValueTwo rationalZeroJetTwo i j k =
      0 := by
  simp only [factorPlaneCubic, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, Pi.add_apply]
  rw [rationalZeroJetTwo_support i j hij,
    rationalZeroJetTwo_support i k hik,
    rationalZeroJetTwo_support j k hjk,
    rationalZeroValueTwo_support i j hij,
    rationalZeroValueTwo_support i k hik,
    rationalZeroValueTwo_support j k hjk]
  simp

private theorem factorPlaneCubic_rationalInfinity_eq_zero_of_sparse
    (ell m : LinearForm) (i j k : Fin 10)
    (hij : ¬ (IsInfinityJetCoord i ∧ IsInfinityJetCoord j))
    (hik : ¬ (IsInfinityJetCoord i ∧ IsInfinityJetCoord k))
    (hjk : ¬ (IsInfinityJetCoord j ∧ IsInfinityJetCoord k)) :
    factorPlaneCubic ell m rationalInfinityValueTwo
      rationalInfinityJetTwo i j k = 0 := by
  simp only [factorPlaneCubic, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, Pi.add_apply]
  rw [rationalInfinityJetTwo_support i j hij,
    rationalInfinityJetTwo_support i k hik,
    rationalInfinityJetTwo_support j k hjk,
    rationalInfinityValueTwo_support i j hij,
    rationalInfinityValueTwo_support i k hik,
    rationalInfinityValueTwo_support j k hjk]
  simp

private theorem zero_or_infinity_triple_sparse (i j k : Fin 10) :
    (¬ (IsZeroJetCoord i ∧ IsZeroJetCoord j) ∧
      ¬ (IsZeroJetCoord i ∧ IsZeroJetCoord k) ∧
      ¬ (IsZeroJetCoord j ∧ IsZeroJetCoord k)) ∨
    (¬ (IsInfinityJetCoord i ∧ IsInfinityJetCoord j) ∧
      ¬ (IsInfinityJetCoord i ∧ IsInfinityJetCoord k) ∧
      ¬ (IsInfinityJetCoord j ∧ IsInfinityJetCoord k)) := by
  have hi := zeroJetCoord_not_infinityJetCoord i
  have hj := zeroJetCoord_not_infinityJetCoord j
  have hk := zeroJetCoord_not_infinityJetCoord k
  tauto

/-- Cubic images of the zero and infinity rational value--jet planes have
trivial intersection. -/
theorem rationalZeroInfinity_cubic_intersection_eq_zero
    (ell m ell' m' : LinearForm)
    (h : factorPlaneCubic ell m rationalZeroValueTwo rationalZeroJetTwo =
      factorPlaneCubic ell' m' rationalInfinityValueTwo
        rationalInfinityJetTwo) :
    factorPlaneCubic ell m rationalZeroValueTwo rationalZeroJetTwo = 0 ∧
      factorPlaneCubic ell' m' rationalInfinityValueTwo
        rationalInfinityJetTwo = 0 := by
  have hleft : factorPlaneCubic ell m rationalZeroValueTwo
      rationalZeroJetTwo = 0 := by
    funext i j k
    have hcoord := congrFun (congrFun (congrFun h i) j) k
    rcases zero_or_infinity_triple_sparse i j k with hzero | hinfinity
    · have hz := factorPlaneCubic_rationalZero_eq_zero_of_sparse
        ell m i j k hzero.1 hzero.2.1 hzero.2.2
      simpa only [Pi.zero_apply] using hz
    · have hinf := factorPlaneCubic_rationalInfinity_eq_zero_of_sparse
        ell' m' i j k hinfinity.1 hinfinity.2.1 hinfinity.2.2
      rw [hcoord]
      simpa only [Pi.zero_apply] using hinf
  have hright : factorPlaneCubic ell' m' rationalInfinityValueTwo
      rationalInfinityJetTwo = 0 := h.symm.trans hleft
  exact ⟨hleft, hright⟩

theorem translation_rationalInfinityValueTwo :
    rationalPlaceTwoFormLinear 0 rationalInfinityValueTwo =
      rationalInfinityValueTwo := by
  rw [rationalInfinityValueTwo_eq_target,
    rationalPlaceTwoFormLinear_targetTwo]
  congr 1

theorem translation_rationalInfinityJetTwo :
    rationalPlaceTwoFormLinear 0 rationalInfinityJetTwo =
      rationalInfinityJetTwo := by
  rw [rationalInfinityJetTwo_eq_target,
    rationalPlaceTwoFormLinear_targetTwo]
  congr 1

theorem reversal_rationalOneValueTwo :
    rationalPlaceTwoFormLinear 1 rationalOneValueTwo =
      rationalOneValueTwo := by
  rw [rationalOneValueTwo_eq_target,
    rationalPlaceTwoFormLinear_targetTwo]
  congr 1

theorem reversal_rationalOneJetTwo :
    rationalPlaceTwoFormLinear 1 rationalOneJetTwo =
      rationalOneJetTwo := by
  rw [rationalOneJetTwo_eq_target,
    rationalPlaceTwoFormLinear_targetTwo]
  congr 1

/-- The one and infinity cubic images are separated by transporting them to
the zero and infinity blocks. -/
theorem rationalOneInfinity_cubic_intersection_eq_zero
    (ell m ell' m' : LinearForm)
    (h : factorPlaneCubic ell m rationalOneValueTwo rationalOneJetTwo =
      factorPlaneCubic ell' m' rationalInfinityValueTwo
        rationalInfinityJetTwo) :
    factorPlaneCubic ell m rationalOneValueTwo rationalOneJetTwo = 0 ∧
      factorPlaneCubic ell' m' rationalInfinityValueTwo
        rationalInfinityJetTwo = 0 := by
  have hmap := congrArg (rationalPlaceThreeFormLinear 0) h
  have htransformed :
      factorPlaneCubic (rationalPlaceLinear 0 ell)
          (rationalPlaceLinear 0 m) rationalZeroValueTwo
          rationalZeroJetTwo =
        factorPlaneCubic (rationalPlaceLinear 0 ell')
          (rationalPlaceLinear 0 m') rationalInfinityValueTwo
          rationalInfinityJetTwo := by
    simpa only [rationalPlaceThreeFormLinear_factorPlaneCubic,
      translation_rationalOneValueTwo, translation_rationalOneJetTwo,
      translation_rationalInfinityValueTwo,
      translation_rationalInfinityJetTwo] using hmap
  rcases rationalZeroInfinity_cubic_intersection_eq_zero
      _ _ _ _ htransformed with ⟨hleftT, hrightT⟩
  have hleftMap := congrArg (rationalPlaceThreeFormLinear 0) hleftT
  have hrightMap := congrArg (rationalPlaceThreeFormLinear 0) hrightT
  have hleft : factorPlaneCubic ell m rationalOneValueTwo
      rationalOneJetTwo = 0 := by
    simpa only [rationalPlaceThreeFormLinear_factorPlaneCubic,
      rationalPlaceLinear_involutive, translation_rationalZeroValueTwo,
      translation_rationalZeroJetTwo, map_zero] using hleftMap
  have hright : factorPlaneCubic ell' m' rationalInfinityValueTwo
      rationalInfinityJetTwo = 0 := by
    simpa only [rationalPlaceThreeFormLinear_factorPlaneCubic,
      rationalPlaceLinear_involutive, translation_rationalInfinityValueTwo,
      translation_rationalInfinityJetTwo, map_zero] using hrightMap
  exact ⟨hleft, hright⟩

/-- The zero and one cubic images are separated after reversal, which fixes
one and exchanges zero with infinity. -/
theorem rationalZeroOne_cubic_intersection_eq_zero
    (ell m ell' m' : LinearForm)
    (h : factorPlaneCubic ell m rationalZeroValueTwo rationalZeroJetTwo =
      factorPlaneCubic ell' m' rationalOneValueTwo rationalOneJetTwo) :
    factorPlaneCubic ell m rationalZeroValueTwo rationalZeroJetTwo = 0 ∧
      factorPlaneCubic ell' m' rationalOneValueTwo rationalOneJetTwo = 0 := by
  have hmap := congrArg (rationalPlaceThreeFormLinear 1) h
  have htransformed :
      factorPlaneCubic (rationalPlaceLinear 1 ell')
          (rationalPlaceLinear 1 m') rationalOneValueTwo rationalOneJetTwo =
        factorPlaneCubic (rationalPlaceLinear 1 ell)
          (rationalPlaceLinear 1 m) rationalInfinityValueTwo
          rationalInfinityJetTwo := by
    symm
    simpa only [rationalPlaceThreeFormLinear_factorPlaneCubic,
      reversal_rationalZeroValueTwo, reversal_rationalZeroJetTwo,
      reversal_rationalOneValueTwo, reversal_rationalOneJetTwo] using hmap
  rcases rationalOneInfinity_cubic_intersection_eq_zero
      _ _ _ _ htransformed with ⟨hrightT, hleftT⟩
  have hleftMap := congrArg (rationalPlaceThreeFormLinear 1) hleftT
  have hrightMap := congrArg (rationalPlaceThreeFormLinear 1) hrightT
  have hleft : factorPlaneCubic ell m rationalZeroValueTwo
      rationalZeroJetTwo = 0 := by
    simpa only [rationalPlaceThreeFormLinear_factorPlaneCubic,
      rationalPlaceLinear_involutive, reversal_rationalInfinityValueTwo,
      reversal_rationalInfinityJetTwo, map_zero] using hleftMap
  have hright : factorPlaneCubic ell' m' rationalOneValueTwo
      rationalOneJetTwo = 0 := by
    simpa only [rationalPlaceThreeFormLinear_factorPlaneCubic,
      rationalPlaceLinear_involutive, reversal_rationalOneValueTwo,
      reversal_rationalOneJetTwo, map_zero] using hrightMap
  exact ⟨hleft, hright⟩

/-- Uniform separation of cubic images at distinct rational value--jet
planes. -/
theorem rationalJet_cubic_intersection_eq_zero
    (place other : Fin 3) (hne : place ≠ other)
    (ell m ell' m' : LinearForm)
    (h : factorPlaneCubic ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right =
      factorPlaneCubic ell' m'
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right) :
    factorPlaneCubic ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right = 0 ∧
      factorPlaneCubic ell' m'
          (ExceptionalIndependentPlane.rationalJet other).left
          (ExceptionalIndependentPlane.rationalJet other).right = 0 := by
  fin_cases place <;> fin_cases other
  · exact (hne rfl).elim
  · exact rationalZeroOne_cubic_intersection_eq_zero ell m ell' m' h
  · exact rationalZeroInfinity_cubic_intersection_eq_zero ell m ell' m' h
  · exact (rationalZeroOne_cubic_intersection_eq_zero
      ell' m' ell m h.symm).symm
  · exact (hne rfl).elim
  · exact rationalOneInfinity_cubic_intersection_eq_zero ell m ell' m' h
  · exact (rationalZeroInfinity_cubic_intersection_eq_zero
      ell' m' ell m h.symm).symm
  · exact (rationalOneInfinity_cubic_intersection_eq_zero
      ell' m' ell m h.symm).symm
  · exact (hne rfl).elim

private theorem rationalJet_booleanCorrection_decomposition
    (place : Fin 3) (x y : LinearForm)
    (hcubic : factorPlaneCubic x y
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      squarefreeWedge x y +
          ambientBooleanContraction x
            (ExceptionalIndependentPlane.rationalJet place).right +
          ambientBooleanContraction y
            (ExceptionalIndependentPlane.rationalJet place).left =
        r + squarefreeWedge x z := by
  fin_cases place
  · exact rationalZero_booleanCorrection_decomposition x y hcubic
  · exact rationalOne_booleanCorrection_decomposition x y hcubic
  · exact rationalInfinity_booleanCorrection_decomposition x y hcubic

private theorem rationalJet_hadamard_mem_firstOrderEnvelope
    (place : Fin 3) :
    ambientTwoHadamard
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right ∈
      firstOrderEnvelopeTwoSpace := by
  fin_cases place
  · change ambientTwoHadamard rationalZeroValueTwo rationalZeroJetTwo ∈
      firstOrderEnvelopeTwoSpace
    rw [ambientTwoHadamard_rationalZeroValue_jet]
    exact firstOrderEnvelopeTwoSpace.zero_mem
  · change ambientTwoHadamard rationalOneValueTwo rationalOneJetTwo ∈
      firstOrderEnvelopeTwoSpace
    rw [ambientTwoHadamard_rationalOneValue_jet]
    simpa [ExceptionalIndependentPlane.right] using
      ExceptionalIndependentPlane.right_mem_firstOrderEnvelope
        (.rationalJet 1)
  · change ambientTwoHadamard rationalInfinityValueTwo
      rationalInfinityJetTwo ∈ firstOrderEnvelopeTwoSpace
    rw [ambientTwoHadamard_rationalInfinityValue_jet]
    exact firstOrderEnvelopeTwoSpace.zero_mem

/-- A single rational-local product with zero cubic part has one
decomposable quadratic shadow modulo the first-order envelope. -/
theorem rationalJet_zeroCubic_shadow_decomposition
    (place : Fin 3) (a b : F₂) (ell m : LinearForm)
    (hcubic : factorPlaneCubic ell m
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      lowProductQuadraticShadow a b ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
        r + squarefreeWedge ell z := by
  rcases rationalJet_booleanCorrection_decomposition
      place ell m hcubic with ⟨r₀, hr₀, z, hcorrection⟩
  let value := (ExceptionalIndependentPlane.rationalJet place).left
  let jet := (ExceptionalIndependentPlane.rationalJet place).right
  let hadamard := ambientTwoHadamard value jet
  let r : TwoForm := a • jet + b • value + r₀ + hadamard
  have hvalue : value ∈ firstOrderEnvelopeTwoSpace :=
    ExceptionalIndependentPlane.left_mem_firstOrderEnvelope _
  have hjet : jet ∈ firstOrderEnvelopeTwoSpace :=
    ExceptionalIndependentPlane.right_mem_firstOrderEnvelope _
  have hhadamard : hadamard ∈ firstOrderEnvelopeTwoSpace :=
    rationalJet_hadamard_mem_firstOrderEnvelope place
  refine ⟨r, ?_, z, ?_⟩
  · exact firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.add_mem
        (firstOrderEnvelopeTwoSpace.add_mem
          (firstOrderEnvelopeTwoSpace.smul_mem _ hjet)
          (firstOrderEnvelopeTwoSpace.smul_mem _ hvalue)) hr₀) hhadamard
  · change lowProductQuadraticShadow a b ell m value jet =
      r + squarefreeWedge ell z
    calc
      lowProductQuadraticShadow a b ell m value jet =
          a • jet + b • value +
            (squarefreeWedge ell m +
              ambientBooleanContraction ell jet +
              ambientBooleanContraction m value) + hadamard := by
        unfold lowProductQuadraticShadow
        module
      _ = a • jet + b • value +
          (r₀ + squarefreeWedge ell z) + hadamard := by
        rw [hcorrection]
      _ = r + squarefreeWedge ell z := by
        dsimp only [r]
        module

/-- Equal cubic parts on two distinct rational local planes cannot produce
the affine missing target coset. -/
theorem distinctRationalJet_shadow_not_missingCoset
    (place other : Fin 3) (hne : place ≠ other)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic : factorPlaneCubic ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right =
      factorPlaneCubic ell' m'
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right +
        lowProductQuadraticShadow a' b' ell' m'
          (ExceptionalIndependentPlane.rationalJet other).left
          (ExceptionalIndependentPlane.rationalJet other).right ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases rationalJet_cubic_intersection_eq_zero
      place other hne ell m ell' m' hcubic with ⟨hzero, hzero'⟩
  rcases rationalJet_zeroCubic_shadow_decomposition
      place a b ell m hzero with ⟨r, hr, z, hshadow⟩
  rcases rationalJet_zeroCubic_shadow_decomposition
      other a' b' ell' m' hzero' with ⟨r', hr', z', hshadow'⟩
  intro hmissing
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    (r + r') (firstOrderEnvelopeTwoSpace.add_mem hr hr')
      ell z ell' z' u hu
  have hdecomp :
      lowProductQuadraticShadow a b ell m
            (ExceptionalIndependentPlane.rationalJet place).left
            (ExceptionalIndependentPlane.rationalJet place).right +
          lowProductQuadraticShadow a' b' ell' m'
            (ExceptionalIndependentPlane.rationalJet other).left
            (ExceptionalIndependentPlane.rationalJet other).right =
        (r + r') + squarefreeWedge ell z + squarefreeWedge ell' z' := by
    rw [hshadow, hshadow']
    module
  exact hdecomp.symm.trans hmissing

/-- Presentation-independent version for two different rational local
planes.  Each of the six ordered bases contributes only an old-envelope
quadratic correction. -/
theorem distinctRationalJet_twoBasisChanges_shadow_not_missingCoset
    (place other : Fin 3) (hne : place ≠ other)
    (g k : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic :
      (changedLowProductHighPart g ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right).2 =
      (changedLowProductHighPart k ell' m'
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right).2)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    changedLowProductQuadraticShadow g a b ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right +
        changedLowProductQuadraticShadow k a' b' ell' m'
          (ExceptionalIndependentPlane.rationalJet other).left
          (ExceptionalIndependentPlane.rationalJet other).right ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hcanonicalCubic :
      factorPlaneCubic ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
        factorPlaneCubic ell' m'
          (ExceptionalIndependentPlane.rationalJet other).left
          (ExceptionalIndependentPlane.rationalJet other).right := by
    rw [← exceptionalPlane_basisChange_cubic
        (.rationalJet place) g ell m,
      ← exceptionalPlane_basisChange_cubic
        (.rationalJet other) k ell' m']
    exact hcubic
  let changed : TwoForm :=
    changedLowProductQuadraticShadow g a b ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right +
      changedLowProductQuadraticShadow k a' b' ell' m'
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right
  let canonical : TwoForm :=
    lowProductQuadraticShadow a b ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right +
      lowProductQuadraticShadow a' b' ell' m'
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right
  have hcorrection : changed + canonical ∈ firstOrderEnvelopeTwoSpace := by
    have hg := (exceptionalPlane_basisChange_high_and_shadow
      (.rationalJet place) g a b ell m).2
    have hk := (exceptionalPlane_basisChange_high_and_shadow
      (.rationalJet other) k a' b' ell' m').2
    change
      (changedLowProductQuadraticShadow g a b ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right +
        changedLowProductQuadraticShadow k a' b' ell' m'
          (ExceptionalIndependentPlane.rationalJet other).left
          (ExceptionalIndependentPlane.rationalJet other).right) +
      (lowProductQuadraticShadow a b ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right +
        lowProductQuadraticShadow a' b' ell' m'
          (ExceptionalIndependentPlane.rationalJet other).left
          (ExceptionalIndependentPlane.rationalJet other).right) ∈
        firstOrderEnvelopeTwoSpace
    have hreassoc :
        (changedLowProductQuadraticShadow g a b ell m
              (ExceptionalIndependentPlane.rationalJet place).left
              (ExceptionalIndependentPlane.rationalJet place).right +
            changedLowProductQuadraticShadow k a' b' ell' m'
              (ExceptionalIndependentPlane.rationalJet other).left
              (ExceptionalIndependentPlane.rationalJet other).right) +
          (lowProductQuadraticShadow a b ell m
              (ExceptionalIndependentPlane.rationalJet place).left
              (ExceptionalIndependentPlane.rationalJet place).right +
            lowProductQuadraticShadow a' b' ell' m'
              (ExceptionalIndependentPlane.rationalJet other).left
              (ExceptionalIndependentPlane.rationalJet other).right) =
        (changedLowProductQuadraticShadow g a b ell m
              (ExceptionalIndependentPlane.rationalJet place).left
              (ExceptionalIndependentPlane.rationalJet place).right +
            lowProductQuadraticShadow a b ell m
              (ExceptionalIndependentPlane.rationalJet place).left
              (ExceptionalIndependentPlane.rationalJet place).right) +
          (changedLowProductQuadraticShadow k a' b' ell' m'
              (ExceptionalIndependentPlane.rationalJet other).left
              (ExceptionalIndependentPlane.rationalJet other).right +
            lowProductQuadraticShadow a' b' ell' m'
              (ExceptionalIndependentPlane.rationalJet other).left
              (ExceptionalIndependentPlane.rationalJet other).right) := by
      module
    rw [hreassoc]
    exact firstOrderEnvelopeTwoSpace.add_mem hg hk
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    changed canonical hcorrection
  · intro v hv
    exact distinctRationalJet_shadow_not_missingCoset
      place other hne a b a' b' ell m ell' m' hcanonicalCubic v hv
  · exact hu

end

end N5
end UnrestrictedBooleanMul
