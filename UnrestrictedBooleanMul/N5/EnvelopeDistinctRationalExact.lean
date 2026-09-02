import UnrestrictedBooleanMul.N5.EnvelopeOneRotationExact
import UnrestrictedBooleanMul.N5.EnvelopeDistinctRational

/-!
# Exact Boolean shadows for distinct rational local planes

The fixed overlap on each rational value--jet plane is absorbed into its
second linear part.  Cubic-image separation then applies to the normalized
pair, while the exact one-product correction keeps the final quadratic
shadow at one decomposable form per product.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def rationalJetOverlapLinear (place : Fin 3) : LinearForm :=
  ![rationalZeroOverlapLinear, rationalOneOverlapLinear,
    rationalInfinityOverlapLinear] place

theorem quadraticOverlapCubic_rationalJet_value_jet (place : Fin 3) :
    quadraticOverlapCubic
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right =
      ambientVectorWedgeTwo (rationalJetOverlapLinear place)
        (ExceptionalIndependentPlane.rationalJet place).left := by
  fin_cases place
  · simpa [rationalJetOverlapLinear,
      ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      quadraticOverlapCubic_rationalZero_value_jet
  · simpa [rationalJetOverlapLinear,
      ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      quadraticOverlapCubic_rationalOne_value_jet
  · simpa [rationalJetOverlapLinear,
      ExceptionalIndependentPlane.left,
      ExceptionalIndependentPlane.right] using
      quadraticOverlapCubic_rationalInfinity_value_jet

theorem rationalJet_exactBooleanCorrection_decomposition
    (place : Fin 3) (x y : LinearForm)
    (hcubic : exactLowProductCubic x y
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
  · exact rationalZero_exactBooleanCorrection_decomposition x y hcubic
  · exact rationalOne_exactBooleanCorrection_decomposition x y hcubic
  · exact rationalInfinity_exactBooleanCorrection_decomposition x y hcubic

private theorem rationalJet_hadamard_mem_firstOrderEnvelope_exact
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

/-- A rational-local product with zero literal cubic has one decomposable
quadratic shadow modulo the first-order envelope. -/
theorem rationalJet_exact_zeroCubic_shadow_decomposition
    (place : Fin 3) (a b : F₂) (ell m : LinearForm)
    (hcubic : exactLowProductCubic ell m
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = 0) :
    ∃ r ∈ firstOrderEnvelopeTwoSpace, ∃ z : LinearForm,
      lowProductQuadraticShadow a b ell m
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
        r + squarefreeWedge ell z := by
  rcases rationalJet_exactBooleanCorrection_decomposition
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
    rationalJet_hadamard_mem_firstOrderEnvelope_exact place
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

theorem factorPlaneCubic_add_overlapLinear_eq_exact
    (value jet : TwoForm) (f : LinearForm)
    (hoverlap : quadraticOverlapCubic value jet =
      ambientVectorWedgeTwo f value)
    (ell m : LinearForm) :
    factorPlaneCubic ell (m + f) value jet =
      exactLowProductCubic ell m value jet := by
  funext i j k
  have ho := congrFun (congrFun (congrFun hoverlap i) j) k
  simp only [exactLowProductCubic, factorPlaneCubic,
    ambientVectorWedgeTwo, N4.vectorWedgeTwoN, Pi.add_apply] at ho ⊢
  rw [ho]
  ring

/-- Distinct rational local planes with equal literal cubics cannot produce
the missing affine target coset. -/
theorem distinctRationalJet_exact_shadow_not_missingCoset
    (place other : Fin 3) (hne : place ≠ other)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic : exactLowProductCubic ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right =
      exactLowProductCubic ell' m'
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
  let value := (ExceptionalIndependentPlane.rationalJet place).left
  let jet := (ExceptionalIndependentPlane.rationalJet place).right
  let value' := (ExceptionalIndependentPlane.rationalJet other).left
  let jet' := (ExceptionalIndependentPlane.rationalJet other).right
  let f := rationalJetOverlapLinear place
  let f' := rationalJetOverlapLinear other
  have hleft : factorPlaneCubic ell (m + f) value jet =
      exactLowProductCubic ell m value jet := by
    exact factorPlaneCubic_add_overlapLinear_eq_exact value jet f
      (quadraticOverlapCubic_rationalJet_value_jet place) ell m
  have hright : factorPlaneCubic ell' (m' + f') value' jet' =
      exactLowProductCubic ell' m' value' jet' := by
    exact factorPlaneCubic_add_overlapLinear_eq_exact value' jet' f'
      (quadraticOverlapCubic_rationalJet_value_jet other) ell' m'
  have hnormalized : factorPlaneCubic ell (m + f) value jet =
      factorPlaneCubic ell' (m' + f') value' jet' := by
    calc
      _ = exactLowProductCubic ell m value jet := hleft
      _ = exactLowProductCubic ell' m' value' jet' := hcubic
      _ = _ := hright.symm
  have hseparated := rationalJet_cubic_intersection_eq_zero
    place other hne ell (m + f) ell' (m' + f') hnormalized
  have hzero : exactLowProductCubic ell m value jet = 0 :=
    hleft.symm.trans hseparated.1
  have hzero' : exactLowProductCubic ell' m' value' jet' = 0 :=
    hright.symm.trans hseparated.2
  rcases rationalJet_exact_zeroCubic_shadow_decomposition
      place a b ell m hzero with ⟨r, hr, z, hshadow⟩
  rcases rationalJet_exact_zeroCubic_shadow_decomposition
      other a' b' ell' m' hzero' with ⟨r', hr', z', hshadow'⟩
  intro hmissing
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    (r + r') (firstOrderEnvelopeTwoSpace.add_mem hr hr')
      ell z ell' z' u hu
  have hdecomp :
      lowProductQuadraticShadow a b ell m value jet +
          lowProductQuadraticShadow a' b' ell' m' value' jet' =
        (r + r') + squarefreeWedge ell z + squarefreeWedge ell' z' := by
    rw [hshadow, hshadow']
    module
  exact hdecomp.symm.trans hmissing

/-- Presentation-free exact exclusion for two distinct rational local
planes.  Arbitrary ordered bases contribute only old-envelope quadratic
corrections. -/
theorem distinctRationalJetPresentations_exact_shadow_not_missingCoset
    (place other : Fin 3) (hne : place ≠ other)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hpresentation : IsRationalJetPresentation place q c)
    (hpresentation' : IsRationalJetPresentation other q' c')
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases hpresentation with ⟨g, hq, hc⟩
  rcases hpresentation' with ⟨k, hq', hc'⟩
  subst q
  subst c
  subst q'
  subst c'
  let ab := g.inverse.basisPair a b
  let lm := g.inverse.basisPair ell m
  let ab' := k.inverse.basisPair a' b'
  let lm' := k.inverse.basisPair ell' m'
  let P := ExceptionalIndependentPlane.rationalJet place
  let P' := ExceptionalIndependentPlane.rationalJet other
  have hgLinear : g.basisPair lm.1 lm.2 = (ell, m) := by
    simpa only [lm] using g.basisPair_apply_inverse ell m
  have hkLinear : k.basisPair lm'.1 lm'.2 = (ell', m') := by
    simpa only [lm'] using k.basisPair_apply_inverse ell' m'
  have hgHigh := g.lowProductHighClass_basisPair lm.1 lm.2 P.left P.right
  have hkHigh := k.lowProductHighClass_basisPair lm'.1 lm'.2 P'.left P'.right
  rw [hgLinear] at hgHigh
  rw [hkLinear] at hkHigh
  have hcanonicalHigh :
      lowProductHighClass lm.1 lm.2 P.left P.right =
        lowProductHighClass lm'.1 lm'.2 P'.left P'.right := by
    calc
      _ = lowProductHighClass ell m
          (g.basisPair P.left P.right).1
          (g.basisPair P.left P.right).2 := hgHigh.symm
      _ = lowProductHighClass ell' m'
          (k.basisPair P'.left P'.right).1
          (k.basisPair P'.left P'.right).2 := hhigh
      _ = _ := hkHigh
  have hcanonicalCubic : exactLowProductCubic lm.1 lm.2 P.left P.right =
      exactLowProductCubic lm'.1 lm'.2 P'.left P'.right :=
    exactLowProductCubic_eq_of_highClass_eq
      _ _ _ _ _ _ _ _ hcanonicalHigh
  let actualFirst := lowProductQuadraticShadow a b ell m
    (g.basisPair P.left P.right).1 (g.basisPair P.left P.right).2
  let actualSecond := lowProductQuadraticShadow a' b' ell' m'
    (k.basisPair P'.left P'.right).1 (k.basisPair P'.left P'.right).2
  let canonicalFirst := lowProductQuadraticShadow
    ab.1 ab.2 lm.1 lm.2 P.left P.right
  let canonicalSecond := lowProductQuadraticShadow
    ab'.1 ab'.2 lm'.1 lm'.2 P'.left P'.right
  let changedFirst := changedLowProductQuadraticShadow
    g ab.1 ab.2 lm.1 lm.2 P.left P.right
  let changedSecond := changedLowProductQuadraticShadow
    k ab'.1 ab'.2 lm'.1 lm'.2 P'.left P'.right
  have hchangedFirst : changedFirst = actualFirst := by
    simpa only [changedFirst, actualFirst, ab, lm] using
      changedLowProductQuadraticShadow_inverse g a b ell m P.left P.right
  have hchangedSecond : changedSecond = actualSecond := by
    simpa only [changedSecond, actualSecond, ab', lm'] using
      changedLowProductQuadraticShadow_inverse k a' b' ell' m' P'.left P'.right
  have hfirstCorrection : changedFirst + canonicalFirst ∈
      firstOrderEnvelopeTwoSpace := by
    exact (exceptionalPlane_basisChange_high_and_shadow
      (.rationalJet place) g ab.1 ab.2 lm.1 lm.2).2
  have hsecondCorrection : changedSecond + canonicalSecond ∈
      firstOrderEnvelopeTwoSpace := by
    exact (exceptionalPlane_basisChange_high_and_shadow
      (.rationalJet other) k ab'.1 ab'.2 lm'.1 lm'.2).2
  have hcorrection :
      (actualFirst + actualSecond) +
          (canonicalFirst + canonicalSecond) ∈
        firstOrderEnvelopeTwoSpace := by
    rw [← hchangedFirst, ← hchangedSecond]
    have hreassoc :
        (changedFirst + changedSecond) +
            (canonicalFirst + canonicalSecond) =
          (changedFirst + canonicalFirst) +
            (changedSecond + canonicalSecond) := by
      module
    rw [hreassoc]
    exact firstOrderEnvelopeTwoSpace.add_mem
      hfirstCorrection hsecondCorrection
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (actualFirst + actualSecond) (canonicalFirst + canonicalSecond)
      hcorrection
  · intro v hv
    exact distinctRationalJet_exact_shadow_not_missingCoset
      place other hne ab.1 ab.2 ab'.1 ab'.2 lm.1 lm.2 lm'.1 lm'.2
        hcanonicalCubic v hv
  · exact hu

end
end N5
end UnrestrictedBooleanMul
