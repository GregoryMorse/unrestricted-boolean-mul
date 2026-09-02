import UnrestrictedBooleanMul.N5.EnvelopeTwoRotationShadow
import UnrestrictedBooleanMul.N5.DegreeTwoTranslateShadow

/-!
# Assembly of distinct independent first-order envelope planes

This module combines the sparse Pluecker classification with the checked
one- and two-local-rotation shadow theorems.  It isolates the genuinely
remaining part of the first-order envelope argument: equal factor planes
and zero-wedge rank-one comparisons.  No circuit states or Boolean
assignments are enumerated.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Every ordered-plane basis change preserves the span of its two
generators.  This is the basis-free bridge used to transport an exceptional
plane presentation through the equal-Pluecker branch. -/
theorem PlaneBasisChange.span_basisPair_eq
    {V : Type*} [AddCommGroup V] [Module F₂ V]
    (g : PlaneBasisChange) (x y : V) :
    Submodule.span F₂ ({(g.basisPair x y).1,
        (g.basisPair x y).2} : Set V) =
      Submodule.span F₂ ({x, y} : Set V) := by
  ext z
  simp only [Submodule.mem_span_pair]
  cases g
  · rfl
  · constructor
    · rintro ⟨a, b, hab⟩
      exact ⟨b, a, by
        simpa only [PlaneBasisChange.basisPair, add_comm] using hab⟩
    · rintro ⟨a, b, hab⟩
      exact ⟨b, a, by
        simpa only [PlaneBasisChange.basisPair, add_comm] using hab⟩
  · constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨a + b, b, ?_⟩
      calc
        (a + b) • x + b • y =
            a • x + b • (x + y) := by module
        _ = z := by
          simpa only [PlaneBasisChange.basisPair] using hab
    · rintro ⟨a, b, hab⟩
      refine ⟨a + b, b, ?_⟩
      have hself : b • x + b • x = 0 := by
        rw [← two_smul F₂, show (2 : F₂) = 0 by decide, zero_smul]
      calc
        (a + b) • x + b • (x + y) =
            (a • x + b • x) + (b • x + b • y) := by
              rw [add_smul, smul_add]
        _ = a • x + (b • x + b • x) + b • y := by abel
        _ = a • x + b • y := by rw [hself, add_zero]
        _ = z := hab
  · constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨a, a + b, ?_⟩
      calc
        a • x + (a + b) • y =
            a • (x + y) + b • y := by module
        _ = z := by
          simpa only [PlaneBasisChange.basisPair] using hab
    · rintro ⟨a, b, hab⟩
      refine ⟨a, a + b, ?_⟩
      have hself : a • y + a • y = 0 := by
        rw [← two_smul F₂, show (2 : F₂) = 0 by decide, zero_smul]
      calc
        a • (x + y) + (a + b) • y =
            (a • x + a • y) + (a • y + b • y) := by
              rw [smul_add, add_smul]
        _ = a • x + (a • y + a • y) + b • y := by abel
        _ = a • x + b • y := by rw [hself, add_zero]
        _ = z := hab
  · constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨b, a + b, ?_⟩
      calc
        b • x + (a + b) • y =
            a • y + b • (x + y) := by module
        _ = z := by
          simpa only [PlaneBasisChange.basisPair] using hab
    · rintro ⟨a, b, hab⟩
      refine ⟨a + b, a, ?_⟩
      have hself : a • y + a • y = 0 := by
        rw [← two_smul F₂, show (2 : F₂) = 0 by decide, zero_smul]
      calc
        (a + b) • y + a • (x + y) =
            (a • y + b • y) + (a • x + a • y) := by
              rw [add_smul, smul_add]
        _ = a • x + (a • y + a • y) + b • y := by abel
        _ = a • x + b • y := by rw [hself, add_zero]
        _ = z := hab
  · constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨a + b, a, ?_⟩
      calc
        (a + b) • x + a • y =
            a • (x + y) + b • x := by module
        _ = z := by
          simpa only [PlaneBasisChange.basisPair] using hab
    · rintro ⟨a, b, hab⟩
      refine ⟨b, a + b, ?_⟩
      have hself : b • x + b • x = 0 := by
        rw [← two_smul F₂, show (2 : F₂) = 0 by decide, zero_smul]
      calc
        b • (x + y) + (a + b) • x =
            (b • x + b • y) + (a • x + b • x) := by
              rw [smul_add, add_smul]
        _ = a • x + (b • x + b • x) + b • y := by abel
        _ = a • x + b • y := by rw [hself, add_zero]
        _ = z := hab

/-- Vanishing of all twenty-eight first-order Pluecker coordinates is
equivalent, over `F₂`, to dependence of the two coordinate vectors. -/
theorem firstOrderPlaneCoeff_eq_zero_iff_dependent
    (x y : Fin 8 → F₂) :
    firstOrderPlaneCoeff x y = 0 ↔ x = 0 ∨ y = 0 ∨ x = y := by
  constructor
  · intro hzero
    have hwedge : squarefreeWedge x y = 0 := by
      have h := squarefreeWedge_eq_of_firstOrderPlaneCoeff_eq
        x y 0 0 (by simpa using hzero)
      simpa using h
    apply N4.dependent_of_vectorWedge_zero x y
    intro i j
    by_cases hij : i = j
    · subst j
      exact CharTwo.add_self_eq_zero _
    · have h := congrFun hwedge (quadraticPair i j hij)
      simpa only [squarefreeWedge_pair, Pi.zero_apply] using h
  · rintro (rfl | rfl | rfl)
    · funext k
      simp [firstOrderPlaneCoeff]
    · funext k
      simp [firstOrderPlaneCoeff]
    · funext k
      simp [firstOrderPlaneCoeff, mul_comm]

theorem firstOrderPlaneCoeff_ne_zero_of_linearIndependent
    (x y : Fin 8 → F₂) (hxy : LinearIndependent F₂ ![x, y]) :
    firstOrderPlaneCoeff x y ≠ 0 := by
  intro hzero
  rcases (firstOrderPlaneCoeff_eq_zero_iff_dependent x y).1 hzero with
    hx | hy | hxyEq
  · exact (hxy.ne_zero 0) (by simpa using hx)
  · exact (hxy.ne_zero 1) (by simpa using hy)
  · have heq : (![x, y] : Fin 2 → (Fin 8 → F₂)) 0 = ![x, y] 1 := by
      simpa using hxyEq
    exact Fin.zero_ne_one (hxy.injective heq)

/-- An independent first-order factor plane with zero ambient quartic wedge
is one of the three rational value--jet planes, in an arbitrary ordered
basis. -/
theorem isRationalJetPresentation_of_independent_ambientWedge_eq_zero
    (q c : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hwedge : ambientWedgeTwo q c = 0) :
    ∃ place : Fin 3, IsRationalJetPresentation place q c := by
  rcases exists_exactFirstOrderTwoCombination q hq with ⟨x, hx⟩
  rcases exists_exactFirstOrderTwoCombination c hc with ⟨y, hy⟩
  have hxMap : q = exactFirstOrderTwoMap x := by
    simpa only [exactFirstOrderTwoMap_apply] using hx
  have hyMap : c = exactFirstOrderTwoMap y := by
    simpa only [exactFirstOrderTwoMap_apply] using hy
  have hxy := exactFirstOrderCoordinates_linearIndependent
    q c x y hxMap hyMap hind
  have hcross : targetCrossWedge (exactFirstOrderCombination x)
      (exactFirstOrderCombination y) = 0 := by
    funext i k j l
    rw [← ambientWedgeTwo_targetTwo_cross]
    rw [← hx, ← hy, hwedge]
    rfl
  rcases exactFirstOrderCombination_zeroWedge_eq_local x y hcross
      (firstOrderPlaneCoeff_ne_zero_of_linearIndependent x y hxy) with
    ⟨place, hlocal⟩
  exact ⟨place, isRationalJetPresentation_of_planeCoeff_eq_local
    q c x y place hxMap hyMap hind hlocal⟩

/-- A dependent ordered quadratic pair has zero quartic exterior product. -/
theorem ambientWedgeTwo_eq_zero_of_dependent
    (q c : TwoForm)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    ambientWedgeTwo q c = 0 := by
  rcases quadraticPlaneDirections_dependent_classification q c hdep with
    rfl | rfl | hqc
  · funext i j k l
    simp [ambientWedgeTwo]
  · funext i j k l
    simp [ambientWedgeTwo]
  · subst c
    exact ambientWedgeTwo_self q

/-- Every dependent ordered pair over `F₂` can be changed to a zero-left
presentation. -/
theorem exists_planeBasisChange_zero_left_of_dependent
    (q c : TwoForm)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    ∃ (g : PlaneBasisChange) (d : TwoForm),
      g.basisPair q c = (0, d) := by
  rcases quadraticPlaneDirections_dependent_classification q c hdep with
    hq | hc | hqc
  · exact ⟨.identity, c, by simp [PlaneBasisChange.basisPair, hq]⟩
  · exact ⟨.swap, q, by simp [PlaneBasisChange.basisPair, hc]⟩
  · subst c
    have hself : q + q = 0 := by
      funext s
      exact CharTwo.add_self_eq_zero _
    exact ⟨.rotateLeft, q, by
      simp [PlaneBasisChange.basisPair, hself]⟩

/-- Presentation-free local/dependent shadow exclusion.  The independent
plane is pulled back to its canonical rational value--jet basis, while the
dependent plane is changed to `(0,d)`.  Both changes alter the total shadow
only inside the old first-order envelope. -/
theorem rationalJetPresentation_dependent_shadow_not_missingCoset
    (place : Fin 3)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hpresentation : IsRationalJetPresentation place q c)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases hpresentation with ⟨g, hqg, hcg⟩
  rcases exists_planeBasisChange_zero_left_of_dependent q' c' hdep with
    ⟨k, d, hk⟩
  let ab := g.inverse.basisPair a b
  let lm := g.inverse.basisPair ell m
  let abDep := k.basisPair a' b'
  let lmDep := k.basisPair ell' m'
  let changedLocal := changedLowProductQuadraticShadow g
    ab.1 ab.2 lm.1 lm.2
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
  let canonicalLocal := lowProductQuadraticShadow
    ab.1 ab.2 lm.1 lm.2
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
  let changedDependent := changedLowProductQuadraticShadow k
    a' b' ell' m' q' c'
  let actualLocal := lowProductQuadraticShadow a b ell m q c
  let actualDependent := lowProductQuadraticShadow a' b' ell' m' q' c'
  have hdmem : d ∈ firstOrderEnvelopeTwoSpace := by
    have hpair := k.basisPair_mem_submodule firstOrderEnvelopeTwoSpace
      q' c' hq' hc'
    rw [hk] at hpair
    exact hpair.2
  rcases hdmem with ⟨dc, hdc, hdcEq⟩
  have hdcEq' : targetTwo dc = d := hdcEq
  have hlocalEq : changedLocal = actualLocal := by
    have hinverse := changedLowProductQuadraticShadow_inverse
      g a b ell m
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right
    simpa [changedLocal, actualLocal, ab, lm, hqg, hcg] using hinverse
  have hdependentEq : changedDependent =
      lowProductQuadraticShadow abDep.1 abDep.2 lmDep.1 lmDep.2 0 d := by
    simp only [changedDependent, changedLowProductQuadraticShadow,
      abDep, lmDep]
    rw [hk]
  have hlocalCubic :
      factorPlaneCubic lm.1 lm.2
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
        factorPlaneCubic ell m q c := by
    calc
      _ = (changedLowProductHighPart g lm.1 lm.2
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right).2 :=
        (exceptionalPlane_basisChange_cubic
          (.rationalJet place) g lm.1 lm.2).symm
      _ = (lowProductHighPart ell m
          (g.basisPair
            (ExceptionalIndependentPlane.rationalJet place).left
            (ExceptionalIndependentPlane.rationalJet place).right).1
          (g.basisPair
            (ExceptionalIndependentPlane.rationalJet place).left
            (ExceptionalIndependentPlane.rationalJet place).right).2).2 := by
        simpa only [lm] using congrArg Prod.snd
          (changedLowProductHighPart_inverse g ell m
            (ExceptionalIndependentPlane.rationalJet place).left
            (ExceptionalIndependentPlane.rationalJet place).right)
      _ = factorPlaneCubic ell m q c := by
        simp only [← hqg, ← hcg, lowProductHighPart]
  have hdependentCubic :
      factorPlaneCubic lmDep.1 lmDep.2 0 d =
        factorPlaneCubic ell' m' q' c' := by
    calc
      _ = (changedLowProductHighPart k ell' m' q' c').2 := by
        simp only [changedLowProductHighPart, lmDep]
        rw [hk]
        rfl
      _ = (lowProductHighPart ell' m' q' c').2 :=
        congrArg Prod.snd (planeBasisChange_high k ell' m' q' c')
      _ = factorPlaneCubic ell' m' q' c' := rfl
  have hcanonicalCubic :
      factorPlaneCubic lm.1 lm.2
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
        factorPlaneCubic lmDep.1 lmDep.2 0 (targetTwo dc) := by
    calc
      _ = factorPlaneCubic ell m q c := hlocalCubic
      _ = factorPlaneCubic ell' m' q' c' := congrArg Prod.snd hhigh
      _ = factorPlaneCubic lmDep.1 lmDep.2 0 d := hdependentCubic.symm
      _ = factorPlaneCubic lmDep.1 lmDep.2 0 (targetTwo dc) := by
        rw [hdcEq']
  have hlocalCorrection : changedLocal + canonicalLocal ∈
      firstOrderEnvelopeTwoSpace := by
    exact (exceptionalPlane_basisChange_high_and_shadow
      (.rationalJet place) g ab.1 ab.2 lm.1 lm.2).2
  have hdependentCorrection : changedDependent + actualDependent ∈
      firstOrderEnvelopeTwoSpace := by
    exact (planeBasisChange_high_and_shadow_mod_submodule
      firstOrderEnvelopeTwoSpace k a' b' ell' m' q' c' hq' hc').2
  have hchangedExcluded : ∀ (v : TargetCoeff),
      v ∈ firstOrderEnvelopeCoeffSpace →
      canonicalLocal + changedDependent ≠
        targetTwo (firstOrderMissingCoeff + v) := by
    intro v hv
    rw [hdependentEq, ← hdcEq']
    exact rationalJet_actual_local_dependent_shadow_not_missingCoset
      place ab.1 ab.2 abDep.1 abDep.2 lm.1 lm.2 lmDep.1 lmDep.2
        dc hdc hcanonicalCubic v hv
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (actualLocal + actualDependent) (canonicalLocal + changedDependent)
  · have hreassoc :
        (actualLocal + actualDependent) +
            (canonicalLocal + changedDependent) =
          (changedLocal + canonicalLocal) +
            (changedDependent + actualDependent) := by
      rw [← hlocalEq]
      module
    rw [hreassoc]
    exact firstOrderEnvelopeTwoSpace.add_mem
      hlocalCorrection hdependentCorrection
  · exact hchangedExcluded
  · exact hu

/-- If the first plane is independent and the second is dependent, equality
of complete high parts forces the first plane into a rational local chart;
the preceding theorem then excludes the missing coset. -/
theorem independentDependentFirstOrderPlanes_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hdepWedge := ambientWedgeTwo_eq_zero_of_dependent q' c' hdep
  have hlocalWedge : ambientWedgeTwo q c = 0 := by
    have hfour := congrArg Prod.fst hhigh
    change ambientWedgeTwo q c = ambientWedgeTwo q' c' at hfour
    rw [hdepWedge] at hfour
    exact hfour
  rcases isRationalJetPresentation_of_independent_ambientWedge_eq_zero
      q c hq hc hind hlocalWedge with ⟨place, hpresentation⟩
  exact rationalJetPresentation_dependent_shadow_not_missingCoset
    place a b a' b' ell m ell' m' q c q' c'
      hq' hc' hpresentation hdep hhigh u hu

/-- Symmetric form of the mixed independent/dependent shadow exclusion. -/
theorem dependentIndependentFirstOrderPlanes_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hdep : ¬ LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  simpa only [add_comm] using
    independentDependentFirstOrderPlanes_shadow_not_missingCoset
      a' b' a b ell' m' ell m q' c' q c
        hq' hc' hq hc hind' hdep hhigh.symm u hu

/-- The generic, non-exceptional equal-plane case is characterized by
injectivity of its cubic syzygy map. -/
def CubicRigidPlane (q c : TwoForm) : Prop :=
  ∀ x y : LinearForm, factorPlaneCubic x y q c = 0 → x = 0 ∧ y = 0

/-- If the linear parts of two products on one quadratic plane agree, their
quadratic-shadow difference is already in the span of that plane. -/
theorem lowProductQuadraticShadow_same_linearParts_sum
    (a b a' b' : F₂) (ell m : LinearForm) (q c : TwoForm) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell m q c =
      (a + a') • c + (b + b') • q := by
  funext s
  simp only [lowProductQuadraticShadow, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Equal complete high parts on a cubic-rigid plane have identical linear
parts; hence their shadow difference cannot leave the first-order
envelope. -/
theorem cubicRigidPlane_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm) (q c : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hrigid : CubicRigidPlane q c)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q c)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q c ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q c := congrArg Prod.snd hhigh
  have hzero := factorPlaneCubic_difference_eq_zero
    ell m ell' m' q c hcubic
  rcases hrigid (ell + ell') (m + m') hzero with ⟨hell, hm⟩
  have hell' : ell = ell' := by
    funext i
    have hi := congrFun hell i
    change ell i + ell' i = 0 at hi
    rw [← CharTwo.sub_eq_add] at hi
    exact sub_eq_zero.mp hi
  have hm' : m = m' := by
    funext i
    have hi := congrFun hm i
    change m i + m' i = 0 at hi
    rw [← CharTwo.sub_eq_add] at hi
    exact sub_eq_zero.mp hi
  subst ell'
  subst m'
  rw [lowProductQuadraticShadow_same_linearParts_sum]
  have hr : (a + a') • c + (b + b') • q ∈
      firstOrderEnvelopeTwoSpace :=
    firstOrderEnvelopeTwoSpace.add_mem
      (firstOrderEnvelopeTwoSpace.smul_mem _ hc)
      (firstOrderEnvelopeTwoSpace.smul_mem _ hq)
  simpa using firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    ((a + a') • c + (b + b') • q) hr 0 0 0 0 u hu

/-- Cubic-rigid shadow exclusion transported across an arbitrary ordered
basis of the same independent plane. -/
theorem sharedCubicRigidPlane_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (g : PlaneBasisChange)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' = (g.basisPair q c).1)
    (hc' : c' = (g.basisPair q c).2)
    (hrigid : CubicRigidPlane q c)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  let ab' := g.inverse.basisPair a' b'
  let lm' := g.inverse.basisPair ell' m'
  let first := lowProductQuadraticShadow a b ell m q c
  let actualSecond := lowProductQuadraticShadow a' b' ell' m' q' c'
  let changedSecond := changedLowProductQuadraticShadow g
    ab'.1 ab'.2 lm'.1 lm'.2 q c
  let alignedSecond := lowProductQuadraticShadow
    ab'.1 ab'.2 lm'.1 lm'.2 q c
  have hchangedEq : changedSecond = actualSecond := by
    have hinverse := changedLowProductQuadraticShadow_inverse
      g a' b' ell' m' q c
    simpa [changedSecond, actualSecond, ab', lm', hq', hc'] using hinverse
  have halignedHigh : lowProductHighPart ell m q c =
      lowProductHighPart lm'.1 lm'.2 q c := by
    calc
      _ = lowProductHighPart ell' m' q' c' := hhigh
      _ = (changedLowProductHighPart g lm'.1 lm'.2 q c) := by
        have hinverse := changedLowProductHighPart_inverse
          g ell' m' q c
        simpa [lm', hq', hc'] using hinverse.symm
      _ = lowProductHighPart lm'.1 lm'.2 q c :=
        planeBasisChange_high g lm'.1 lm'.2 q c
  have halignedExcluded : ∀ (v : TargetCoeff),
      v ∈ firstOrderEnvelopeCoeffSpace →
      first + alignedSecond ≠ targetTwo (firstOrderMissingCoeff + v) := by
    intro v hv
    exact cubicRigidPlane_shadow_not_missingCoset
      a b ab'.1 ab'.2 ell m lm'.1 lm'.2 q c
        hq hc hrigid halignedHigh v hv
  have hcorrection : changedSecond + alignedSecond ∈
      firstOrderEnvelopeTwoSpace := by
    exact (planeBasisChange_high_and_shadow_mod_submodule
      firstOrderEnvelopeTwoSpace g ab'.1 ab'.2 lm'.1 lm'.2 q c hq hc).2
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (first + actualSecond) (first + alignedSecond)
  · have hself : first + first = 0 := by
      funext s
      exact @CharTwo.add_self_eq_zero F₂ _ _ (first s)
    have hsums :
      (first + actualSecond) + (first + alignedSecond) =
        changedSecond + alignedSecond := by
      calc
        _ = (first + first) + (actualSecond + alignedSecond) := by module
        _ = actualSecond + alignedSecond := by rw [hself, zero_add]
        _ = changedSecond + alignedSecond := by rw [hchangedEq]
    rw [hsums]
    exact hcorrection
  · exact halignedExcluded
  · exact hu

/-- Two independent first-order factor planes which are not two ordered
bases of the same plane cannot produce the missing target coset when their
complete high parts agree.  The one- and two-local Pluecker branches are
discharged by the corresponding algebraic shadow theorems. -/
theorem independentDistinctFirstOrderPlanes_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hdistinct : ∀ g : PlaneBasisChange,
      ¬ (q' = (g.basisPair q c).1 ∧ c' = (g.basisPair q c).2))
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hfour : ambientWedgeTwo q c = ambientWedgeTwo q' c' :=
    congrArg Prod.fst hhigh
  rcases independentFirstOrderPlane_classification_of_ambientWedge_eq
      q c q' c' hq hc hq' hc' hind hind' hfour with
    hsame | ⟨x, y, z, w, hx, hy, hz, hw, hone | htwo⟩
  · rcases hsame with ⟨g, hqg, hcg⟩
    exact (hdistinct g ⟨hqg, hcg⟩).elim
  · rcases hone with ⟨place, hdiff⟩
    apply oneLocalKernelDifference_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c' x y z w place
      hq hc hq' hc'
    · simpa only [exactFirstOrderTwoMap_apply] using hx
    · simpa only [exactFirstOrderTwoMap_apply] using hy
    · simpa only [exactFirstOrderTwoMap_apply] using hz
    · simpa only [exactFirstOrderTwoMap_apply] using hw
    · exact hind
    · exact hind'
    · exact hdiff
    · exact hhigh
    · exact hu
  · rcases htwo with ⟨place, other, hne, hdiff⟩
    apply twoLocalKernelDifference_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c' x y z w place other
      hq hc hq' hc'
    · simpa only [exactFirstOrderTwoMap_apply] using hx
    · simpa only [exactFirstOrderTwoMap_apply] using hy
    · simpa only [exactFirstOrderTwoMap_apply] using hz
    · simpa only [exactFirstOrderTwoMap_apply] using hw
    · exact hind
    · exact hind'
    · exact hne
    · exact hdiff
    · exact hhigh
    · exact hu

/-- Complete shadow exclusion for two independent first-order planes once
one plane has been localized to one of the seven exceptional presentations.
The equal-plane branch transports that presentation across the common span;
the genuinely different branches are the checked one- and two-rotation
cases. -/
theorem independentLocalizedFirstOrderPlanes_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hlocalized : IsExceptionalIndependentPlanePresentation q c)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hfour : ambientWedgeTwo q c = ambientWedgeTwo q' c' :=
    congrArg Prod.fst hhigh
  have hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q' c' := congrArg Prod.snd hhigh
  rcases independentFirstOrderPlane_classification_of_ambientWedge_eq
      q c q' c' hq hc hq' hc' hind hind' hfour with
    hsame | ⟨x, y, z, w, hx, hy, hz, hw, hone | htwo⟩
  · rcases hsame with ⟨basis, hqb, hcb⟩
    rcases hlocalized with ⟨P, g, hqg, hcg⟩
    have hqcSpan : Submodule.span F₂ ({q, c} : Set TwoForm) =
        Submodule.span F₂ ({P.left, P.right} : Set TwoForm) := by
      rw [hqg, hcg]
      exact g.span_basisPair_eq P.left P.right
    have hq'c'Span : Submodule.span F₂ ({q', c'} : Set TwoForm) =
        Submodule.span F₂ ({P.left, P.right} : Set TwoForm) := by
      rw [hqb, hcb]
      exact (basis.span_basisPair_eq q c).trans hqcSpan
    rcases exists_planeBasisChange_of_span_eq
        P.left P.right q' c' hind' hq'c'Span with ⟨g', hqg', hcg'⟩
    exact sharedExceptionalIndependentPlane_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c'
        ⟨P, g, g', hqg, hcg, hqg', hcg'⟩ hcubic u hu
  · rcases hone with ⟨place, hdiff⟩
    apply oneLocalKernelDifference_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c' x y z w place
      hq hc hq' hc'
    · simpa only [exactFirstOrderTwoMap_apply] using hx
    · simpa only [exactFirstOrderTwoMap_apply] using hy
    · simpa only [exactFirstOrderTwoMap_apply] using hz
    · simpa only [exactFirstOrderTwoMap_apply] using hw
    · exact hind
    · exact hind'
    · exact hdiff
    · exact hhigh
    · exact hu
  · rcases htwo with ⟨place, other, hne, hdiff⟩
    apply twoLocalKernelDifference_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c' x y z w place other
      hq hc hq' hc'
    · simpa only [exactFirstOrderTwoMap_apply] using hx
    · simpa only [exactFirstOrderTwoMap_apply] using hy
    · simpa only [exactFirstOrderTwoMap_apply] using hz
    · simpa only [exactFirstOrderTwoMap_apply] using hw
    · exact hind
    · exact hind'
    · exact hne
    · exact hdiff
    · exact hhigh
    · exact hu

/-- Complete independent-plane assembly, conditional only on the intrinsic
single-plane dichotomy used in the manuscript: the first plane is either
cubic-rigid or one of the seven exceptional local presentations. -/
theorem independentClassifiedFirstOrderPlanes_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hclassified : CubicRigidPlane q c ∨
      IsExceptionalIndependentPlanePresentation q c)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases hclassified with hrigid | hlocalized
  · by_cases hsame : ∃ g : PlaneBasisChange,
        q' = (g.basisPair q c).1 ∧ c' = (g.basisPair q c).2
    · rcases hsame with ⟨g, hqg, hcg⟩
      exact sharedCubicRigidPlane_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c' g
          hq hc hqg hcg hrigid hhigh u hu
    · exact independentDistinctFirstOrderPlanes_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c'
          hq hc hq' hc' hind hind'
          (fun g hg => hsame ⟨g, hg⟩) hhigh u hu
  · exact independentLocalizedFirstOrderPlanes_shadow_not_missingCoset
      a b a' b' ell m ell' m' q c q' c'
        hq hc hq' hc' hind hind' hlocalized hhigh u hu

/-! ## Equal planes containing a rational value direction -/

/-- The generic cubic-kernel condition for a companion to a rational value
direction.  It says that every syzygy is the unavoidable two-dimensional
Koszul kernel on the rational value factors. -/
def RationalValueRegularCompanion (place : Fin 3) (c : TwoForm) : Prop :=
  ∀ x y : LinearForm,
    factorPlaneCubic x y (targetTwo (rationalValueCoeff place)) c = 0 →
      x = 0 ∧ ∃ p s : F₂,
        y = p • rationalValueA place + s • rationalValueB place

/-- Equal complete high parts on a regular rational-value plane cannot have
quadratic-shadow difference in the missing target coset.  The proof is
purely algebraic: the generic cubic kernel leaves one decomposable exterior
product modulo the old envelope. -/
theorem rationalValueRegularCompanion_shadow_not_missingCoset
    (place : Fin 3) (c : TwoForm)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hregular : RationalValueRegularCompanion place c)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hcubic :
      factorPlaneCubic ell m (targetTwo (rationalValueCoeff place)) c =
        factorPlaneCubic ell' m' (targetTwo (rationalValueCoeff place)) c)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m
          (targetTwo (rationalValueCoeff place)) c +
        lowProductQuadraticShadow a' b' ell' m'
          (targetTwo (rationalValueCoeff place)) c ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  let x : LinearForm := ell + ell'
  let y : LinearForm := m + m'
  have hx : ell + x = ell' := by
    change ell + (ell + ell') = ell'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hy : m + y = m' := by
    change m + (m + m') = m'
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hcubicZero :
      factorPlaneCubic x y (targetTwo (rationalValueCoeff place)) c = 0 :=
    factorPlaneCubic_difference_eq_zero ell m ell' m'
      (targetTwo (rationalValueCoeff place)) c hcubic
  rcases hregular x y hcubicZero with ⟨hx0, p, s, hyspan⟩
  have hcorrection :
      squarefreeWedge x y + ambientBooleanContraction x c +
          ambientBooleanContraction y
            (targetTwo (rationalValueCoeff place)) =
        (p + s) • targetTwo (rationalValueCoeff place) +
          squarefreeWedge x 0 := by
    rw [hx0, hyspan, targetTwo_rationalValueCoeff,
      ambientBooleanContraction_factorSpan_of_disjoint
        (rationalValueA place) (rationalValueB place)
        (rationalValue_factors_disjoint place) p s]
    simp
  rcases lowProductShadow_decomposition_of_correction
      firstOrderEnvelopeTwoSpace a b a' b' ell m x y
      (targetTwo (rationalValueCoeff place)) c
      (rationalValueTwo_mem_firstOrderEnvelope place) hc
      ((p + s) • targetTwo (rationalValueCoeff place))
      (firstOrderEnvelopeTwoSpace.smul_mem _
        (rationalValueTwo_mem_firstOrderEnvelope place))
      0 hcorrection with
    ⟨r, hr, v, w, v', w', hdecomp⟩
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    r hr v w v' w' u hu
  have hdecomp' :
      lowProductQuadraticShadow a b ell m
            (targetTwo (rationalValueCoeff place)) c +
          lowProductQuadraticShadow a' b' ell' m'
            (targetTwo (rationalValueCoeff place)) c =
        r + squarefreeWedge v w + squarefreeWedge v' w' := by
    simpa only [hx, hy] using hdecomp
  exact hdecomp'.symm.trans hmissing

/-- Presentation-independent interface for a single quadratic plane: equal
cubic parts on the displayed ordered basis have shadow difference outside
the missing target coset. -/
def CubicEqualPlaneShadowExcluded (q c : TwoForm) : Prop :=
  ∀ (a b a' b' : F₂) (ell m ell' m' : LinearForm),
    factorPlaneCubic ell m q c = factorPlaneCubic ell' m' q c →
      ∀ (u : TargetCoeff), u ∈ firstOrderEnvelopeCoeffSpace →
        lowProductQuadraticShadow a b ell m q c +
            lowProductQuadraticShadow a' b' ell' m' q c ≠
          targetTwo (firstOrderMissingCoeff + u)

theorem rationalValueRegularCompanion_shadowExcluded
    (place : Fin 3) (c : TwoForm)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hregular : RationalValueRegularCompanion place c) :
    CubicEqualPlaneShadowExcluded
      (targetTwo (rationalValueCoeff place)) c := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact rationalValueRegularCompanion_shadow_not_missingCoset
    place c hc hregular a b a' b' ell m ell' m' hcubic u hu

/-- Canonical equal-plane exclusion for the unique non-rational translate
of the degree-two place. -/
theorem degreeTwoTranslate_shadowExcluded :
    CubicEqualPlaneShadowExcluded degreeTwoTranslateLeftTwo
      degreeTwoTranslateRightTwo := by
  intro a b a' b' ell m ell' m' hcubic u hu
  exact degreeTwoTranslate_shadow_not_missingCoset
    a b a' b' ell m ell' m' hcubic u hu

/-- A shadow exclusion for one ordered basis of a first-order plane
transports to two independently chosen ordered bases of that plane. -/
theorem cubicEqualPlaneShadowExcluded_twoBasisChanges
    (q c : TwoForm) (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hshadow : CubicEqualPlaneShadowExcluded q c)
    (g k : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hhigh :
      lowProductHighPart ell m
          (g.basisPair q c).1 (g.basisPair q c).2 =
        lowProductHighPart ell' m'
          (k.basisPair q c).1 (k.basisPair q c).2)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m
          (g.basisPair q c).1 (g.basisPair q c).2 +
        lowProductQuadraticShadow a' b' ell' m'
          (k.basisPair q c).1 (k.basisPair q c).2 ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  let ab := g.inverse.basisPair a b
  let lm := g.inverse.basisPair ell m
  let ab' := k.inverse.basisPair a' b'
  let lm' := k.inverse.basisPair ell' m'
  let actualFirst := lowProductQuadraticShadow a b ell m
    (g.basisPair q c).1 (g.basisPair q c).2
  let actualSecond := lowProductQuadraticShadow a' b' ell' m'
    (k.basisPair q c).1 (k.basisPair q c).2
  let changedFirst := changedLowProductQuadraticShadow
    g ab.1 ab.2 lm.1 lm.2 q c
  let changedSecond := changedLowProductQuadraticShadow
    k ab'.1 ab'.2 lm'.1 lm'.2 q c
  let canonicalFirst := lowProductQuadraticShadow
    ab.1 ab.2 lm.1 lm.2 q c
  let canonicalSecond := lowProductQuadraticShadow
    ab'.1 ab'.2 lm'.1 lm'.2 q c
  have hchangedFirst : changedFirst = actualFirst := by
    simpa [changedFirst, actualFirst, ab, lm] using
      changedLowProductQuadraticShadow_inverse g a b ell m q c
  have hchangedSecond : changedSecond = actualSecond := by
    simpa [changedSecond, actualSecond, ab', lm'] using
      changedLowProductQuadraticShadow_inverse k a' b' ell' m' q c
  have hcanonicalHigh :
      lowProductHighPart lm.1 lm.2 q c =
        lowProductHighPart lm'.1 lm'.2 q c := by
    calc
      _ = changedLowProductHighPart g lm.1 lm.2 q c :=
        (planeBasisChange_high g lm.1 lm.2 q c).symm
      _ = lowProductHighPart ell m
          (g.basisPair q c).1 (g.basisPair q c).2 := by
        simpa [lm] using changedLowProductHighPart_inverse g ell m q c
      _ = lowProductHighPart ell' m'
          (k.basisPair q c).1 (k.basisPair q c).2 := hhigh
      _ = changedLowProductHighPart k lm'.1 lm'.2 q c := by
        simpa [lm'] using
          (changedLowProductHighPart_inverse k ell' m' q c).symm
      _ = lowProductHighPart lm'.1 lm'.2 q c :=
        planeBasisChange_high k lm'.1 lm'.2 q c
  have hcanonicalCubic :
      factorPlaneCubic lm.1 lm.2 q c =
        factorPlaneCubic lm'.1 lm'.2 q c :=
    congrArg Prod.snd hcanonicalHigh
  have hcanonicalExcluded : ∀ (v : TargetCoeff),
      v ∈ firstOrderEnvelopeCoeffSpace →
      canonicalFirst + canonicalSecond ≠
        targetTwo (firstOrderMissingCoeff + v) := by
    intro v hv
    exact hshadow ab.1 ab.2 ab'.1 ab'.2 lm.1 lm.2 lm'.1 lm'.2
      hcanonicalCubic v hv
  have hchangedCorrection :
      (changedFirst + changedSecond) +
          (canonicalFirst + canonicalSecond) ∈
        firstOrderEnvelopeTwoSpace := by
    exact twoPlaneBasisChanges_shadow_sum_add_original_mem
      firstOrderEnvelopeTwoSpace g k
      ab.1 ab.2 ab'.1 ab'.2 lm.1 lm.2 lm'.1 lm'.2
      q c q c hq hc hq hc
  have hactualCorrection :
      (actualFirst + actualSecond) +
          (canonicalFirst + canonicalSecond) ∈
        firstOrderEnvelopeTwoSpace := by
    rw [← hchangedFirst, ← hchangedSecond]
    exact hchangedCorrection
  exact missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (actualFirst + actualSecond) (canonicalFirst + canonicalSecond)
      hactualCorrection hcanonicalExcluded u hu

/-- Intrinsic equal-plane wrapper for the non-rational degree-two translate;
the two products may use independently chosen ordered bases. -/
theorem sharedDegreeTwoTranslatePlane_shadow_not_missingCoset
    (g k : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hhigh :
      lowProductHighPart ell m
          (g.basisPair degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo).1
          (g.basisPair degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo).2 =
        lowProductHighPart ell' m'
          (k.basisPair degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo).1
          (k.basisPair degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo).2)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m
          (g.basisPair degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo).1
          (g.basisPair degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo).2 +
        lowProductQuadraticShadow a' b' ell' m'
          (k.basisPair degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo).1
          (k.basisPair degreeTwoTranslateLeftTwo
            degreeTwoTranslateRightTwo).2 ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  exact cubicEqualPlaneShadowExcluded_twoBasisChanges
    degreeTwoTranslateLeftTwo degreeTwoTranslateRightTwo
    degreeTwoTranslateLeftTwo_mem_firstOrderEnvelope
    degreeTwoTranslateRightTwo_mem_firstOrderEnvelope
    degreeTwoTranslate_shadowExcluded
    g k a b a' b' ell m ell' m' hhigh u hu

/-- Intrinsic equal-plane wrapper for a regular rational-value companion.
Both products may use arbitrary ordered bases of the common plane. -/
theorem sharedRationalValueRegularPlane_shadow_not_missingCoset
    (place : Fin 3) (c : TwoForm)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hregular : RationalValueRegularCompanion place c)
    (g k : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (hhigh :
      lowProductHighPart ell m
          (g.basisPair (targetTwo (rationalValueCoeff place)) c).1
          (g.basisPair (targetTwo (rationalValueCoeff place)) c).2 =
        lowProductHighPart ell' m'
          (k.basisPair (targetTwo (rationalValueCoeff place)) c).1
          (k.basisPair (targetTwo (rationalValueCoeff place)) c).2)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m
          (g.basisPair (targetTwo (rationalValueCoeff place)) c).1
          (g.basisPair (targetTwo (rationalValueCoeff place)) c).2 +
        lowProductQuadraticShadow a' b' ell' m'
          (k.basisPair (targetTwo (rationalValueCoeff place)) c).1
          (k.basisPair (targetTwo (rationalValueCoeff place)) c).2 ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  exact cubicEqualPlaneShadowExcluded_twoBasisChanges
    (targetTwo (rationalValueCoeff place)) c
    (rationalValueTwo_mem_firstOrderEnvelope place) hc
    (rationalValueRegularCompanion_shadowExcluded place c hc hregular)
    g k a b a' b' ell m ell' m' hhigh u hu

end

end N5
end UnrestrictedBooleanMul
