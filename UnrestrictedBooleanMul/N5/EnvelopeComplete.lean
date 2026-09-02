import UnrestrictedBooleanMul.N5.EnvelopeTwoRotationShadow

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

end

end N5
end UnrestrictedBooleanMul
