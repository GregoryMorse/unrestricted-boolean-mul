import UnrestrictedBooleanMul.N5.EnvelopeDistinctRational

/-!
# Algebraic shadow exclusion for two rational rotations

This module rewires a sum of two low products along an independent
intermediate plane.  The proof uses only bilinearity and the six ordered
bases of a two-dimensional `F₂`-plane; it does not enumerate circuits or
Boolean assignments.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem basisPair_components_mem_span
    {V : Type*} [AddCommGroup V] [Module F₂ V]
    (g : PlaneBasisChange) (x y : V) :
    (g.basisPair x y).1 ∈ Submodule.span F₂ ({x, y} : Set V) ∧
      (g.basisPair x y).2 ∈ Submodule.span F₂ ({x, y} : Set V) := by
  have hx : x ∈ Submodule.span F₂ ({x, y} : Set V) :=
    Submodule.subset_span (by simp)
  have hy : y ∈ Submodule.span F₂ ({x, y} : Set V) :=
    Submodule.subset_span (by simp)
  have hxy := Submodule.add_mem (Submodule.span F₂ ({x, y} : Set V)) hx hy
  cases g <;> simp only [PlaneBasisChange.basisPair]
  · exact ⟨hx, hy⟩
  · exact ⟨hy, hx⟩
  · exact ⟨hx, hxy⟩
  · exact ⟨hxy, hy⟩
  · exact ⟨hy, hxy⟩
  · exact ⟨hxy, hx⟩

/-- Every one of the six ordered basis changes preserves the generated
two-dimensional submodule. -/
theorem PlaneBasisChange.span_basisPair
    {V : Type*} [AddCommGroup V] [Module F₂ V]
    (g : PlaneBasisChange) (x y : V) :
    Submodule.span F₂
        ({(g.basisPair x y).1, (g.basisPair x y).2} : Set V) =
      Submodule.span F₂ ({x, y} : Set V) := by
  let pair := g.basisPair x y
  have hforward := basisPair_components_mem_span g x y
  have hinverse := basisPair_components_mem_span g.inverse pair.1 pair.2
  have hrecover : g.inverse.basisPair pair.1 pair.2 = (x, y) := by
    exact g.inverse_basisPair_apply x y
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with hz | hz
    · subst z
      exact hforward.1
    · subst z
      exact hforward.2
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with hz | hz
    · subst z
      rw [Prod.ext_iff] at hrecover
      simpa [pair, hrecover.1] using hinverse.1
    · subst z
      rw [Prod.ext_iff] at hrecover
      simpa [pair, hrecover.2] using hinverse.2

private theorem quadraticPlaneDirections_linearIndependent_of_nonzero_ne
    (q c : TwoForm) (hq : q ≠ 0) (hc : c ≠ 0) (hqc : q ≠ c) :
    LinearIndependent F₂ (quadraticPlaneDirections q c) := by
  change LinearIndependent F₂ ![c, q]
  rw [linearIndependent_fin2]
  change q ≠ 0 ∧ ∀ a : F₂, a • q ≠ c
  refine ⟨hq, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hc
  · simpa using hqc

/-- An ordered basis change preserves independence of quadratic-plane
directions. -/
theorem PlaneBasisChange.quadraticPlaneDirections_linearIndependent
    (g : PlaneBasisChange) (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    LinearIndependent F₂
      (quadraticPlaneDirections (g.basisPair q c).1
        (g.basisPair q c).2) := by
  rcases quadraticPlaneDirections_independent_nonzero_ne q c hind with
    ⟨hq, hc, hqc⟩
  have hsum : q + c ≠ 0 := by
    intro h
    apply hqc
    funext s
    exact CharTwo.add_eq_zero.mp (congrFun h s)
  cases g <;> simp only [PlaneBasisChange.basisPair]
  · exact quadraticPlaneDirections_linearIndependent_of_nonzero_ne
      q c hq hc hqc
  · exact quadraticPlaneDirections_linearIndependent_of_nonzero_ne
      c q hc hq hqc.symm
  · exact quadraticPlaneDirections_linearIndependent_of_nonzero_ne
      q (q + c) hq hsum (by
        intro h
        apply hc
        funext s
        have hs := congrFun h s
        change q s = q s + c s at hs
        exact (add_left_cancel
          (show q s + 0 = q s + c s by simpa using hs)).symm)
  · exact quadraticPlaneDirections_linearIndependent_of_nonzero_ne
      (q + c) c hsum hc (by
        intro h
        apply hq
        funext s
        have hs := congrFun h s
        change q s + c s = c s at hs
        exact add_right_cancel
          (show q s + c s = 0 + c s by simpa using hs))
  · exact quadraticPlaneDirections_linearIndependent_of_nonzero_ne
      c (q + c) hc hsum (by
        intro h
        apply hq
        funext s
        have hs := congrFun h s
        change c s = q s + c s at hs
        exact add_right_cancel
          (show q s + c s = 0 + c s by simpa using hs.symm))
  · exact quadraticPlaneDirections_linearIndependent_of_nonzero_ne
      (q + c) q hsum hq (by
        intro h
        apply hc
        funext s
        have hs := congrFun h s
        change q s + c s = q s at hs
        exact add_left_cancel
          (show q s + c s = q s + 0 by simpa using hs))

/-- Bilinear two-product rewire.  The new quadratic planes are
`(q,c+c')` and `(q+q',c')`. -/
theorem lowProductQuadraticShadow_twoProduct_rewire
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' =
      lowProductQuadraticShadow a (b + b') ell (m + m') q (c + c') +
        lowProductQuadraticShadow (a + a') b' (ell + ell') m'
          (q + q') c' := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [Pi.add_apply, lowProductQuadraticShadow_pair]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Cubic component of the general two-product rewire. -/
theorem factorPlaneCubic_twoProduct_rewire
    (ell m ell' m' : LinearForm) (q c q' c' : TwoForm) :
    factorPlaneCubic ell m q c + factorPlaneCubic ell' m' q' c' =
      factorPlaneCubic ell (m + m') q (c + c') +
        factorPlaneCubic (ell + ell') m' (q + q') c' := by
  funext i j k
  simp only [factorPlaneCubic, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, ambientTwoCoeff_add, Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Quartic component of the general two-product rewire. -/
theorem ambientWedgeTwo_twoProduct_rewire
    (q c q' c' : TwoForm) :
    ambientWedgeTwo q c + ambientWedgeTwo q' c' =
      ambientWedgeTwo q (c + c') + ambientWedgeTwo (q + q') c' := by
  funext i j k l
  simp only [ambientWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff_add, Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Equality of the original high parts becomes equality of the two rewired
high parts. -/
theorem lowProductHighPart_twoProduct_rewire
    (ell m ell' m' : LinearForm) (q c q' c' : TwoForm)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c') :
    lowProductHighPart ell (m + m') q (c + c') =
      lowProductHighPart (ell + ell') m' (q + q') c' := by
  have hquartic : ambientWedgeTwo q c = ambientWedgeTwo q' c' :=
    congrArg Prod.fst hhigh
  have hcubic : factorPlaneCubic ell m q c =
      factorPlaneCubic ell' m' q' c' := congrArg Prod.snd hhigh
  apply Prod.ext
  · have hrewire := ambientWedgeTwo_twoProduct_rewire q c q' c'
    have hzero :
        ambientWedgeTwo q (c + c') + ambientWedgeTwo (q + q') c' = 0 := by
      rw [← hrewire, hquartic]
      funext i j k l
      exact @CharTwo.add_self_eq_zero F₂ _ _
        (ambientWedgeTwo q' c' i j k l)
    funext i j k l
    exact CharTwo.add_eq_zero.mp
      (congrFun (congrFun (congrFun (congrFun hzero i) j) k) l)
  · have hrewire := factorPlaneCubic_twoProduct_rewire
      ell m ell' m' q c q' c'
    have hzero :
        factorPlaneCubic ell (m + m') q (c + c') +
          factorPlaneCubic (ell + ell') m' (q + q') c' = 0 := by
      rw [← hrewire, hcubic]
      funext i j k
      exact @CharTwo.add_self_eq_zero F₂ _ _
        (factorPlaneCubic ell' m' q' c' i j k)
    funext i j k
    exact CharTwo.add_eq_zero.mp
      (congrFun (congrFun (congrFun hzero i) j) k)

/-- The canonical rational value--jet plane is independent. -/
theorem rationalJet_quadraticPlaneDirections_linearIndependent
    (place : Fin 3) :
    LinearIndependent F₂ (quadraticPlaneDirections
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right) := by
  have hmap := (firstOrderLocalCoordinates_linearIndependent place).map'
      exactFirstOrderTwoMap
      (LinearMap.ker_eq_bot.mpr exactFirstOrderTwoMap_injective)
  have hleft : (ExceptionalIndependentPlane.rationalJet place).left ≠ 0 := by
    rw [← exactFirstOrderTwoMap_localValueCoordinates]
    simpa only [Function.comp_apply, Matrix.cons_val_zero] using
      hmap.ne_zero 0
  have hright : (ExceptionalIndependentPlane.rationalJet place).right ≠ 0 := by
    rw [← exactFirstOrderTwoMap_localJetCoordinates]
    simpa only [Function.comp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      hmap.ne_zero 1
  have hne : (ExceptionalIndependentPlane.rationalJet place).left ≠
      (ExceptionalIndependentPlane.rationalJet place).right := by
    intro h
    have heq :
        (exactFirstOrderTwoMap ∘ ![firstOrderLocalValueCoordinates place,
          firstOrderLocalJetCoordinates place]) 0 =
        (exactFirstOrderTwoMap ∘ ![firstOrderLocalValueCoordinates place,
          firstOrderLocalJetCoordinates place]) 1 := by
      simpa only [Function.comp_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, exactFirstOrderTwoMap_localValueCoordinates,
        exactFirstOrderTwoMap_localJetCoordinates] using h
    exact Fin.zero_ne_one (hmap.injective heq)
  exact quadraticPlaneDirections_linearIndependent_of_nonzero_ne
    _ _ hleft hright hne

/-- An arbitrary ordered basis of the rational value--jet plane at one
place. -/
def IsRationalJetPresentation
    (place : Fin 3) (q c : TwoForm) : Prop :=
  ∃ g : PlaneBasisChange,
    q = (g.basisPair
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right).1 ∧
      c = (g.basisPair
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right).2

theorem isRationalJetPresentation_of_span_eq
    (place : Fin 3) (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hspan : Submodule.span F₂ ({q, c} : Set TwoForm) =
      Submodule.span F₂
        ({(ExceptionalIndependentPlane.rationalJet place).left,
          (ExceptionalIndependentPlane.rationalJet place).right} : Set TwoForm)) :
    IsRationalJetPresentation place q c := by
  rcases exists_planeBasisChange_of_span_eq
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
      q c hind hspan with ⟨g, hq, hc⟩
  exact ⟨g, hq, hc⟩

/-- Presentation-free exclusion for two distinct rational value--jet
planes. -/
theorem distinctRationalJetPresentations_shadow_not_missingCoset
    (place other : Fin 3) (hne : place ≠ other)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hpresentation : IsRationalJetPresentation place q c)
    (hpresentation' : IsRationalJetPresentation other q' c')
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
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
  let ab' := k.inverse.basisPair a' b'
  let lm := g.inverse.basisPair ell m
  let lm' := k.inverse.basisPair ell' m'
  have hchangedHigh :
      changedLowProductHighPart g lm.1 lm.2
          (ExceptionalIndependentPlane.rationalJet place).left
          (ExceptionalIndependentPlane.rationalJet place).right =
        changedLowProductHighPart k lm'.1 lm'.2
          (ExceptionalIndependentPlane.rationalJet other).left
          (ExceptionalIndependentPlane.rationalJet other).right := by
    rw [show lm = g.inverse.basisPair ell m by rfl,
      show lm' = k.inverse.basisPair ell' m' by rfl,
      changedLowProductHighPart_inverse,
      changedLowProductHighPart_inverse]
    exact hhigh
  have hexclusion := distinctRationalJet_twoBasisChanges_shadow_not_missingCoset
    place other hne g k ab.1 ab.2 ab'.1 ab'.2 lm.1 lm.2 lm'.1 lm'.2
      (congrArg Prod.snd hchangedHigh) u hu
  rw [show ab = g.inverse.basisPair a b by rfl,
    show ab' = k.inverse.basisPair a' b' by rfl,
    show lm = g.inverse.basisPair ell m by rfl,
    show lm' = k.inverse.basisPair ell' m' by rfl,
    changedLowProductQuadraticShadow_inverse,
    changedLowProductQuadraticShadow_inverse] at hexclusion
  exact hexclusion

theorem isRationalJetPresentation_of_iterated_basisPair
    (place : Fin 3) (h f : PlaneBasisChange)
    (p t q c : TwoForm)
    (hloc : h.basisPair
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = (p, t))
    (hpair : (q, c) = f.basisPair p t) :
    IsRationalJetPresentation place q c := by
  have hcanonical :=
    rationalJet_quadraticPlaneDirections_linearIndependent place
  have hpt := h.quadraticPlaneDirections_linearIndependent _ _ hcanonical
  rw [hloc] at hpt
  have hqc := f.quadraticPlaneDirections_linearIndependent p t hpt
  rw [← hpair] at hqc
  have hqpair : q = (f.basisPair p t).1 := by
    simpa only using congrArg Prod.fst hpair
  have hcpair : c = (f.basisPair p t).2 := by
    simpa only using congrArg Prod.snd hpair
  apply isRationalJetPresentation_of_span_eq place q c hqc
  calc
    Submodule.span F₂ ({q, c} : Set TwoForm) =
        Submodule.span F₂
          ({(f.basisPair p t).1, (f.basisPair p t).2} : Set TwoForm) := by
      rw [hqpair, hcpair]
    _ = Submodule.span F₂ ({p, t} : Set TwoForm) :=
      f.span_basisPair p t
    _ = Submodule.span F₂
        ({(ExceptionalIndependentPlane.rationalJet place).left,
          (ExceptionalIndependentPlane.rationalJet place).right} : Set TwoForm) := by
      have hspan := h.span_basisPair
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right
      rw [hloc] at hspan
      exact hspan

/-- The direct algebraic two-rotation rewire once the middle ordered bases
differ by one of the four changes that do not preserve their first line. -/
theorem rationalTwoRotation_normalForm_shadow_not_missingCoset
    (place other : Fin 3) (hne : place ≠ other)
    (h k e : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (p v t r s z : TwoForm)
    (hplace : h.basisPair
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = (p, t))
    (hother : k.basisPair
      (ExceptionalIndependentPlane.rationalJet other).left
      (ExceptionalIndependentPlane.rationalJet other).right = (r, z))
    (hmiddle : e.basisPair p v = (r, s))
    (he : e = .swap ∨ e = .rotateLeft ∨
      e = .cycleRight ∨ e = .cycleLeft)
    (hhigh : lowProductHighPart ell m p (v + t) =
      lowProductHighPart ell' m' (s + z) r)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m p (v + t) +
        lowProductQuadraticShadow a' b' ell' m' (s + z) r ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hrewiredHigh := lowProductHighPart_twoProduct_rewire
    ell m ell' m' p (v + t) (s + z) r hhigh
  have hrewiredShadow := lowProductQuadraticShadow_twoProduct_rewire
    a b a' b' ell m ell' m' p (v + t) (s + z) r
  rcases he with rfl | rfl | rfl | rfl
  · simp only [PlaneBasisChange.basisPair] at hmiddle
    have hr := congrArg Prod.fst hmiddle
    have hs := congrArg Prod.snd hmiddle
    simp only at hr hs
    subst r
    subst s
    have hpairPlace :
        (p, (v + t) + v) = PlaneBasisChange.identity.basisPair p t := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpairOther :
        (p + (p + z), v) = PlaneBasisChange.swap.basisPair v z := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpresentation := isRationalJetPresentation_of_iterated_basisPair
      place h .identity p t p ((v + t) + v) hplace hpairPlace
    have hpresentation' := isRationalJetPresentation_of_iterated_basisPair
      other k .swap v z (p + (p + z)) v hother hpairOther
    rw [hrewiredShadow]
    exact distinctRationalJetPresentations_shadow_not_missingCoset
      place other hne a (b + b') (a + a') b'
        ell (m + m') (ell + ell') m'
        p ((v + t) + v) (p + (p + z)) v
        hpresentation hpresentation' hrewiredHigh u hu
  · simp only [PlaneBasisChange.basisPair] at hmiddle
    have hr := congrArg Prod.fst hmiddle
    have hs := congrArg Prod.snd hmiddle
    simp only at hr hs
    subst r
    subst s
    have hpairPlace :
        (p, (v + t) + (p + v)) =
          PlaneBasisChange.rotateRight.basisPair p t := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpairOther :
        (p + (v + z), p + v) =
          PlaneBasisChange.cycleLeft.basisPair (p + v) z := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpresentation := isRationalJetPresentation_of_iterated_basisPair
      place h .rotateRight p t p ((v + t) + (p + v)) hplace hpairPlace
    have hpresentation' := isRationalJetPresentation_of_iterated_basisPair
      other k .cycleLeft (p + v) z (p + (v + z)) (p + v)
        hother hpairOther
    rw [hrewiredShadow]
    exact distinctRationalJetPresentations_shadow_not_missingCoset
      place other hne a (b + b') (a + a') b'
        ell (m + m') (ell + ell') m'
        p ((v + t) + (p + v)) (p + (v + z)) (p + v)
        hpresentation hpresentation' hrewiredHigh u hu
  · simp only [PlaneBasisChange.basisPair] at hmiddle
    have hr := congrArg Prod.fst hmiddle
    have hs := congrArg Prod.snd hmiddle
    simp only at hr hs
    subst r
    subst s
    have hpairPlace :
        (p, (v + t) + v) = PlaneBasisChange.identity.basisPair p t := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpairOther :
        (p + ((p + v) + z), v) =
          PlaneBasisChange.cycleLeft.basisPair v z := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpresentation := isRationalJetPresentation_of_iterated_basisPair
      place h .identity p t p ((v + t) + v) hplace hpairPlace
    have hpresentation' := isRationalJetPresentation_of_iterated_basisPair
      other k .cycleLeft v z (p + ((p + v) + z)) v hother hpairOther
    rw [hrewiredShadow]
    exact distinctRationalJetPresentations_shadow_not_missingCoset
      place other hne a (b + b') (a + a') b'
        ell (m + m') (ell + ell') m'
        p ((v + t) + v) (p + ((p + v) + z)) v
        hpresentation hpresentation' hrewiredHigh u hu
  · simp only [PlaneBasisChange.basisPair] at hmiddle
    have hr := congrArg Prod.fst hmiddle
    have hs := congrArg Prod.snd hmiddle
    simp only at hr hs
    subst r
    subst s
    have hpairPlace :
        (p, (v + t) + (p + v)) =
          PlaneBasisChange.rotateRight.basisPair p t := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpairOther :
        (p + (p + z), p + v) =
          PlaneBasisChange.swap.basisPair (p + v) z := by
      apply Prod.ext <;> simp only [PlaneBasisChange.basisPair] <;>
        funext x <;> simp only [Pi.add_apply] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    have hpresentation := isRationalJetPresentation_of_iterated_basisPair
      place h .rotateRight p t p ((v + t) + (p + v)) hplace hpairPlace
    have hpresentation' := isRationalJetPresentation_of_iterated_basisPair
      other k .swap (p + v) z (p + (p + z)) (p + v) hother hpairOther
    rw [hrewiredShadow]
    exact distinctRationalJetPresentations_shadow_not_missingCoset
      place other hne a (b + b') (a + a') b'
        ell (m + m') (ell + ell') m'
        p ((v + t) + (p + v)) (p + (p + z)) (p + v)
        hpresentation hpresentation' hrewiredHigh u hu

private theorem eq_zero_of_mem_distinct_local_coordinate_spans
    (place other : Fin 3) (hne : place ≠ other)
    (x : Fin 8 → F₂)
    (hx : x ∈ Submodule.span F₂
      ({firstOrderLocalValueCoordinates place,
        firstOrderLocalJetCoordinates place} : Set (Fin 8 → F₂)))
    (hx' : x ∈ Submodule.span F₂
      ({firstOrderLocalValueCoordinates other,
        firstOrderLocalJetCoordinates other} : Set (Fin 8 → F₂))) :
    x = 0 := by
  rcases Submodule.mem_span_pair.mp hx with ⟨a, b, hab⟩
  rcases Submodule.mem_span_pair.mp hx' with ⟨c, d, hcd⟩
  have hframe := twoLocalCoordinateFrame_linearIndependent place other hne
  rw [Fintype.linearIndependent_iff] at hframe
  have hrelation :
      ∑ k : Fin 4, ![a, b, c, d] k • twoLocalCoordinateFrame place other k = 0 := by
    calc
      _ = (a • firstOrderLocalValueCoordinates place +
            b • firstOrderLocalJetCoordinates place) +
          (c • firstOrderLocalValueCoordinates other +
            d • firstOrderLocalJetCoordinates other) := by
        simp [Fin.sum_univ_succ, twoLocalCoordinateFrame]
        module
      _ = x + x := by rw [hab, hcd]
      _ = 0 := by
        funext i
        exact CharTwo.add_self_eq_zero _
  have ha : a = 0 := by
    simpa using hframe ![a, b, c, d] hrelation 0
  have hb : b = 0 := by
    simpa using hframe ![a, b, c, d] hrelation 1
  calc
    x = a • firstOrderLocalValueCoordinates place +
        b • firstOrderLocalJetCoordinates place := hab.symm
    _ = 0 := by simp [ha, hb]

/-- Distinct rational local planes cannot have the same first vector after
arbitrary ordered basis changes. -/
theorem distinctRationalJet_basisPair_first_ne
    (place other : Fin 3) (hne : place ≠ other)
    (h k : PlaneBasisChange) :
    (h.basisPair
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right).1 ≠
      (k.basisPair
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right).1 := by
  let x := (h.basisPair (firstOrderLocalValueCoordinates place)
    (firstOrderLocalJetCoordinates place)).1
  let y := (k.basisPair (firstOrderLocalValueCoordinates other)
    (firstOrderLocalJetCoordinates other)).1
  have hxmem : x ∈ Submodule.span F₂
      ({firstOrderLocalValueCoordinates place,
        firstOrderLocalJetCoordinates place} : Set (Fin 8 → F₂)) :=
    (basisPair_components_mem_span h _ _).1
  have hymem : y ∈ Submodule.span F₂
      ({firstOrderLocalValueCoordinates other,
        firstOrderLocalJetCoordinates other} : Set (Fin 8 → F₂)) :=
    (basisPair_components_mem_span k _ _).1
  have hxmap : exactFirstOrderTwoMap x =
      (h.basisPair
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right).1 := by
    calc
      exactFirstOrderTwoMap x =
          (exactFirstOrderTwoMap (h.basisPair
            (firstOrderLocalValueCoordinates place)
            (firstOrderLocalJetCoordinates place)).1,
          exactFirstOrderTwoMap (h.basisPair
            (firstOrderLocalValueCoordinates place)
            (firstOrderLocalJetCoordinates place)).2).1 := rfl
      _ = (h.basisPair
          (exactFirstOrderTwoMap (firstOrderLocalValueCoordinates place))
          (exactFirstOrderTwoMap (firstOrderLocalJetCoordinates place))).1 := by
        rw [exactFirstOrderTwoMap_basisPair]
      _ = _ := by rw [exactFirstOrderTwoMap_localValueCoordinates,
        exactFirstOrderTwoMap_localJetCoordinates]
  have hymap : exactFirstOrderTwoMap y =
      (k.basisPair
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right).1 := by
    calc
      exactFirstOrderTwoMap y =
          (exactFirstOrderTwoMap (k.basisPair
            (firstOrderLocalValueCoordinates other)
            (firstOrderLocalJetCoordinates other)).1,
          exactFirstOrderTwoMap (k.basisPair
            (firstOrderLocalValueCoordinates other)
            (firstOrderLocalJetCoordinates other)).2).1 := rfl
      _ = (k.basisPair
          (exactFirstOrderTwoMap (firstOrderLocalValueCoordinates other))
          (exactFirstOrderTwoMap (firstOrderLocalJetCoordinates other))).1 := by
        rw [exactFirstOrderTwoMap_basisPair]
      _ = _ := by rw [exactFirstOrderTwoMap_localValueCoordinates,
        exactFirstOrderTwoMap_localJetCoordinates]
  have hchanged := h.quadraticPlaneDirections_linearIndependent
    _ _ (rationalJet_quadraticPlaneDirections_linearIndependent place)
  have hfirstNonzero :=
    (quadraticPlaneDirections_independent_nonzero_ne _ _ hchanged).1
  intro heq
  have hxy : x = y := by
    apply exactFirstOrderTwoMap_injective
    rw [hxmap, hymap, heq]
  have hxOther : x ∈ Submodule.span F₂
      ({firstOrderLocalValueCoordinates other,
        firstOrderLocalJetCoordinates other} : Set (Fin 8 → F₂)) := by
    rw [hxy]
    exact hymem
  have hxzero := eq_zero_of_mem_distinct_local_coordinate_spans
    place other hne x hxmem hxOther
  apply hfirstNonzero
  rw [← hxmap, hxzero, exactFirstOrderTwoMap.map_zero]

/-- The middle basis change in a chain through two distinct rational local
planes is one of the four changes used by the direct rewire. -/
theorem twoRotation_middleBasisChange_admissible
    (place other : Fin 3) (hne : place ≠ other)
    (h k e : PlaneBasisChange) (p v t r s z : TwoForm)
    (hplace : h.basisPair
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = (p, t))
    (hother : k.basisPair
      (ExceptionalIndependentPlane.rationalJet other).left
      (ExceptionalIndependentPlane.rationalJet other).right = (r, z))
    (hmiddle : e.basisPair p v = (r, s)) :
    e = .swap ∨ e = .rotateLeft ∨
      e = .cycleRight ∨ e = .cycleLeft := by
  have hfirst := distinctRationalJet_basisPair_first_ne place other hne h k
  cases e
  · exfalso
    apply hfirst
    rw [hplace, hother]
    simpa only [PlaneBasisChange.basisPair] using
      congrArg (fun x : TwoForm × TwoForm => x.1) hmiddle
  · exact Or.inl rfl
  · exfalso
    apply hfirst
    rw [hplace, hother]
    simpa only [PlaneBasisChange.basisPair] using
      congrArg (fun x : TwoForm × TwoForm => x.1) hmiddle
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- Injectivity of the exact envelope map sends an independent ordered
coordinate pair to an independent ambient quadratic plane. -/
theorem exactFirstOrderTwoMap_quadraticPlaneDirections_linearIndependent
    (x y : Fin 8 → F₂) (hxy : LinearIndependent F₂ ![x, y]) :
    LinearIndependent F₂ (quadraticPlaneDirections
      (exactFirstOrderTwoMap x) (exactFirstOrderTwoMap y)) := by
  have hmap := hxy.map' exactFirstOrderTwoMap
    (LinearMap.ker_eq_bot.mpr exactFirstOrderTwoMap_injective)
  have hq : exactFirstOrderTwoMap x ≠ 0 := by
    simpa only [Function.comp_apply, Matrix.cons_val_zero] using hmap.ne_zero 0
  have hc : exactFirstOrderTwoMap y ≠ 0 := by
    simpa only [Function.comp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hmap.ne_zero 1
  have hne : exactFirstOrderTwoMap x ≠ exactFirstOrderTwoMap y := by
    intro h
    have heq : (exactFirstOrderTwoMap ∘ ![x, y]) 0 =
        (exactFirstOrderTwoMap ∘ ![x, y]) 1 := by
      simpa only [Function.comp_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one] using h
    exact Fin.zero_ne_one (hmap.injective heq)
  exact quadraticPlaneDirections_linearIndependent_of_nonzero_ne
    _ _ hq hc hne

theorem isRationalJetPresentation_of_planeCoeff_eq_local
    (q c : TwoForm) (x y : Fin 8 → F₂) (place : Fin 3)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (heq : firstOrderPlaneCoeff x y =
      firstOrderLocalKernelDirections place) :
    IsRationalJetPresentation place q c := by
  have hxy := exactFirstOrderCoordinates_linearIndependent q c x y hx hy hind
  have hzero : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff (firstOrderLocalValueCoordinates place)
        (firstOrderLocalJetCoordinates place) = 0 := by
    rw [heq, firstOrderPlaneCoeff_localCoordinates]
    funext k
    exact CharTwo.add_self_eq_zero _
  have hcoordSpan := firstOrderCoordinate_span_eq_of_planeCoeff_add_eq_zero
    x y (firstOrderLocalValueCoordinates place)
      (firstOrderLocalJetCoordinates place) hxy
      (firstOrderLocalCoordinates_linearIndependent place) hzero
  have hambientSpan := quadraticPlane_span_eq_of_firstOrderCoordinate_span_eq
    q c (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right
    x y (firstOrderLocalValueCoordinates place)
      (firstOrderLocalJetCoordinates place) hx hy
      (exactFirstOrderTwoMap_localValueCoordinates place).symm
      (exactFirstOrderTwoMap_localJetCoordinates place).symm hcoordSpan
  exact isRationalJetPresentation_of_span_eq place q c hind hambientSpan

theorem other_planeCoeff_of_twoLocal_total
    (x y z w : Fin 8 → F₂) (place other : Fin 3)
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections place +
        firstOrderLocalKernelDirections other)
    (hfirst : firstOrderPlaneCoeff x y =
      firstOrderLocalKernelDirections place) :
    firstOrderPlaneCoeff z w = firstOrderLocalKernelDirections other := by
  rw [hfirst] at hdiff
  exact add_left_cancel hdiff

inductive TwoRotationNormalFormData
    (q c q' c' : TwoForm) (place other : Fin 3) : Prop where
  | intro
      (p v t r s d : TwoForm)
      (hPlace hOther kFirst kSecond e : PlaneBasisChange)
      (first_eq : PlaneBasisChange.basisPair kFirst q c = (p, v + t))
      (second_eq : PlaneBasisChange.basisPair kSecond q' c' = (r, s + d))
      (place_eq : PlaneBasisChange.basisPair hPlace
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right = (p, t))
      (other_eq : PlaneBasisChange.basisPair hOther
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right = (r, d))
      (middle_eq : PlaneBasisChange.basisPair e p v = (r, s))
      (admissible : e = .swap ∨ e = .rotateLeft ∨
        e = .cycleRight ∨ e = .cycleLeft) :
      TwoRotationNormalFormData q c q' c' place other

private inductive TwoOneRotationNormalFormData
    (q c q' c' qMid cMid : TwoForm) (place other : Fin 3) : Prop where
  | intro
      (p v t r s d : TwoForm)
      (gMid gMid' hPlace hOther kFirst kSecond : PlaneBasisChange)
      (mid_first_eq : gMid.basisPair qMid cMid = (p, v))
      (mid_second_eq : gMid'.basisPair qMid cMid = (r, s))
      (place_eq : hPlace.basisPair
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right = (p, t))
      (other_eq : hOther.basisPair
        (ExceptionalIndependentPlane.rationalJet other).left
        (ExceptionalIndependentPlane.rationalJet other).right = (r, d))
      (first_eq : kFirst.basisPair q c = (p, v + t))
      (second_eq : kSecond.basisPair q' c' = (r, s + d)) :
      TwoOneRotationNormalFormData q c q' c' qMid cMid place other

private inductive ActualOneRotationNormalFormData
    (q c q' c' : TwoForm) (place : Fin 3) : Prop where
  | intro
      (p v t : TwoForm) (g h k : PlaneBasisChange)
      (first_eq : g.basisPair q c = (p, v))
      (local_eq : h.basisPair
        (ExceptionalIndependentPlane.rationalJet place).left
        (ExceptionalIndependentPlane.rationalJet place).right = (p, t))
      (second_eq : k.basisPair q' c' = (p, v + t)) :
      ActualOneRotationNormalFormData q c q' c' place

private theorem oneLocalKernelDifference_normalFormData
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂) (place : Fin 3)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hxy : LinearIndependent F₂ ![x, y])
    (hzw : LinearIndependent F₂ ![z, w])
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections place) :
    ActualOneRotationNormalFormData q c q' c' place := by
  rcases oneLocalKernelDifference_actualNormalForm
      q c q' c' x y z w place hx hy hz hw hxy hzw hdiff with
    ⟨p, v, t, g, h, k, _hp, hg, hh, hk⟩
  have hh' : h.basisPair
      (ExceptionalIndependentPlane.rationalJet place).left
      (ExceptionalIndependentPlane.rationalJet place).right = (p, t) := by
    simpa only [exactFirstOrderTwoMap_localValueCoordinates,
      exactFirstOrderTwoMap_localJetCoordinates] using hh
  exact .intro p v t g h k hg hh' hk

private theorem twoLocalKernelDifference_twoNormalForms
    (q c q' c' qMid cMid : TwoForm)
    (x y z w rCoord sCoord : Fin 8 → F₂)
    (place other : Fin 3)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hqMid : qMid = exactFirstOrderTwoMap rCoord)
    (hcMid : cMid = exactFirstOrderTwoMap sCoord)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hrsCoord : LinearIndependent F₂ ![rCoord, sCoord])
    (hfirst : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff rCoord sCoord =
        firstOrderLocalKernelDirections place)
    (hsecond : firstOrderPlaneCoeff rCoord sCoord +
      firstOrderPlaneCoeff z w =
        firstOrderLocalKernelDirections other) :
    TwoOneRotationNormalFormData
      q c q' c' qMid cMid place other := by
  have hxy := exactFirstOrderCoordinates_linearIndependent
    q c x y hx hy hind
  have hzw := exactFirstOrderCoordinates_linearIndependent
    q' c' z w hz hw hind'
  have hfirstReversed : firstOrderPlaneCoeff rCoord sCoord +
      firstOrderPlaneCoeff x y = firstOrderLocalKernelDirections place := by
    simpa only [add_comm] using hfirst
  rcases oneLocalKernelDifference_normalFormData
      qMid cMid q c rCoord sCoord x y place
      hqMid hcMid hx hy hrsCoord hxy hfirstReversed with
    ⟨p, v, t, gMid, hPlace, kFirst, hgMid, hhPlace, hkFirst⟩
  rcases oneLocalKernelDifference_normalFormData
      qMid cMid q' c' rCoord sCoord z w other
      hqMid hcMid hz hw hrsCoord hzw hsecond with
    ⟨r, s, d, gMid', hOther, kSecond, hgMid', hhOther, hkSecond⟩
  exact .intro p v t r s d gMid gMid' hPlace hOther kFirst kSecond
    hgMid hgMid' hhPlace hhOther hkFirst hkSecond

theorem twoLocalKernelDifference_chain_normalForms
    (q c q' c' : TwoForm) (x y z w rCoord sCoord : Fin 8 → F₂)
    (place other : Fin 3) (hne : place ≠ other)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hrsCoord : LinearIndependent F₂ ![rCoord, sCoord])
    (hfirst : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff rCoord sCoord =
        firstOrderLocalKernelDirections place)
    (hsecond : firstOrderPlaneCoeff rCoord sCoord +
      firstOrderPlaneCoeff z w =
        firstOrderLocalKernelDirections other) :
    TwoRotationNormalFormData q c q' c' place other := by
  let qMid := exactFirstOrderTwoMap rCoord
  let cMid := exactFirstOrderTwoMap sCoord
  have hmid : LinearIndependent F₂
      (quadraticPlaneDirections qMid cMid) :=
    exactFirstOrderTwoMap_quadraticPlaneDirections_linearIndependent
      rCoord sCoord hrsCoord
  rcases twoLocalKernelDifference_twoNormalForms
      q c q' c' qMid cMid x y z w rCoord sCoord place other
      hx hy hz hw rfl rfl hind hind' hrsCoord hfirst hsecond with
    ⟨p, v, t, r, s, d, gMid, gMid', hPlace, hOther, kFirst, kSecond,
      hgMid, hgMid', hhPlace, hhOther, hkFirst, hkSecond⟩
  have hmidChanged : LinearIndependent F₂
      (quadraticPlaneDirections r s) := by
    have h := gMid'.quadraticPlaneDirections_linearIndependent
      qMid cMid hmid
    rw [hgMid'] at h
    exact h
  have hspanMid' : Submodule.span F₂ ({r, s} : Set TwoForm) =
      Submodule.span F₂ ({qMid, cMid} : Set TwoForm) := by
    have h := gMid'.span_basisPair qMid cMid
    rw [hgMid'] at h
    exact h
  have hspanMid : Submodule.span F₂ ({p, v} : Set TwoForm) =
      Submodule.span F₂ ({qMid, cMid} : Set TwoForm) := by
    have h := gMid.span_basisPair qMid cMid
    rw [hgMid] at h
    exact h
  have hspan : Submodule.span F₂ ({r, s} : Set TwoForm) =
      Submodule.span F₂ ({p, v} : Set TwoForm) :=
    hspanMid'.trans hspanMid.symm
  rcases exists_planeBasisChange_of_span_eq p v r s hmidChanged hspan with
    ⟨e, hr, hs⟩
  have hmiddle : e.basisPair p v = (r, s) := Prod.ext hr.symm hs.symm
  have hadmissible := twoRotation_middleBasisChange_admissible
    place other hne hPlace hOther e p v t r s d hhPlace hhOther hmiddle
  exact .intro p v t r s d hPlace hOther kFirst kSecond e
    hkFirst hkSecond hhPlace hhOther hmiddle hadmissible

private inductive TwoRotationChangedShadowData
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) : Prop where
  | intro (kFirst kSecond : PlaneBasisChange)
      (excluded :
        ∀ (u : TargetCoeff), u ∈ firstOrderEnvelopeCoeffSpace →
          changedLowProductQuadraticShadow kFirst a b ell m q c +
              changedLowProductQuadraticShadow kSecond a' b' ell' m' q' c' ≠
            targetTwo (firstOrderMissingCoeff + u)) :
      TwoRotationChangedShadowData
        a b a' b' ell m ell' m' q c q' c'

private theorem twoRotationNormalFormData_changedShadow
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (place other : Fin 3) (hne : place ≠ other)
    (hdata : TwoRotationNormalFormData q c q' c' place other)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c') :
    TwoRotationChangedShadowData
      a b a' b' ell m ell' m' q c q' c' := by
  rcases hdata with
    ⟨p, v, t, r, s, d, hPlace, hOther, kFirst, kSecond, e,
      hkFirst, hkSecond, hhPlace, hhOther, hmiddle, hadmissible⟩
  let ab := kFirst.basisPair a b
  let lm := kFirst.basisPair ell m
  let ab' := kSecond.basisPair a' b'
  let lm' := kSecond.basisPair ell' m'
  have hchangedHigh :
      changedLowProductHighPart kFirst ell m q c =
        changedLowProductHighPart kSecond ell' m' q' c' := by
    rw [planeBasisChange_high, planeBasisChange_high]
    exact hhigh
  have hnormalizedHigh :
      lowProductHighPart lm.1 lm.2 p (v + t) =
        lowProductHighPart lm'.2 lm'.1 (s + d) r := by
    have hchangedHigh' := hchangedHigh
    simp only [changedLowProductHighPart] at hchangedHigh'
    rw [hkFirst, hkSecond] at hchangedHigh'
    change lowProductHighPart lm.1 lm.2 p (v + t) =
      lowProductHighPart lm'.1 lm'.2 r (s + d) at hchangedHigh'
    exact hchangedHigh'.trans
      (lowProductHighPart_swap lm'.1 lm'.2 r (s + d))
  have hchangedExcluded : ∀ (u : TargetCoeff),
      u ∈ firstOrderEnvelopeCoeffSpace →
        changedLowProductQuadraticShadow kFirst a b ell m q c +
            changedLowProductQuadraticShadow kSecond a' b' ell' m' q' c' ≠
          targetTwo (firstOrderMissingCoeff + u) := by
    intro u hu
    have hnormalizedExcluded :=
      rationalTwoRotation_normalForm_shadow_not_missingCoset
        place other hne hPlace hOther e
        ab.1 ab.2 ab'.2 ab'.1 lm.1 lm.2 lm'.2 lm'.1
        p v t r s d hhPlace hhOther hmiddle hadmissible
        hnormalizedHigh u hu
    simp only [changedLowProductQuadraticShadow]
    rw [hkFirst, hkSecond]
    change
      lowProductQuadraticShadow ab.1 ab.2 lm.1 lm.2 p (v + t) +
          lowProductQuadraticShadow ab'.1 ab'.2 lm'.1 lm'.2 r (s + d) ≠
        targetTwo (firstOrderMissingCoeff + u)
    rw [lowProductQuadraticShadow_swap ab'.1 ab'.2 lm'.1 lm'.2 r (s + d)]
    exact hnormalizedExcluded
  exact .intro kFirst kSecond hchangedExcluded

private theorem twoRotationNormalFormData_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (place other : Fin 3) (hne : place ≠ other)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hdata : TwoRotationNormalFormData q c q' c' place other)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases twoRotationNormalFormData_changedShadow
      a b a' b' ell m ell' m' q c q' c' place other hne
      hdata hhigh with
    ⟨kFirst, kSecond, hchangedExcluded⟩
  apply missingCoset_exclusion_of_add_mem_firstOrderEnvelope
    (lowProductQuadraticShadow a b ell m q c +
      lowProductQuadraticShadow a' b' ell' m' q' c')
    (changedLowProductQuadraticShadow kFirst a b ell m q c +
      changedLowProductQuadraticShadow kSecond a' b' ell' m' q' c')
  · have hcorrection := twoPlaneBasisChanges_shadow_sum_add_original_mem
      firstOrderEnvelopeTwoSpace kFirst kSecond
        a b a' b' ell m ell' m' q c q' c' hq hc hq' hc'
    simpa only [add_comm] using hcorrection
  · exact hchangedExcluded
  · exact hu

private theorem twoLocalKernelDifference_chain_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (x y z w rCoord sCoord : Fin 8 → F₂)
    (place other : Fin 3) (hne : place ≠ other)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hrsCoord : LinearIndependent F₂ ![rCoord, sCoord])
    (hfirst : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff rCoord sCoord =
        firstOrderLocalKernelDirections place)
    (hsecond : firstOrderPlaneCoeff rCoord sCoord +
      firstOrderPlaneCoeff z w =
        firstOrderLocalKernelDirections other)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  have hdata := twoLocalKernelDifference_chain_normalForms
      q c q' c' x y z w rCoord sCoord place other hne
      hx hy hz hw hind hind' hrsCoord hfirst hsecond
  exact twoRotationNormalFormData_shadow_not_missingCoset
    a b a' b' ell m ell' m' q c q' c' place other hne
      hq hc hq' hc' hdata hhigh u hu

/-- Complete weight-two local-difference shadow exclusion.  Both the
collapsed rational-endpoint cases and the independent-midpoint chain are
discharged internally. -/
theorem twoLocalKernelDifference_shadow_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂)
    (place other : Fin 3)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hne : place ≠ other)
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections place +
        firstOrderLocalKernelDirections other)
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c')
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c' ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  rcases twoLocalKernelDifference_chain x y z w place other hne hdiff with
    hplace | hother | ⟨rCoord, sCoord, hrs, hchain⟩
  · have hpresentation := isRationalJetPresentation_of_planeCoeff_eq_local
      q c x y place hx hy hind hplace
    have hsecond := other_planeCoeff_of_twoLocal_total
      x y z w place other hdiff hplace
    have hpresentation' := isRationalJetPresentation_of_planeCoeff_eq_local
      q' c' z w other hz hw hind' hsecond
    exact distinctRationalJetPresentations_shadow_not_missingCoset
      place other hne a b a' b' ell m ell' m' q c q' c'
        hpresentation hpresentation' hhigh u hu
  · have hpresentation := isRationalJetPresentation_of_planeCoeff_eq_local
      q c x y other hx hy hind hother
    have hdiff' : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
        firstOrderLocalKernelDirections other +
          firstOrderLocalKernelDirections place := by
      simpa only [add_comm] using hdiff
    have hsecond := other_planeCoeff_of_twoLocal_total
      x y z w other place hdiff' hother
    have hpresentation' := isRationalJetPresentation_of_planeCoeff_eq_local
      q' c' z w place hz hw hind' hsecond
    exact distinctRationalJetPresentations_shadow_not_missingCoset
      other place hne.symm a b a' b' ell m ell' m' q c q' c'
        hpresentation hpresentation' hhigh u hu
  · rcases hchain with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact twoLocalKernelDifference_chain_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c' x y z w rCoord sCoord
        place other hne hq hc hq' hc' hx hy hz hw hind hind' hrs
        hfirst hsecond hhigh u hu
    · exact twoLocalKernelDifference_chain_shadow_not_missingCoset
        a b a' b' ell m ell' m' q c q' c' x y z w rCoord sCoord
        other place hne.symm hq hc hq' hc' hx hy hz hw hind hind' hrs
        hfirst hsecond hhigh u hu

end

end N5
end UnrestrictedBooleanMul
