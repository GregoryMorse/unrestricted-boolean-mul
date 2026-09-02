import UnrestrictedBooleanMul.N5.EnvelopeAssembly

/-!
# Shadow rewiring for a one-rotation envelope

The one-local-rotation normal form from `EnvelopeAssembly` has quadratic
factor planes `(p,q)` and `(p,q+t)`, where `(p,t)` is the corresponding
rational value--jet plane.  This file records the exact algebraic rewiring

`FG + F'G' = F(G+G') + (F+F')G'`.

On quadratic shadows it converts the original pair into one product on the
local plane `(p,t)` and one product on the dependent plane `(0,q+t)`.  The
same identity holds for the cubic parts.  These are symbolic identities over
`F₂`; they perform no assignment or circuit search.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Basis changes of an arbitrary quadratic plane preserve its high part.
If both quadratic directions lie in `W`, the Boolean quadratic shadow changes
only by an element of `W`.  Unlike the earlier exceptional-plane wrapper,
this form applies directly to planes produced by the Pluecker normal form. -/
theorem planeBasisChange_high_and_shadow_mod_submodule
    (W : Submodule F₂ TwoForm) (g : PlaneBasisChange)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hq : q ∈ W) (hc : c ∈ W) :
    changedLowProductHighPart g ell m q c =
        lowProductHighPart ell m q c ∧
      changedLowProductQuadraticShadow g a b ell m q c +
          lowProductQuadraticShadow a b ell m q c ∈ W := by
  cases g with
  | identity =>
      constructor
      · rfl
      · change lowProductQuadraticShadow a b ell m q c +
            lowProductQuadraticShadow a b ell m q c ∈ W
        have hzero : lowProductQuadraticShadow a b ell m q c +
            lowProductQuadraticShadow a b ell m q c = 0 := by
          funext s
          exact @CharTwo.add_self_eq_zero F₂ _ _
            (lowProductQuadraticShadow a b ell m q c s)
        rw [hzero]
        exact W.zero_mem
  | swap =>
      constructor
      · exact lowProductHighPart_swap m ell c q
      · change lowProductQuadraticShadow b a m ell c q +
            lowProductQuadraticShadow a b ell m q c ∈ W
        rw [lowProductQuadraticShadow_swap b a m ell c q]
        have hzero : lowProductQuadraticShadow a b ell m q c +
            lowProductQuadraticShadow a b ell m q c = 0 := by
          funext s
          exact @CharTwo.add_self_eq_zero F₂ _ _
            (lowProductQuadraticShadow a b ell m q c s)
        rw [hzero]
        exact W.zero_mem
  | rotateRight =>
      exact lowProduct_rotate_right_high_and_shadow_mod_submodule
        W a b ell m q c hq
  | rotateLeft =>
      exact lowProduct_rotate_left_high_and_shadow_mod_submodule
        W a b ell m q c hc
  | cycleRight =>
      exact lowProduct_two_rotations_high_and_shadow_mod_submodule
        W a b ell m q c hc
  | cycleLeft =>
      constructor
      · change lowProductHighPart (ell + m) ell (q + c) q =
          lowProductHighPart ell m q c
        calc
          lowProductHighPart (ell + m) ell (q + c) q =
              lowProductHighPart ell (ell + m) q (q + c) :=
            lowProductHighPart_swap (ell + m) ell (q + c) q
          _ = lowProductHighPart ell m q c :=
            lowProductHighPart_rotate_right ell m q c
      · change lowProductQuadraticShadow (a + b) a (ell + m) ell
              (q + c) q + lowProductQuadraticShadow a b ell m q c ∈ W
        rw [lowProductQuadraticShadow_swap (a + b) a (ell + m) ell
          (q + c) q]
        exact rotate_right_shadow_mod_submodule W a b ell m q c hq

/-- High-part invariance does not require a submodule hypothesis. -/
theorem planeBasisChange_high
    (g : PlaneBasisChange) (ell m : LinearForm) (q c : TwoForm) :
    changedLowProductHighPart g ell m q c =
      lowProductHighPart ell m q c :=
  (planeBasisChange_high_and_shadow_mod_submodule
    ⊤ g 0 0 ell m q c Submodule.mem_top Submodule.mem_top).1

/-- Applying independent basis changes to two products changes their total
quadratic shadow only by an element of the chosen old space. -/
theorem twoPlaneBasisChanges_shadow_sum_add_original_mem
    (W : Submodule F₂ TwoForm) (g k : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' : TwoForm)
    (hq : q ∈ W) (hc : c ∈ W) (hq' : q' ∈ W) (hc' : c' ∈ W) :
    (changedLowProductQuadraticShadow g a b ell m q c +
        changedLowProductQuadraticShadow k a' b' ell' m' q' c') +
      (lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q' c') ∈ W := by
  have hg := (planeBasisChange_high_and_shadow_mod_submodule
    W g a b ell m q c hq hc).2
  have hk := (planeBasisChange_high_and_shadow_mod_submodule
    W k a' b' ell' m' q' c' hq' hc').2
  have hreassoc :
      (changedLowProductQuadraticShadow g a b ell m q c +
          changedLowProductQuadraticShadow k a' b' ell' m' q' c') +
        (lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q' c') =
      (changedLowProductQuadraticShadow g a b ell m q c +
          lowProductQuadraticShadow a b ell m q c) +
        (changedLowProductQuadraticShadow k a' b' ell' m' q' c' +
          lowProductQuadraticShadow a' b' ell' m' q' c') := by
    module
  rw [hreassoc]
  exact W.add_mem hg hk

/-- The exact envelope realization commutes with every ordered-plane basis
change. -/
theorem exactFirstOrderTwoMap_basisPair
    (g : PlaneBasisChange) (x y : Fin 8 → F₂) :
    g.basisPair (exactFirstOrderTwoMap x) (exactFirstOrderTwoMap y) =
      (exactFirstOrderTwoMap (g.basisPair x y).1,
        exactFirstOrderTwoMap (g.basisPair x y).2) := by
  cases g <;> simp [PlaneBasisChange.basisPair, map_add]

/-- Ambient two-form version of the one-local-rotation normal form.  Thus the
coefficient-space result used by the Pluecker classifier is immediately
available to the low-product shadow identities below. -/
theorem oneLocalKernelDifference_actualNormalForm
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂) (i : Fin 3)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hxy : LinearIndependent F₂ ![x, y])
    (hzw : LinearIndependent F₂ ![z, w])
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections i) :
    ∃ (p q₀ t : TwoForm) (g h k : PlaneBasisChange),
      p ≠ 0 ∧
      g.basisPair q c = (p, q₀) ∧
      h.basisPair
          (exactFirstOrderTwoMap (firstOrderLocalValueCoordinates i))
          (exactFirstOrderTwoMap (firstOrderLocalJetCoordinates i)) =
        (p, t) ∧
      k.basisPair q' c' = (p, q₀ + t) := by
  rcases oneLocalKernelDifference_normalForm
      x y z w i hxy hzw hdiff with
    ⟨p₀, q₀, t₀, g, h, k, hp₀, hg, hh, hk⟩
  let p := exactFirstOrderTwoMap p₀
  let q₁ := exactFirstOrderTwoMap q₀
  let t := exactFirstOrderTwoMap t₀
  have hp : p ≠ 0 := by
    intro hpzero
    apply hp₀
    change exactFirstOrderTwoMap p₀ = 0 at hpzero
    apply exactFirstOrderTwoMap_injective
    exact hpzero.trans exactFirstOrderTwoMap.map_zero.symm
  refine ⟨p, q₁, t, g, h, k, hp, ?_, ?_, ?_⟩
  · calc
      g.basisPair q c =
          g.basisPair (exactFirstOrderTwoMap x)
            (exactFirstOrderTwoMap y) := by rw [← hx, ← hy]
      _ = (exactFirstOrderTwoMap (g.basisPair x y).1,
            exactFirstOrderTwoMap (g.basisPair x y).2) :=
        exactFirstOrderTwoMap_basisPair g x y
      _ = (p, q₁) := by rw [hg]
  · calc
      h.basisPair
          (exactFirstOrderTwoMap (firstOrderLocalValueCoordinates i))
          (exactFirstOrderTwoMap (firstOrderLocalJetCoordinates i)) =
        (exactFirstOrderTwoMap
            (h.basisPair (firstOrderLocalValueCoordinates i)
              (firstOrderLocalJetCoordinates i)).1,
          exactFirstOrderTwoMap
            (h.basisPair (firstOrderLocalValueCoordinates i)
              (firstOrderLocalJetCoordinates i)).2) :=
        exactFirstOrderTwoMap_basisPair h
          (firstOrderLocalValueCoordinates i)
          (firstOrderLocalJetCoordinates i)
      _ = (p, t) := by rw [hh]
  · calc
      k.basisPair q' c' =
          k.basisPair (exactFirstOrderTwoMap z)
            (exactFirstOrderTwoMap w) := by rw [← hz, ← hw]
      _ = (exactFirstOrderTwoMap (k.basisPair z w).1,
            exactFirstOrderTwoMap (k.basisPair z w).2) :=
        exactFirstOrderTwoMap_basisPair k z w
      _ = (p, exactFirstOrderTwoMap (q₀ + t₀)) := by rw [hk]
      _ = (p, q₁ + t) := by simp [q₁, t, map_add]

/-- Exact quadratic-shadow rewiring in the one-local-rotation normal form.
The right-hand products have quadratic planes `(p,t)` and `(0,q+t)`. -/
theorem lowProductQuadraticShadow_oneRotation_rewire
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (p q t : TwoForm) :
    lowProductQuadraticShadow a b ell m p q +
        lowProductQuadraticShadow a' b' ell' m' p (q + t) =
      lowProductQuadraticShadow a (b + b') ell (m + m') p t +
        lowProductQuadraticShadow (a + a') b' (ell + ell') m' 0 (q + t) := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [Pi.add_apply, lowProductQuadraticShadow_pair]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- The cubic part obeys the same one-local-rotation rewiring identity. -/
theorem factorPlaneCubic_oneRotation_rewire
    (ell m ell' m' : LinearForm) (p q t : TwoForm) :
    factorPlaneCubic ell m p q +
        factorPlaneCubic ell' m' p (q + t) =
      factorPlaneCubic ell (m + m') p t +
        factorPlaneCubic (ell + ell') m' 0 (q + t) := by
  funext i j k
  simp only [factorPlaneCubic, ambientVectorWedgeTwo,
    N4.vectorWedgeTwoN, ambientTwoCoeff_add, ambientTwoCoeff_zero,
    Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- If the original two products have equal cubic parts, rewiring identifies
the cubic part on the rational local plane with that on the dependent plane.
This is the cubic constraint consumed by the remaining shadow-localization
argument. -/
theorem factorPlaneCubic_local_eq_dependent_of_oneRotation
    (ell m ell' m' : LinearForm) (p q t : TwoForm)
    (hcubic : factorPlaneCubic ell m p q =
      factorPlaneCubic ell' m' p (q + t)) :
    factorPlaneCubic ell (m + m') p t =
      factorPlaneCubic (ell + ell') m' 0 (q + t) := by
  have hrewire := factorPlaneCubic_oneRotation_rewire
    ell m ell' m' p q t
  rw [hcubic] at hrewire
  have hzero :
      factorPlaneCubic ell (m + m') p t +
        factorPlaneCubic (ell + ell') m' 0 (q + t) = 0 := by
    rw [← hrewire]
    funext i j k
    exact @CharTwo.add_self_eq_zero F₂ _ _
      (factorPlaneCubic ell' m' p (q + t) i j k)
  funext i j k
  exact CharTwo.add_eq_zero.mp
    (congrFun (congrFun (congrFun hzero i) j) k)

/-- Rewiring after the two factor planes have been put into the ambient
one-rotation normal form. -/
theorem changedLowProductQuadraticShadow_oneRotation_rewire
    (g k : PlaneBasisChange)
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c q' c' p q₀ t : TwoForm)
    (hg : g.basisPair q c = (p, q₀))
    (hk : k.basisPair q' c' = (p, q₀ + t)) :
    changedLowProductQuadraticShadow g a b ell m q c +
        changedLowProductQuadraticShadow k a' b' ell' m' q' c' =
      lowProductQuadraticShadow
          (g.basisPair a b).1
          ((g.basisPair a b).2 + (k.basisPair a' b').2)
          (g.basisPair ell m).1
          ((g.basisPair ell m).2 + (k.basisPair ell' m').2) p t +
        lowProductQuadraticShadow
          ((g.basisPair a b).1 + (k.basisPair a' b').1)
          (k.basisPair a' b').2
          ((g.basisPair ell m).1 + (k.basisPair ell' m').1)
          (k.basisPair ell' m').2 0 (q₀ + t) := by
  simp only [changedLowProductQuadraticShadow]
  rw [hg, hk]
  exact lowProductQuadraticShadow_oneRotation_rewire
    (g.basisPair a b).1 (g.basisPair a b).2
    (k.basisPair a' b').1 (k.basisPair a' b').2
    (g.basisPair ell m).1 (g.basisPair ell m).2
    (k.basisPair ell' m').1 (k.basisPair ell' m').2 p q₀ t

/-- Equality of the original high parts supplies precisely the local versus
dependent cubic equation after normalization and rewiring. -/
theorem oneRotation_local_eq_dependent_cubic_of_high_eq
    (g k : PlaneBasisChange) (ell m ell' m' : LinearForm)
    (q c q' c' p q₀ t : TwoForm)
    (hg : g.basisPair q c = (p, q₀))
    (hk : k.basisPair q' c' = (p, q₀ + t))
    (hhigh : lowProductHighPart ell m q c =
      lowProductHighPart ell' m' q' c') :
    factorPlaneCubic
        (g.basisPair ell m).1
        ((g.basisPair ell m).2 + (k.basisPair ell' m').2) p t =
      factorPlaneCubic
        ((g.basisPair ell m).1 + (k.basisPair ell' m').1)
        (k.basisPair ell' m').2 0 (q₀ + t) := by
  have hchanged :
      changedLowProductHighPart g ell m q c =
        changedLowProductHighPart k ell' m' q' c' := by
    rw [planeBasisChange_high, planeBasisChange_high]
    exact hhigh
  have hcubic := congrArg Prod.snd hchanged
  simp only [changedLowProductHighPart] at hcubic
  rw [hg, hk] at hcubic
  exact factorPlaneCubic_local_eq_dependent_of_oneRotation
    (g.basisPair ell m).1 (g.basisPair ell m).2
    (k.basisPair ell' m').1 (k.basisPair ell' m').2 p q₀ t hcubic

end

end N5
end UnrestrictedBooleanMul
