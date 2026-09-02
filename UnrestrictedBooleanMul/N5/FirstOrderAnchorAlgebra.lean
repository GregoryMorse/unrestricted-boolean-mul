import UnrestrictedBooleanMul.N5.FirstOrderAnchorState
import UnrestrictedBooleanMul.N5.LowProductSemantic
import UnrestrictedBooleanMul.N5.EnvelopeRotationShadow

/-!
# Algebra of a decomposable first-order anchor

Members of the canonical quadratic base are first-order-envelope forms plus
one scalar multiple of the anchor.  This module records that decomposition
and the exact Boolean effect of the anchor coefficient on a low product.
The formulas use the literal quotient modulo quadratic ANFs, so repeated
anchor factors are removed by Boolean idempotence rather than by an exterior
approximation.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Every member of `U + <d>` is an envelope form plus one scalar multiple
of `d`. -/
theorem exists_firstOrderEnvelope_add_smul_anchor
    (d p : TwoForm) (hp : p ∈ firstOrderAnchorTwoSpace d) :
    ∃ u ∈ firstOrderEnvelopeTwoSpace, ∃ a : F₂, p = u + a • d := by
  rcases Submodule.mem_sup.mp hp with ⟨u, hu, z, hz, rfl⟩
  rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
  exact ⟨u, hu, a, rfl⟩

/-- ANF-level form of the anchored decomposition. -/
theorem exists_firstOrderEnvelopeANF_add_anchor
    (d : TwoForm) (p : ANF 10) (hp : p ∈ firstOrderAnchorState d) :
    ∃ u ∈ firstOrderEnvelopeState, ∃ a : F₂,
      p = u + a • quadraticANFOfForm d := by
  have hpData := (E2.mem_quadraticEnvelopeState_iff
    (firstOrderAnchorTwoSpace d) p).1 hp
  rcases exists_quadraticCoordinates hpData.1 with ⟨c, ell, q, hpq⟩
  have hqAnchor : q ∈ firstOrderAnchorTwoSpace d := by
    have := hpData.2
    rwa [hpq, quadraticProjection_quadraticCoordinateANF] at this
  rcases exists_firstOrderEnvelope_add_smul_anchor d q hqAnchor with
    ⟨q₀, hq₀, a, hq⟩
  let u := quadraticCoordinateANF c ell q₀
  have hu : u ∈ firstOrderEnvelopeState :=
    (E2.mem_quadraticEnvelopeState_iff
      firstOrderEnvelopeTwoSpace u).2
      ⟨quadraticCoordinateANF_mem_quadraticANFSpace c ell q₀,
        by simp [u, hq₀]⟩
  refine ⟨u, hu, a, ?_⟩
  rw [hpq, hq]
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simp [u]
  · simpa [u, quadraticCoordinateANF] using
      (quadraticCoordinateANF_add c 0 ell 0 q₀ d).symm

/-- Equation (11.7) in the exact affine-coset form needed by anchored
low-product comparisons. -/
theorem missingCoset_targetTwo_not_mem_firstOrderAnchor
    (d : TwoForm) (hddec : IsDecomposableTwo d)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    targetTwo (firstOrderMissingCoeff + u) ∉
      firstOrderAnchorTwoSpace d := by
  intro hmem
  have htarget : targetTwo (firstOrderMissingCoeff + u) ∈
      targetTwoSpace := ⟨firstOrderMissingCoeff + u, rfl⟩
  have hintersection : targetTwo (firstOrderMissingCoeff + u) ∈
      targetTwoSpace ⊓ firstOrderAnchorTwoSpace d := ⟨htarget, hmem⟩
  rw [targetTwoSpace_inf_firstOrderAnchorTwoSpace d hddec] at hintersection
  rcases hintersection with ⟨c, hc, hceq⟩
  have hcoeff : c = firstOrderMissingCoeff + u := by
    apply targetTwoLinear_injective
    exact hceq
  have hmissing : firstOrderMissingCoeff ∈
      firstOrderEnvelopeCoeffSpace := by
    have hsum := firstOrderEnvelopeCoeffSpace.add_mem (hcoeff ▸ hc) hu
    have hcancel : (firstOrderMissingCoeff + u) + u =
        firstOrderMissingCoeff := by
      funext i
      simp only [Pi.add_apply]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rwa [hcancel] at hsum
  exact firstOrderMissingCoeff_not_mem hmissing

/-- If the complete lower data of one low product is obtained from the
other by an ordered basis change of the same anchored plane, their shadow
difference lies in the anchored space.  Equation (11.7) therefore excludes
the missing target class. -/
theorem anchored_basisChange_shadow_not_missingCoset
    (d : TwoForm) (hddec : IsDecomposableTwo d)
    (g : PlaneBasisChange)
    (a b : F₂) (ell m : LinearForm) (q c : TwoForm)
    (hq : q ∈ firstOrderAnchorTwoSpace d)
    (hc : c ∈ firstOrderAnchorTwoSpace d)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    changedLowProductQuadraticShadow g a b ell m q c +
        lowProductQuadraticShadow a b ell m q c ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro heq
  apply missingCoset_targetTwo_not_mem_firstOrderAnchor d hddec u hu
  rw [← heq]
  exact (planeBasisChange_high_and_shadow_mod_submodule
    (firstOrderAnchorTwoSpace d) g a b ell m q c hq hc).2

/-- Boolean idempotence makes the product difference under any ordered
basis change an old factor (or zero). -/
theorem PlaneBasisChange.product_add_product_mem
    (g : PlaneBasisChange) (V : Submodule F₂ (ANF 10))
    (X Y : ANF 10) (hX : X ∈ V) (hY : Y ∈ V) :
    (g.basisPair X Y).1 * (g.basisPair X Y).2 + X * Y ∈ V := by
  cases g with
  | identity =>
      change X * Y + X * Y ∈ V
      rw [anf_add_self]
      exact V.zero_mem
  | swap =>
      change Y * X + X * Y ∈ V
      rw [mul_comm Y X, anf_add_self]
      exact V.zero_mem
  | rotateRight =>
      have heq : X * (X + Y) + X * Y = X := by
        rw [mul_add, N4.anf_mul_self, add_assoc, anf_add_self, add_zero]
      change X * (X + Y) + X * Y ∈ V
      rw [heq]
      exact hX
  | rotateLeft =>
      have heq : (X + Y) * Y + X * Y = Y := by
        rw [add_mul, N4.anf_mul_self]
        calc
          (X * Y + Y) + X * Y = Y + (X * Y + X * Y) := by ac_rfl
          _ = Y := by rw [anf_add_self, add_zero]
      change (X + Y) * Y + X * Y ∈ V
      rw [heq]
      exact hY
  | cycleRight =>
      have heq : Y * (X + Y) + X * Y = Y := by
        rw [mul_add, N4.anf_mul_self, mul_comm Y X]
        calc
          (X * Y + Y) + X * Y = Y + (X * Y + X * Y) := by ac_rfl
          _ = Y := by rw [anf_add_self, add_zero]
      change Y * (X + Y) + X * Y ∈ V
      rw [heq]
      exact hY
  | cycleLeft =>
      have heq : (X + Y) * X + X * Y = X := by
        rw [add_mul, N4.anf_mul_self, mul_comm Y X]
        rw [add_assoc, anf_add_self, add_zero]
      change (X + Y) * X + X * Y ∈ V
      rw [heq]
      exact hX

/-- Circuit-facing anchored basis-change exclusion.  This includes affine
and linear lower parts automatically because it is an identity of Boolean
ANFs, not only of homogeneous shadows. -/
theorem firstOrderAnchor_basisChange_products_ne_missingTargetANF
    (d : TwoForm) (hddec : IsDecomposableTwo d)
    (g : PlaneBasisChange) (X Y : ANF 10)
    (hX : X ∈ firstOrderAnchorState d)
    (hY : Y ∈ firstOrderAnchorState d)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    (g.basisPair X Y).1 * (g.basisPair X Y).2 + X * Y ≠
      targetANF (firstOrderMissingCoeff + u) := by
  intro heq
  have hstate : targetANF (firstOrderMissingCoeff + u) ∈
      firstOrderAnchorState d := by
    rw [← heq]
    exact g.product_add_product_mem
      (firstOrderAnchorState d) X Y hX hY
  have htarget : targetANF (firstOrderMissingCoeff + u) ∈
      N4.targetAmbient 10 (mulTarget 5) :=
    Submodule.mem_sup_right (targetANF_mem_mulTarget
      (firstOrderMissingCoeff + u))
  have henvelope :=
    firstOrderAnchorState_inf_targetAmbient_le_firstOrderEnvelopeState
      d hddec ⟨hstate, htarget⟩
  have hprojection : targetTwo (firstOrderMissingCoeff + u) ∈
      firstOrderEnvelopeTwoSpace := by
    have hdata := (E2.mem_quadraticEnvelopeState_iff
      firstOrderEnvelopeTwoSpace
      (targetANF (firstOrderMissingCoeff + u))).1 henvelope
    simpa only [quadraticProjection_targetANF] using hdata.2
  exact missingCoset_targetTwo_not_mem_firstOrderAnchor
    d hddec u hu (Submodule.mem_sup_left hprojection)

/-- Every ordered pair in `U + <d>` can be normalized so that either the
anchor is absent or it occurs only in the first direction. -/
theorem exists_firstOrderAnchor_plane_normalForm
    (d q c : TwoForm)
    (hq : q ∈ firstOrderAnchorTwoSpace d)
    (hc : c ∈ firstOrderAnchorTwoSpace d) :
    ∃ (g : PlaneBasisChange) (u v : TwoForm),
      u ∈ firstOrderEnvelopeTwoSpace ∧
      v ∈ firstOrderEnvelopeTwoSpace ∧
      (g.basisPair q c = (u, v) ∨
        g.basisPair q c = (u + d, v)) := by
  rcases exists_firstOrderEnvelope_add_smul_anchor d q hq with
    ⟨u, hu, alpha, hqeq⟩
  rcases exists_firstOrderEnvelope_add_smul_anchor d c hc with
    ⟨v, hv, beta, hceq⟩
  rcases f2_eq_zero_or_one alpha with rfl | rfl <;>
    rcases f2_eq_zero_or_one beta with rfl | rfl
  · refine ⟨.identity, u, v, hu, hv, Or.inl ?_⟩
    simpa [PlaneBasisChange.basisPair] using congrArg₂ (fun x y => (x, y)) hqeq hceq
  · refine ⟨.swap, v, u, hv, hu, Or.inr ?_⟩
    simp only [zero_smul, add_zero, one_smul] at hqeq hceq
    simp [PlaneBasisChange.basisPair, hqeq, hceq]
  · refine ⟨.identity, u, v, hu, hv, Or.inr ?_⟩
    simp only [zero_smul, add_zero, one_smul] at hqeq hceq
    simp [PlaneBasisChange.basisPair, hqeq, hceq]
  · refine ⟨.rotateRight, u, u + v, hu,
      firstOrderEnvelopeTwoSpace.add_mem hu hv, Or.inr ?_⟩
    simp only [one_smul] at hqeq hceq
    simp only [PlaneBasisChange.basisPair, hqeq, hceq, Prod.mk.injEq,
      true_and]
    funext s
    simp only [Pi.add_apply]
    calc
      (u s + d s) + (v s + d s) =
          (d s + d s) + (u s + v s) := by ac_rfl
      _ = u s + v s := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- Quadratic projection commutes with each of the six ordered basis
changes. -/
theorem quadraticProjection_basisPair
    (g : PlaneBasisChange) (X Y : ANF 10) :
    (quadraticProjection 10 (g.basisPair X Y).1,
        quadraticProjection 10 (g.basisPair X Y).2) =
      g.basisPair (quadraticProjection 10 X) (quadraticProjection 10 Y) := by
  cases g <;> simp [PlaneBasisChange.basisPair, map_add]

/-- Ordered basis changes preserve membership in an ANF wire state. -/
theorem PlaneBasisChange.basisPair_mem_anfSubmodule
    (g : PlaneBasisChange) (V : Submodule F₂ (ANF 10))
    (X Y : ANF 10) (hX : X ∈ V) (hY : Y ∈ V) :
    (g.basisPair X Y).1 ∈ V ∧ (g.basisPair X Y).2 ∈ V := by
  cases g with
  | identity => exact ⟨hX, hY⟩
  | swap => exact ⟨hY, hX⟩
  | rotateRight => exact ⟨hX, V.add_mem hX hY⟩
  | rotateLeft => exact ⟨V.add_mem hX hY, hY⟩
  | cycleRight => exact ⟨hY, V.add_mem hX hY⟩
  | cycleLeft => exact ⟨V.add_mem hX hY, hX⟩

/-- Circuit-facing normal form for a pair of anchored quadratic wires.  The
same basis change keeps both factors old and changes their product by an old
wire, while their quadratic directions become either `(u,v)` or
`(u+d,v)` with `u,v ∈ U`. -/
theorem exists_firstOrderAnchor_wirePair_normalForm
    (d : TwoForm) (X Y : ANF 10)
    (hX : X ∈ firstOrderAnchorState d)
    (hY : Y ∈ firstOrderAnchorState d) :
    ∃ (g : PlaneBasisChange) (u v : TwoForm),
      u ∈ firstOrderEnvelopeTwoSpace ∧
      v ∈ firstOrderEnvelopeTwoSpace ∧
      (g.basisPair X Y).1 ∈ firstOrderAnchorState d ∧
      (g.basisPair X Y).2 ∈ firstOrderAnchorState d ∧
      ((g.basisPair X Y).1 * (g.basisPair X Y).2 + X * Y) ∈
        firstOrderAnchorState d ∧
      ((quadraticProjection 10 (g.basisPair X Y).1 = u ∧
          quadraticProjection 10 (g.basisPair X Y).2 = v) ∨
        (quadraticProjection 10 (g.basisPair X Y).1 = u + d ∧
          quadraticProjection 10 (g.basisPair X Y).2 = v)) := by
  have hXdata := (E2.mem_quadraticEnvelopeState_iff
    (firstOrderAnchorTwoSpace d) X).1 hX
  have hYdata := (E2.mem_quadraticEnvelopeState_iff
    (firstOrderAnchorTwoSpace d) Y).1 hY
  rcases exists_firstOrderAnchor_plane_normalForm d
      (quadraticProjection 10 X) (quadraticProjection 10 Y)
      hXdata.2 hYdata.2 with ⟨g, u, v, hu, hv, hnormal⟩
  have hmem := g.basisPair_mem_anfSubmodule
    (firstOrderAnchorState d) X Y hX hY
  have hprojection := quadraticProjection_basisPair g X Y
  refine ⟨g, u, v, hu, hv, hmem.1, hmem.2,
    g.product_add_product_mem (firstOrderAnchorState d) X Y hX hY, ?_⟩
  rcases hnormal with hnormal | hnormal
  · left
    have hpair := hprojection.trans hnormal
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  · right
    have hpair := hprojection.trans hnormal
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- Compact predicate for the two normalized anchored plane types. -/
def IsFirstOrderAnchorWirePairNormalForm
    (d : TwoForm) (X Y : ANF 10) : Prop :=
  ∃ u ∈ firstOrderEnvelopeTwoSpace,
    ∃ v ∈ firstOrderEnvelopeTwoSpace,
      ((quadraticProjection 10 X = u ∧ quadraticProjection 10 Y = v) ∨
        (quadraticProjection 10 X = u + d ∧
          quadraticProjection 10 Y = v))

/-- Every anchored quadratic wire pair admits the compact normal form by an
old-wire-preserving basis change. -/
theorem exists_basisChange_isFirstOrderAnchorWirePairNormalForm
    (d : TwoForm) (X Y : ANF 10)
    (hX : X ∈ firstOrderAnchorState d)
    (hY : Y ∈ firstOrderAnchorState d) :
    ∃ g : PlaneBasisChange,
      (g.basisPair X Y).1 ∈ firstOrderAnchorState d ∧
      (g.basisPair X Y).2 ∈ firstOrderAnchorState d ∧
      ((g.basisPair X Y).1 * (g.basisPair X Y).2 + X * Y) ∈
        firstOrderAnchorState d ∧
      IsFirstOrderAnchorWirePairNormalForm d
        (g.basisPair X Y).1 (g.basisPair X Y).2 := by
  rcases exists_firstOrderAnchor_wirePair_normalForm d X Y hX hY with
    ⟨g, u, v, hu, hv, hXg, hYg, hproduct, hnormal⟩
  refine ⟨g, hXg, hYg, hproduct, u, hu, v, hv, hnormal⟩

/-- Literal high classes are additive in the complete linear/quadratic data
of the right factor. -/
theorem lowProductHighClass_add_right
    (ell m n : LinearForm) (q c d : TwoForm) :
    lowProductHighClass ell (m + n) q (c + d) =
      lowProductHighClass ell m q c +
        lowProductHighClass ell n q d := by
  have hsum := quadraticCoordinateANF_add 0 0 m n c d
  simp only [zero_add] at hsum
  rw [lowProductHighClass, lowProductHighClass, lowProductHighClass,
    ← hsum, mul_add, map_add]

/-- Literal high classes are additive in the complete linear/quadratic data
of the left factor. -/
theorem lowProductHighClass_add_left
    (ell n m : LinearForm) (q d c : TwoForm) :
    lowProductHighClass (ell + n) m (q + d) c =
      lowProductHighClass ell m q c +
        lowProductHighClass n m d c := by
  have hsum := quadraticCoordinateANF_add 0 0 ell n q d
  simp only [zero_add] at hsum
  rw [lowProductHighClass, lowProductHighClass, lowProductHighClass,
    ← hsum, add_mul, map_add]

@[simp] theorem lowProductHighClass_zero_linear_self (d : TwoForm) :
    lowProductHighClass 0 0 d d = 0 := by
  rw [lowProductHighClass, N4.anf_mul_self]
  exact highProjectionTen_eq_zero_of_quadratic
    (quadraticCoordinateANF_mem_quadraticANFSpace 0 0 d)

/-- The correction in the literal high quotient caused by adjoining scalar
anchor coefficients to the two quadratic factors. -/
theorem lowProductHighClass_add_smul_anchor
    (ell m : LinearForm) (q c d : TwoForm) (alpha beta : F₂) :
    lowProductHighClass ell m (q + alpha • d) (c + beta • d) =
      lowProductHighClass ell m q c +
        beta • lowProductHighClass ell 0 q d +
        alpha • lowProductHighClass 0 m d c := by
  rcases f2_eq_zero_or_one alpha with rfl | rfl <;>
    rcases f2_eq_zero_or_one beta with rfl | rfl
  · simp
  · simpa only [zero_smul, one_smul, add_zero] using
      lowProductHighClass_add_right ell m 0 q c d
  · simpa only [zero_smul, one_smul, add_zero] using
      lowProductHighClass_add_left ell 0 m q d c
  · simp only [one_smul]
    have hleft₁ : lowProductHighClass ell m (q + d) c =
        lowProductHighClass ell m q c +
          lowProductHighClass 0 m d c := by
      simpa only [add_zero] using
        lowProductHighClass_add_left ell 0 m q d c
    have hleft₂ : lowProductHighClass ell 0 (q + d) d =
        lowProductHighClass ell 0 q d +
          lowProductHighClass 0 0 d d := by
      simpa only [add_zero] using
        lowProductHighClass_add_left ell 0 0 q d d
    calc
      lowProductHighClass ell m (q + d) (c + d) =
          lowProductHighClass ell m (q + d) c +
            lowProductHighClass ell 0 (q + d) d := by
        simpa only [add_zero] using
          lowProductHighClass_add_right ell m 0 (q + d) c d
      _ = (lowProductHighClass ell m q c +
            lowProductHighClass 0 m d c) +
          (lowProductHighClass ell 0 q d +
            lowProductHighClass 0 0 d d) := by
        rw [hleft₁, hleft₂]
      _ = lowProductHighClass ell m q c +
          lowProductHighClass ell 0 q d +
          lowProductHighClass 0 m d c := by
        rw [lowProductHighClass_zero_linear_self, add_zero]
        abel

/-- Exact quadratic-shadow correction for scalar anchor coefficients. -/
theorem lowProductQuadraticShadow_add_smul_anchor
    (a b : F₂) (ell m : LinearForm) (q c d : TwoForm)
    (alpha beta : F₂) :
    lowProductQuadraticShadow a b ell m
        (q + alpha • d) (c + beta • d) =
      lowProductQuadraticShadow a b ell m q c +
        (a * beta + b * alpha + alpha * beta) • d +
        beta • ambientBooleanContraction ell d +
        alpha • ambientBooleanContraction m d +
        beta • ambientTwoHadamard q d +
        alpha • ambientTwoHadamard d c := by
  funext s
  simp only [lowProductQuadraticShadow, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ambientBooleanContraction, ambientTwoHadamard]
  ring_nf
  simp only [N3Certificate.pow_two_f2]
  ring

end
end N5
end UnrestrictedBooleanMul
