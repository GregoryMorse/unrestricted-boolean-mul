import UnrestrictedBooleanMul.N5.FirstOrderAnchorState
import UnrestrictedBooleanMul.N5.LowProductSemantic

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
