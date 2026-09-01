import UnrestrictedBooleanMul.N5.IndependentShadow

/-!
# First-order envelope shadow bridge

This module isolates the decomposable-defect step in manuscript Lemma 11.2.
Once a quadratic shadow comparison has been localized to the target-clean
second-jet module, adjoining one decomposable defect direction still cannot
create the missing target class.  The proof is the submodule intersection
identity (11.7), not a finite circuit or coordinate-state enumeration.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Target-valued members of the target-clean second jet with one adjoined
decomposable direction already belong to the first-order envelope. -/
theorem targetClean_sup_decomposable_target_mem_firstOrder
    (D defect : TwoForm) (hdefect : IsDecomposableTwo defect)
    (hDtarget : D ∈ targetTwoSpace)
    (hDclean : D ∈ targetCleanSecondJetSpace ⊔
      Submodule.span F₂ ({defect} : Set TwoForm)) :
    D ∈ firstOrderEnvelopeTwoSpace := by
  have hD : D ∈ targetTwoSpace ⊓
      (targetCleanSecondJetSpace ⊔
        Submodule.span F₂ ({defect} : Set TwoForm)) :=
    ⟨hDtarget, hDclean⟩
  rw [targetTwoSpace_inf_targetClean_sup_decomposable
    defect hdefect] at hD
  exact hD

/-- Decomposable-defect bridge for an actual low-product shadow comparison.
The preceding local shadow calculations supply `hclean`; this theorem turns
target-valuedness into membership in the old first-order envelope. -/
theorem envelope_shadow_of_targetClean
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c defect : TwoForm) (hdefect : IsDecomposableTwo defect)
    (htarget :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q c ∈ targetTwoSpace)
    (hclean :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q c ∈
        targetCleanSecondJetSpace ⊔
          Submodule.span F₂ ({defect} : Set TwoForm)) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q c ∈
      firstOrderEnvelopeTwoSpace :=
  targetClean_sup_decomposable_target_mem_firstOrder
    _ defect hdefect htarget hclean

/-- A target-clean low-product comparison with one decomposable defect cannot
represent the affine missing target coset. -/
theorem envelope_shadow_of_targetClean_not_missingCoset
    (a b a' b' : F₂) (ell m ell' m' : LinearForm)
    (q c defect : TwoForm) (hdefect : IsDecomposableTwo defect)
    (hclean :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q c ∈
        targetCleanSecondJetSpace ⊔
          Submodule.span F₂ ({defect} : Set TwoForm))
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    lowProductQuadraticShadow a b ell m q c +
        lowProductQuadraticShadow a' b' ell' m' q c ≠
      targetTwo (firstOrderMissingCoeff + u) := by
  intro hmissing
  have htarget :
      lowProductQuadraticShadow a b ell m q c +
          lowProductQuadraticShadow a' b' ell' m' q c ∈
        targetTwoSpace := by
    rw [hmissing]
    exact ⟨firstOrderMissingCoeff + u, rfl⟩
  have hfirst := envelope_shadow_of_targetClean
    a b a' b' ell m ell' m' q c defect hdefect htarget hclean
  apply firstOrderEnvelope_add_two_decomposable_ne_missingCoset
    _ hfirst 0 0 0 0 u hu
  simpa using hmissing

end

end N5
end UnrestrictedBooleanMul
