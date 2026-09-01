import UnrestrictedBooleanMul.N5.MissingCosetQuadratic
import UnrestrictedBooleanMul.N5.TargetCleanMatrix

/-!
# Target-clean reduction for the rank-one colour branch

This module joins manuscript equations (11.2) and (11.7).  A quadratic part
belonging to the target-clean second jet, with at most one decomposable
defect direction adjoined, cannot be the missing target representative.
The missing-coset exterior kernels then force both its quadratic and linear
lower parts to vanish.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- No member of the affine missing target coset belongs to the first-order
envelope. -/
theorem missingCoset_targetTwo_not_mem_firstOrderEnvelope
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace) :
    targetTwo (firstOrderMissingCoeff + u) ∉ firstOrderEnvelopeTwoSpace := by
  rintro ⟨c, hc, htarget⟩
  have hcoeff : c = firstOrderMissingCoeff + u := by
    apply targetTwoLinear_injective
    exact htarget
  have hmissing : firstOrderMissingCoeff ∈
      firstOrderEnvelopeCoeffSpace := by
    have hsub := firstOrderEnvelopeCoeffSpace.sub_mem (hcoeff ▸ hc) hu
    simpa using hsub
  exact firstOrderMissingCoeff_not_mem hmissing

/-- Equation (11.7) excludes the missing target representative from every
old target-clean quadratic base with one decomposable defect direction. -/
theorem targetClean_sup_decomposable_ne_missingCoset
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (q : TwoForm) (hqdec : IsDecomposableTwo q)
    (C : TwoForm)
    (hC : C ∈ targetCleanSecondJetSpace ⊔
      Submodule.span F₂ ({q} : Set TwoForm)) :
    C ≠ targetTwo (firstOrderMissingCoeff + u) := by
  intro hCeq
  have hpT : targetTwo (firstOrderMissingCoeff + u) ∈ targetTwoSpace :=
    ⟨firstOrderMissingCoeff + u, rfl⟩
  have hpSup : targetTwo (firstOrderMissingCoeff + u) ∈
      targetCleanSecondJetSpace ⊔
        Submodule.span F₂ ({q} : Set TwoForm) := by
    rwa [← hCeq]
  have hpInf : targetTwo (firstOrderMissingCoeff + u) ∈
      targetTwoSpace ⊓
        (targetCleanSecondJetSpace ⊔
          Submodule.span F₂ ({q} : Set TwoForm)) :=
    ⟨hpT, hpSup⟩
  rw [targetTwoSpace_inf_targetClean_sup_decomposable q hqdec] at hpInf
  exact missingCoset_targetTwo_not_mem_firstOrderEnvelope u hu hpInf

/-- Rank-one target-clean consequence used in manuscript Theorem 12.3:
the quartic and cubic matching equations force the old factor's lower parts
to vanish. -/
theorem rankOne_targetClean_lower_parts_zero
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (q : TwoForm) (hqdec : IsDecomposableTwo q)
    (C : TwoForm) (ell : LinearForm)
    (hC : C ∈ targetCleanSecondJetSpace ⊔
      Submodule.span F₂ ({q} : Set TwoForm))
    (hfour : ambientWedgeTwo
      (targetTwo (firstOrderMissingCoeff + u)) C = 0)
    (hthree : ambientVectorWedgeTwo ell
      (targetTwo (firstOrderMissingCoeff + u)) = 0) :
    C = 0 ∧ ell = 0 :=
  missingCoset_lower_parts_zero u hu C ell hfour
    (targetClean_sup_decomposable_ne_missingCoset u hu q hqdec C hC)
    hthree

end
end N5
end UnrestrictedBooleanMul
