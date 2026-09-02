import UnrestrictedBooleanMul.N5.FirstOrderLowCollision
import UnrestrictedBooleanMul.N5.RankOneEscape

/-!
# Absorbing first-order corrections in the rank-one branch

An old correction lying in the first-order envelope contributes only affine
coordinates and an allowed target coefficient.  Absorbing those coordinates
into the missing-coset target reduces the corrected escape to the already
checked Boolean-absorption contradiction.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The terminal rank-one contradiction remains valid when the product
equation contains an arbitrary correction from the first-order envelope. -/
theorem rankOne_targetClean_envelopeCorrection_impossible
    (U : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (fConst cConst : F₂) (fLinear cLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (q C : TwoForm) (hqdec : IsDecomposableTwo q)
    (hC : C ∈ targetCleanSecondJetSpace ⊔
      Submodule.span F₂ ({q} : Set TwoForm))
    (v : ANF 10) (hv : v ∈ firstOrderEnvelopeState)
    (hproduct :
      U * quadraticCoordinateANF cConst cLinear C =
        quadraticCoordinateANF fConst fLinear
          (targetTwo (firstOrderMissingCoeff + u)) + v)
    (habsorb :
      (U * quadraticCoordinateANF cConst cLinear C) *
          quadraticCoordinateANF cConst cLinear C =
        U * quadraticCoordinateANF cConst cLinear C) : False := by
  rcases exists_firstOrderCoeff_of_mem_envelopeState hv with
    ⟨uv, huv, hprojectionV⟩
  have hvquad : v ∈ N4.quadraticANFSpace 10 :=
    E2.quadraticEnvelopeState_le_quadraticANFSpace
      firstOrderEnvelopeTwoSpace hv
  rcases exists_quadraticCoordinates hvquad with
    ⟨vConst, vLinear, vTwo, hvCoordinates⟩
  have hvTwo : vTwo = targetTwo uv := by
    calc
      vTwo = quadraticProjection 10 v := by
        rw [hvCoordinates, quadraticProjection_quadraticCoordinateANF]
      _ = targetTwo uv := hprojectionV
  subst vTwo
  let F := quadraticCoordinateANF (fConst + vConst) (fLinear + vLinear)
    (targetTwo (firstOrderMissingCoeff + (u + uv)))
  have htargetAdd :
      targetTwo (firstOrderMissingCoeff + u) + targetTwo uv =
        targetTwo (firstOrderMissingCoeff + (u + uv)) := by
    change targetTwoLinear (firstOrderMissingCoeff + u) +
        targetTwoLinear uv =
      targetTwoLinear (firstOrderMissingCoeff + (u + uv))
    rw [← targetTwoLinear.map_add]
    congr 1
    ac_rfl
  have hproductF :
      U * quadraticCoordinateANF cConst cLinear C = F := by
    rw [hproduct, hvCoordinates, quadraticCoordinateANF_add, htargetAdd]
  have habsorbF :
      F * quadraticCoordinateANF cConst cLinear C = F := by
    calc
      F * quadraticCoordinateANF cConst cLinear C =
          (U * quadraticCoordinateANF cConst cLinear C) *
            quadraticCoordinateANF cConst cLinear C := by rw [hproductF]
      _ = U * quadraticCoordinateANF cConst cLinear C := habsorb
      _ = F := hproductF
  exact rankOne_targetClean_absorption_impossible
    U hUhigh (fConst + vConst) cConst (fLinear + vLinear) cLinear
      (u + uv) (firstOrderEnvelopeCoeffSpace.add_mem hu huv)
      q C hqdec hC hproductF habsorbF

end
end N5
end UnrestrictedBooleanMul
