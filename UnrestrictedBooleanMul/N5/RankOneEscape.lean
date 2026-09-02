import UnrestrictedBooleanMul.N5.FirstOrderEscape
import UnrestrictedBooleanMul.N5.RankOneTargetClean
import UnrestrictedBooleanMul.N5.QuarticSemantic
import UnrestrictedBooleanMul.N5.RankOneShadow
import UnrestrictedBooleanMul.N5.CubicOverlapBasis

/-!
# Exclusion of a rank-one-colour target escape

This is the algebraic contradiction at the end of the rank-one branch of
manuscript Theorem 12.3.  The two Boolean absorption identities force the
old quadratic factor to be the constant one; the product identity then says
that a genuinely high wire is itself quadratic.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- A genuinely high wire cannot produce a missing-coset target through a
target-clean quadratic factor while satisfying the Boolean absorption
identity supplied by rank-one colour normalization. -/
theorem rankOne_targetClean_absorption_impossible
    (U : ANF 10) (hUhigh : U ∉ N4.quadraticANFSpace 10)
    (fConst cConst : F₂) (fLinear cLinear : LinearForm)
    (u : TargetCoeff) (hu : u ∈ firstOrderEnvelopeCoeffSpace)
    (q C : TwoForm) (hqdec : IsDecomposableTwo q)
    (hC : C ∈ targetCleanSecondJetSpace ⊔
      Submodule.span F₂ ({q} : Set TwoForm))
    (hproduct :
      U * quadraticCoordinateANF cConst cLinear C =
        quadraticCoordinateANF fConst fLinear
          (targetTwo (firstOrderMissingCoeff + u)))
    (habsorb :
      quadraticCoordinateANF fConst fLinear
          (targetTwo (firstOrderMissingCoeff + u)) *
        quadraticCoordinateANF cConst cLinear C =
      quadraticCoordinateANF fConst fLinear
        (targetTwo (firstOrderMissingCoeff + u))) : False := by
  let Ftwo := targetTwo (firstOrderMissingCoeff + u)
  let F := quadraticCoordinateANF fConst fLinear Ftwo
  let c := quadraticCoordinateANF cConst cLinear C
  change U * c = F at hproduct
  change F * c = F at habsorb
  have hFquad : F ∈ N4.quadraticANFSpace 10 :=
    quadraticCoordinateANF_mem_quadraticANFSpace fConst fLinear Ftwo
  have hfour : ambientWedgeTwo Ftwo C = 0 := by
    calc
      ambientWedgeTwo Ftwo C = anfFourProjectionTen (F * c) := by
        symm
        exact anfFourProjectionTen_quadraticCoordinateANF_mul
          fConst cConst fLinear cLinear Ftwo C
      _ = anfFourProjectionTen F := congrArg anfFourProjectionTen habsorb
      _ = 0 := anfFourProjectionTen_eq_zero_of_degreeLE_three
        (hFquad.mono (by omega))
  have hthree : ambientVectorWedgeTwo cLinear Ftwo = 0 := by
    have hCzero : C = 0 := by
      rcases (missingCoset_wedge_eq_zero_iff u hu C).1 hfour with
        ⟨a, ha⟩
      rcases f2_eq_zero_or_one a with ha0 | ha1
      · rw [ha, ha0, zero_smul]
      · exfalso
        apply targetClean_sup_decomposable_ne_missingCoset
          u hu q hqdec C hC
        simpa [ha1] using ha
    calc
      ambientVectorWedgeTwo cLinear Ftwo =
          factorPlaneCubic fLinear cLinear Ftwo 0 := by
            symm
            exact factorPlaneCubic_zero_right fLinear cLinear Ftwo
      _ = exactLowProductCubic fLinear cLinear Ftwo 0 := by
        simp [exactLowProductCubic]
      _ = anfThreeProjectionTen (F * c) := by
        change exactLowProductCubic fLinear cLinear Ftwo 0 =
          anfThreeProjectionTen
            (quadraticCoordinateANF fConst fLinear Ftwo *
              quadraticCoordinateANF cConst cLinear C)
        rw [hCzero]
        symm
        exact anfThreeProjectionTen_quadraticCoordinateANF_mul
          fConst cConst fLinear cLinear Ftwo 0
      _ = anfThreeProjectionTen F := congrArg anfThreeProjectionTen habsorb
      _ = 0 := anfThreeProjectionTen_eq_zero_of_quadratic hFquad
  have hlower := rankOne_targetClean_lower_parts_zero
    u hu q hqdec C cLinear hC hfour hthree
  have hcConstant : c = cConst • (1 : ANF 10) := by
    simp [c, quadraticCoordinateANF, hlower.1, hlower.2,
      show quadraticANFOfForm (0 : TwoForm) = 0 by
        exact map_zero quadraticANFOfFormLinear]
  have hFtwoNotZero : Ftwo ≠ 0 := by
    intro hzero
    apply missingCoset_targetTwo_not_mem_firstOrderEnvelope u hu
    rw [show targetTwo (firstOrderMissingCoeff + u) = 0 by exact hzero]
    exact firstOrderEnvelopeTwoSpace.zero_mem
  rcases f2_eq_zero_or_one cConst with hc0 | hc1
  · have hFzero : F = 0 := by
      have h := habsorb
      rw [hcConstant, hc0, zero_smul, mul_zero] at h
      exact h.symm
    apply hFtwoNotZero
    have hprojection := congrArg (quadraticProjection 10) hFzero
    simpa [F] using hprojection
  · apply hUhigh
    have h := hproduct
    rw [hcConstant, hc1, one_smul, mul_one] at h
    rw [h]
    exact hFquad

end
end N5
end UnrestrictedBooleanMul
