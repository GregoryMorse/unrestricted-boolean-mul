import UnrestrictedBooleanMul.N5.EnvelopePlaneNormalization

/-!
# Geometric types of the eight rank-two Hankel lines

This small transport layer identifies the coefficient normal forms with the
ambient two-form presentations used by the shadow lemmas.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem canonicalRankTwoPlane_target_classification
    (p : Fin 8) (g : PlaneBasisChange) (q c : TwoForm)
    (hq : q = (g.basisPair
      (targetTwo (canonicalRankTwoLeftCoeff p))
      (targetTwo (canonicalRankTwoRightCoeff p))).1)
    (hc : c = (g.basisPair
      (targetTwo (canonicalRankTwoLeftCoeff p))
      (targetTwo (canonicalRankTwoRightCoeff p))).2) :
    IsExceptionalIndependentPlanePresentation q c ∨
      IsDegreeTwoTranslatePlanePresentation q c ∨
      CubicRigidPlane q c := by
  fin_cases p
  · left
    change q = (g.basisPair (targetTwo rZeroCoeff)
      (targetTwo jZeroCoeff)).1 at hq
    change c = (g.basisPair (targetTwo rZeroCoeff)
      (targetTwo jZeroCoeff)).2 at hc
    refine ⟨.rationalJet 0, g, ?_, ?_⟩
    · change q = (g.basisPair rationalZeroValueTwo rationalZeroJetTwo).1
      rw [rationalZeroValueTwo_eq_target, rationalZeroJetTwo_eq_target]
      exact hq
    · change c = (g.basisPair rationalZeroValueTwo rationalZeroJetTwo).2
      rw [rationalZeroValueTwo_eq_target, rationalZeroJetTwo_eq_target]
      exact hc
  · left
    change q = (g.basisPair (targetTwo rOneCoeff)
      (targetTwo exactJOneCoeff)).1 at hq
    change c = (g.basisPair (targetTwo rOneCoeff)
      (targetTwo exactJOneCoeff)).2 at hc
    refine ⟨.rationalJet 1, g, ?_, ?_⟩
    · change q = (g.basisPair rationalOneValueTwo rationalOneJetTwo).1
      rw [rationalOneValueTwo_eq_target, rationalOneJetTwo_eq_target]
      exact hq
    · change c = (g.basisPair rationalOneValueTwo rationalOneJetTwo).2
      rw [rationalOneValueTwo_eq_target, rationalOneJetTwo_eq_target]
      exact hc
  · left
    change q = (g.basisPair (targetTwo rInfinityCoeff)
      (targetTwo exactJInfinityCoeff)).1 at hq
    change c = (g.basisPair (targetTwo rInfinityCoeff)
      (targetTwo exactJInfinityCoeff)).2 at hc
    refine ⟨.rationalJet 2, g, ?_, ?_⟩
    · change q = (g.basisPair rationalInfinityValueTwo
        rationalInfinityJetTwo).1
      rw [rationalInfinityValueTwo_eq_target,
        rationalInfinityJetTwo_eq_target]
      exact hq
    · change c = (g.basisPair rationalInfinityValueTwo
        rationalInfinityJetTwo).2
      rw [rationalInfinityValueTwo_eq_target,
        rationalInfinityJetTwo_eq_target]
      exact hc
  · left
    change q = (g.basisPair (targetTwo rZeroCoeff)
      (targetTwo rOneCoeff)).1 at hq
    change c = (g.basisPair (targetTwo rZeroCoeff)
      (targetTwo rOneCoeff)).2 at hc
    refine ⟨.rationalPair 0, g, ?_, ?_⟩
    · change q = (g.basisPair (targetTwo rZeroCoeff)
        (targetTwo rOneCoeff)).1
      exact hq
    · change c = (g.basisPair (targetTwo rZeroCoeff)
        (targetTwo rOneCoeff)).2
      exact hc
  · left
    change q = (g.basisPair (targetTwo rZeroCoeff)
      (targetTwo rInfinityCoeff)).1 at hq
    change c = (g.basisPair (targetTwo rZeroCoeff)
      (targetTwo rInfinityCoeff)).2 at hc
    refine ⟨.rationalPair 1, g, ?_, ?_⟩
    · change q = (g.basisPair (targetTwo rZeroCoeff)
        (targetTwo rInfinityCoeff)).1
      exact hq
    · change c = (g.basisPair (targetTwo rZeroCoeff)
        (targetTwo rInfinityCoeff)).2
      exact hc
  · left
    change q = (g.basisPair (targetTwo rOneCoeff)
      (targetTwo rInfinityCoeff)).1 at hq
    change c = (g.basisPair (targetTwo rOneCoeff)
      (targetTwo rInfinityCoeff)).2 at hc
    refine ⟨.rationalPair 2, g, ?_, ?_⟩
    · change q = (g.basisPair (targetTwo rOneCoeff)
        (targetTwo rInfinityCoeff)).1
      exact hq
    · change c = (g.basisPair (targetTwo rOneCoeff)
        (targetTwo rInfinityCoeff)).2
      exact hc
  · right
    left
    change q = (g.basisPair (targetTwo degreeTwoTranslateLeftCoeff)
      (targetTwo degreeTwoTranslateRightCoeff)).1 at hq
    change c = (g.basisPair (targetTwo degreeTwoTranslateLeftCoeff)
      (targetTwo degreeTwoTranslateRightCoeff)).2 at hc
    exact ⟨g, hq, hc⟩
  · right
    right
    change q = (g.basisPair (targetTwo (rZeroCoeff + rOneCoeff))
      (targetTwo (rZeroCoeff + rInfinityCoeff))).1 at hq
    change c = (g.basisPair (targetTwo (rZeroCoeff + rOneCoeff))
      (targetTwo (rZeroCoeff + rInfinityCoeff))).2 at hc
    have hleft : targetTwo (rZeroCoeff + rOneCoeff) =
        rationalTriangleLeftTwo := by
      rw [rationalTriangleLeftTwo, rationalZeroValueTwo_eq_target,
        rationalOneValueTwo_eq_target]
      exact map_add targetTwoLinear rZeroCoeff rOneCoeff
    have hright : targetTwo (rZeroCoeff + rInfinityCoeff) =
        rationalTriangleRightTwo := by
      rw [rationalTriangleRightTwo, rationalZeroValueTwo_eq_target,
        rationalInfinityValueTwo_eq_target]
      exact map_add targetTwoLinear rZeroCoeff rInfinityCoeff
    rw [hleft, hright] at hq hc
    have htriangle : CubicRigidPlane rationalTriangleLeftTwo
        rationalTriangleRightTwo := rationalTriangle_cubic_syzygy
    have hchanged := cubicRigidPlane_basisChange
      rationalTriangleLeftTwo rationalTriangleRightTwo htriangle g
    rw [hq, hc]
    exact hchanged

end
end N5
end UnrestrictedBooleanMul
