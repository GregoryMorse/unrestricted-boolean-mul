import UnrestrictedBooleanMul.N5.EnvelopeRankTwoPlaneTypes

/-!
# Intrinsic classification of independent first-order planes

The cubic-syzygy split is entirely algebraic.  An independent syzygy forces
the three projective directions of the plane into the rank-two Hankel locus;
the eight lines of that locus are then the six exceptional rational lines,
the degree-two translate, and the cubic-rigid rational triangle.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private theorem independentCubicSyzygy_plane_classification
    (q c : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (x y : LinearForm) (hxy : LinearIndependent F₂ ![x, y])
    (hcubic : factorPlaneCubic x y q c = 0) :
    IsExceptionalIndependentPlanePresentation q c ∨
      IsDegreeTwoTranslatePlanePresentation q c ∨
      CubicRigidPlane q c := by
  rcases hq with ⟨d, hd, hdq⟩
  rcases hc with ⟨e, he, hec⟩
  have hcubic' : factorPlaneCubic x y (targetTwo d) (targetTwo e) = 0 := by
    change factorPlaneCubic x y (targetTwoLinear d) (targetTwoLinear e) = 0
    rw [hdq, hec]
    exact hcubic
  have hrank := targetPlane_rankTwo_of_independent_cubic_syzygy
    d e x y hxy hcubic'
  rcases quadraticPlaneDirections_independent_nonzero_ne q c hind with
    ⟨hq0, hc0, hqc⟩
  have hd0 : d ≠ 0 := by
    intro hzero
    apply hq0
    rw [← hdq, hzero]
    exact map_zero targetTwoLinear
  have he0 : e ≠ 0 := by
    intro hzero
    apply hc0
    rw [← hec, hzero]
    exact map_zero targetTwoLinear
  have hde : d ≠ e := by
    intro hsame
    apply hqc
    rw [← hdq, ← hec, hsame]
  rcases rankTwo_plane_canonical d e hrank.1 hrank.2.1 hrank.2.2
      hd0 he0 hde with ⟨p, g, hdg, heg⟩
  have hqg : q = (g.basisPair
      (targetTwo (canonicalRankTwoLeftCoeff p))
      (targetTwo (canonicalRankTwoRightCoeff p))).1 := by
    calc
      q = targetTwo d := hdq.symm
      _ = targetTwo (g.basisPair (canonicalRankTwoLeftCoeff p)
          (canonicalRankTwoRightCoeff p)).1 := congrArg targetTwo hdg
      _ = (g.basisPair (targetTwo (canonicalRankTwoLeftCoeff p))
          (targetTwo (canonicalRankTwoRightCoeff p))).1 :=
        targetTwo_basisPair_fst g _ _
  have hcg : c = (g.basisPair
      (targetTwo (canonicalRankTwoLeftCoeff p))
      (targetTwo (canonicalRankTwoRightCoeff p))).2 := by
    calc
      c = targetTwo e := hec.symm
      _ = targetTwo (g.basisPair (canonicalRankTwoLeftCoeff p)
          (canonicalRankTwoRightCoeff p)).2 := congrArg targetTwo heg
      _ = (g.basisPair (targetTwo (canonicalRankTwoLeftCoeff p))
          (targetTwo (canonicalRankTwoRightCoeff p))).2 :=
        targetTwo_basisPair_snd g _ _
  exact canonicalRankTwoPlane_target_classification p g q c hqg hcg

/-- Every independent plane in the first-order envelope is either
cubic-rigid, exceptional, the degree-two translate, or a regular plane
containing a rational value direction. -/
theorem independentFirstOrderPlane_intrinsic_classification
    (q c : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    CubicRigidPlane q c ∨
      IsExceptionalIndependentPlanePresentation q c ∨
      IsDegreeTwoTranslatePlanePresentation q c ∨
      IsRationalValueRegularPlanePresentation q c := by
  by_cases hrigid : CubicRigidPlane q c
  · exact Or.inl hrigid
  simp only [CubicRigidPlane, not_forall, not_and_or] at hrigid
  rcases hrigid with ⟨x, y, hcubic, hnonzero⟩
  by_cases hxy : LinearIndependent F₂ ![x, y]
  · rcases independentCubicSyzygy_plane_classification
      q c hq hc hind x y hxy hcubic with hexceptional | htranslate | htriangle
    · exact Or.inr (Or.inl hexceptional)
    · exact Or.inr (Or.inr (Or.inl htranslate))
    · exact Or.inl htriangle
  · rcases linearPair_dependent_classification_f2 x y hxy with
      hx0 | hy0 | hxyEq
    · have hy : y ≠ 0 := by
        rcases hnonzero with hx | hy
        · exact (hx hx0).elim
        · exact hy
      have hq' := hq
      rcases hq' with ⟨d, hd, hdq⟩
      have hd0 : d ≠ 0 := by
        intro hdZero
        have hqZero : q = 0 := by
          rw [← hdq, hdZero]
          exact map_zero targetTwoLinear
        exact (quadraticPlaneDirections_independent_nonzero_ne q c hind).1 hqZero
      have hzero : ambientVectorWedgeTwo y (targetTwo d) = 0 := by
        change ambientVectorWedgeTwo y (targetTwoLinear d) = 0
        rw [hdq]
        rw [hx0, factorPlaneCubic] at hcubic
        simpa only [ambientVectorWedgeTwo_zero_left, zero_add] using hcubic
      rcases targetCoeff_eq_rationalValue_of_annihilator
          d y hd0 hy hzero with ⟨place, hplace⟩
      have hfirst : (PlaneBasisChange.identity.basisPair q c).1 =
          targetTwo (rationalValueCoeff place) := by
        change q = targetTwoLinear (rationalValueCoeff place)
        rw [← hdq, hplace]
      rcases rationalDirection_plane_regular_or_exceptional
          q c hq hc hind place .identity hfirst with hregular | hexceptional
      · exact Or.inr (Or.inr (Or.inr hregular))
      · exact Or.inr (Or.inl hexceptional)
    · have hx : x ≠ 0 := by
        rcases hnonzero with hx | hy
        · exact hx
        · exact (hy hy0).elim
      have hc' := hc
      rcases hc' with ⟨e, he, hec⟩
      have he0 : e ≠ 0 := by
        intro heZero
        have hcZero : c = 0 := by
          rw [← hec, heZero]
          exact map_zero targetTwoLinear
        exact (quadraticPlaneDirections_independent_nonzero_ne q c hind).2.1 hcZero
      have hzero : ambientVectorWedgeTwo x (targetTwo e) = 0 := by
        change ambientVectorWedgeTwo x (targetTwoLinear e) = 0
        rw [hec]
        rw [hy0, factorPlaneCubic] at hcubic
        simpa only [ambientVectorWedgeTwo_zero_left, add_zero] using hcubic
      rcases targetCoeff_eq_rationalValue_of_annihilator
          e x he0 hx hzero with ⟨place, hplace⟩
      have hfirst : (PlaneBasisChange.swap.basisPair q c).1 =
          targetTwo (rationalValueCoeff place) := by
        change c = targetTwoLinear (rationalValueCoeff place)
        rw [← hec, hplace]
      rcases rationalDirection_plane_regular_or_exceptional
          q c hq hc hind place .swap hfirst with hregular | hexceptional
      · exact Or.inr (Or.inr (Or.inr hregular))
      · exact Or.inr (Or.inl hexceptional)
    · subst y
      have hx : x ≠ 0 := by
        rcases hnonzero with hx | hx <;> exact hx
      have hq' := hq
      have hc' := hc
      rcases hq' with ⟨d, hd, hdq⟩
      rcases hc' with ⟨e, he, hec⟩
      have hde0 : d + e ≠ 0 := by
        intro hzero
        have hde : d = e := by
          funext i
          have hi := congrFun hzero i
          simp only [Pi.add_apply, Pi.zero_apply] at hi
          calc
            d i = d i + 0 := (add_zero _).symm
            _ = d i + (e i + e i) := by
              rw [CharTwo.add_self_eq_zero]
            _ = (d i + e i) + e i := (add_assoc _ _ _).symm
            _ = 0 + e i := by rw [hi]
            _ = e i := zero_add _
        exact (quadraticPlaneDirections_independent_nonzero_ne q c hind).2.2
          (calc
            q = targetTwoLinear d := hdq.symm
            _ = targetTwoLinear e := congrArg targetTwoLinear hde
            _ = c := hec)
      have hzeroQC : ambientVectorWedgeTwo x (q + c) = 0 := by
        rw [ambientVectorWedgeTwo_add]
        rw [factorPlaneCubic] at hcubic
        simpa only [add_comm] using hcubic
      have hzero : ambientVectorWedgeTwo x (targetTwo (d + e)) = 0 := by
        change ambientVectorWedgeTwo x (targetTwoLinear (d + e)) = 0
        rw [map_add, hdq, hec]
        exact hzeroQC
      rcases targetCoeff_eq_rationalValue_of_annihilator
          (d + e) x hde0 hx hzero with ⟨place, hplace⟩
      have hfirst : (PlaneBasisChange.rotateLeft.basisPair q c).1 =
          targetTwo (rationalValueCoeff place) := by
        change q + c = targetTwo (rationalValueCoeff place)
        change q + c = targetTwoLinear (rationalValueCoeff place)
        rw [← hdq, ← hec, ← hplace]
        exact (map_add targetTwoLinear d e).symm
      rcases rationalDirection_plane_regular_or_exceptional
          q c hq hc hind place .rotateLeft hfirst with hregular | hexceptional
      · exact Or.inr (Or.inr (Or.inr hregular))
      · exact Or.inr (Or.inl hexceptional)

end
end N5
end UnrestrictedBooleanMul
