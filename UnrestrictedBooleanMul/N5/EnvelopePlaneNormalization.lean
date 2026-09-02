import UnrestrictedBooleanMul.N5.EnvelopeRationalTriangle

/-!
# Normal forms for first-order envelope planes

This file supplies the algebraic normalization lemmas used by the complete
independent-plane classification.  In particular, a dependent cubic syzygy
exhibits a rational direction, and a plane containing such a direction is
either a regular rational-value plane or one of the exceptional planes.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The target embedding commutes with every ordered basis change of a
two-dimensional coefficient plane. -/
theorem targetTwo_basisPair (g : PlaneBasisChange) (d e : TargetCoeff) :
    (targetTwo (g.basisPair d e).1, targetTwo (g.basisPair d e).2) =
      g.basisPair (targetTwo d) (targetTwo e) := by
  cases g <;>
    simp [PlaneBasisChange.basisPair, targetTwo, map_add]

theorem targetTwo_basisPair_fst (g : PlaneBasisChange) (d e : TargetCoeff) :
    targetTwo (g.basisPair d e).1 =
      (g.basisPair (targetTwo d) (targetTwo e)).1 :=
  congrArg Prod.fst (targetTwo_basisPair g d e)

theorem targetTwo_basisPair_snd (g : PlaneBasisChange) (d e : TargetCoeff) :
    targetTwo (g.basisPair d e).2 =
      (g.basisPair (targetTwo d) (targetTwo e)).2 :=
  congrArg Prod.snd (targetTwo_basisPair g d e)

theorem ambientVectorWedgeTwo_add (x : LinearForm) (q c : TwoForm) :
    ambientVectorWedgeTwo x (q + c) =
      ambientVectorWedgeTwo x q + ambientVectorWedgeTwo x c := by
  funext i j k
  simp only [ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    ambientTwoCoeff_add, Pi.add_apply]
  ring

@[simp] theorem ambientVectorWedgeTwo_zero_left (q : TwoForm) :
    ambientVectorWedgeTwo 0 q = 0 := by
  funext i j k
  simp [ambientVectorWedgeTwo, N4.vectorWedgeTwoN]

theorem linearPair_dependent_classification_f2
    {V : Type*} [AddCommGroup V] [Module F₂ V]
    (x y : V) (hdep : ¬ LinearIndependent F₂ ![x, y]) :
    x = 0 ∨ y = 0 ∨ x = y := by
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr (Or.inl hy)
  by_cases hxy : x = y
  · exact Or.inr (Or.inr hxy)
  exfalso
  apply hdep
  rw [linearIndependent_fin2]
  change y ≠ 0 ∧ ∀ a : F₂, a • y ≠ x
  refine ⟨hy, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hx
  · simpa using Ne.symm hxy

theorem targetCoeff_eq_rationalValue_of_annihilator
    (d : TargetCoeff) (x : LinearForm) (hd : d ≠ 0) (hx : x ≠ 0)
    (hzero : ambientVectorWedgeTwo x (targetTwo d) = 0) :
    ∃ place : Fin 3, d = rationalValueCoeff place := by
  rcases eq_squarefreeWedge_of_ambientVectorWedgeTwo_eq_zero
      (targetTwo d) x hx hzero with ⟨y, hy⟩
  have hdec : IsDecomposableTwo (targetTwo d) := ⟨x, y, hy⟩
  rcases decomposableTarget_classification hdec hd with h | h | h
  · exact ⟨0, by simpa [rationalValueCoeff] using h⟩
  · exact ⟨1, by simpa [rationalValueCoeff] using h⟩
  · exact ⟨2, by simpa [rationalValueCoeff] using h⟩

/-- A first-order plane in the orbit of the degree-two translate plane. -/
def IsDegreeTwoTranslatePlanePresentation (q c : TwoForm) : Prop :=
  ∃ g : PlaneBasisChange,
    q = (g.basisPair degreeTwoTranslateLeftTwo
      degreeTwoTranslateRightTwo).1 ∧
    c = (g.basisPair degreeTwoTranslateLeftTwo
      degreeTwoTranslateRightTwo).2

/-- A first-order plane normalized by a rational value and a regular
companion at that value. -/
def IsRationalValueRegularPlanePresentation (q c : TwoForm) : Prop :=
  ∃ (place : Fin 3) (d : TargetCoeff) (g : PlaneBasisChange),
    d ∈ firstOrderEnvelopeCoeffSpace ∧
    RationalValueRegularCompanion place (targetTwo d) ∧
    q = (g.basisPair (targetTwo (rationalValueCoeff place))
      (targetTwo d)).1 ∧
    c = (g.basisPair (targetTwo (rationalValueCoeff place))
      (targetTwo d)).2

theorem rationalDirection_plane_regular_or_exceptional
    (q c : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (place : Fin 3) (g : PlaneBasisChange)
    (hfirst : (g.basisPair q c).1 =
      targetTwo (rationalValueCoeff place)) :
    IsRationalValueRegularPlanePresentation q c ∨
      IsExceptionalIndependentPlanePresentation q c := by
  have hpairMem := g.basisPair_mem_submodule
    firstOrderEnvelopeTwoSpace q c hq hc
  rcases hpairMem.2 with ⟨d, hd, hdEq⟩
  have hchangedInd := g.quadraticPlaneDirections_linearIndependent q c hind
  have hnormalizedInd : LinearIndependent F₂
      (quadraticPlaneDirections (targetTwo (rationalValueCoeff place))
        (targetTwo d)) := by
    simpa only [hfirst, ← hdEq, targetTwo] using hchangedInd
  rcases rationalValue_companion_regular_or_exceptional
      place d hd hnormalizedInd with hregular | hexceptional
  · left
    have hback := g.inverse_basisPair_apply q c
    have hback' : g.inverse.basisPair
        (targetTwo (rationalValueCoeff place)) (targetTwo d) = (q, c) := by
      simpa only [hfirst, ← hdEq, targetTwo] using hback
    exact ⟨place, d, g.inverse, hd, hregular,
      (congrArg Prod.fst hback').symm, (congrArg Prod.snd hback').symm⟩
  · right
    rcases hexceptional with ⟨P, k, hp, hs⟩
    apply isExceptionalIndependentPlanePresentation_of_span_eq P q c hind
    calc
      Submodule.span F₂ ({q, c} : Set TwoForm) =
          Submodule.span F₂ ({(g.basisPair q c).1,
            (g.basisPair q c).2} : Set TwoForm) :=
        (g.span_basisPair_eq q c).symm
      _ = Submodule.span F₂
          ({targetTwo (rationalValueCoeff place), targetTwo d} : Set TwoForm) := by
        rw [hfirst, ← hdEq]
        rfl
      _ = Submodule.span F₂ ({P.left, P.right} : Set TwoForm) := by
        rw [hp, hs]
        exact k.span_basisPair_eq P.left P.right

end
end N5
end UnrestrictedBooleanMul
