import UnrestrictedBooleanMul.N5.QuadraticReturnOffAxisSymmetry

/-!
# Boolean factor shears reduce four return charts to two

Replacing a factor pair `(A,B)` by `(A,A+B)` changes its product by the
already available wire `A`, since `A²=A`.  The same change in the comparison
product alters the returned section only by the affine shift of `A`.
Adjusting the old-state correction by `A` and that affine shift leaves the
later feedback product exactly unchanged.

Consequently `(1,1)` reduces to `(0,1)` and `(1,3)` reduces to `(1,2)`.
The target row `r0` added to the correction is explicit throughout.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section

inductive ReturnFactorShear where
  | equal
  | incident

def ReturnFactorShear.source : ReturnFactorShear → MixedReturnFactorPair
  | .equal => .oneOneDifference
  | .incident => .oneThree

def ReturnFactorShear.target : ReturnFactorShear → MixedReturnFactorPair
  | .equal => .zeroOne
  | .incident => .oneTwo

/-- The correction includes the old left factor and the shifted return row. -/
def ReturnFactorShear.parameters (s : ReturnFactorShear)
    (p : ZeroOneOffAxisHistoryParameters) : ZeroOneOffAxisHistoryParameters where
  ell := match s with | .equal => p.m | .incident => p.ell
  m := match s with | .equal => p.ell | .incident => p.m + p.ell
  leftShift := match s with | .equal => p.leftShift + p.rightShift | .incident => p.leftShift
  rightShift := match s with | .equal => p.leftShift | .incident => p.rightShift + p.leftShift
  feedbackConstant := p.feedbackConstant
  feedbackLinear := p.feedbackLinear
  correctionConstant := p.correctionConstant
  correctionLinear := p.correctionLinear + p.ell + p.correctionReturn • p.leftShift
  correctionTarget := returnHistoryCoordinates (p.correctionCoeff + rZeroCoeff)
  correctionReturn := p.correctionReturn

theorem ReturnFactorShear.correctionCoeff (s : ReturnFactorShear)
    (p : ZeroOneOffAxisHistoryParameters) :
    (s.parameters p).correctionCoeff = p.correctionCoeff + rZeroCoeff := by
  apply returnHistoryCoordinates_reconstruct
  rw [map_add, p.correctionCoeff_missing]
  simp [firstOrderMissingFunctional, rZeroCoeff]

private theorem targetANF_add (c d : TargetCoeff) :
    targetANF (c + d) = targetANF c + targetANF d := by
  rw [← quadraticANFOfForm_targetTwo]
  change quadraticANFOfFormLinear (targetTwoLinear (c + d)) = _
  rw [map_add, map_add]
  exact congrArg₂ (· + ·) (quadraticANFOfForm_targetTwo c)
    (quadraticANFOfForm_targetTwo d)

/-- The first high product changes by the old left factor only. -/
theorem ReturnFactorShear.firstProduct (s : ReturnFactorShear)
    (p : ZeroOneOffAxisHistoryParameters) :
    mixedReturnFirstProduct s.target (s.parameters p) =
      mixedReturnFirstProduct s.source p +
        quadraticCoordinateANF 0 p.ell (targetTwo rZeroCoeff) := by
  cases s <;>
    simp only [ReturnFactorShear.target, ReturnFactorShear.source,
      ReturnFactorShear.parameters, mixedReturnFirstProduct,
      MixedReturnFactorPair.leftTwo, MixedReturnFactorPair.rightTwo,
      MixedReturnFactorPair.rightLinear, quadraticCoordinateANF,
      quadraticANFOfForm_targetTwo, targetANF_add,
      quadraticANFOfForm_zero, zero_smul, zero_add, add_zero,
      linearANFTen_add] <;>
    ring_nf <;> simp only [pow_two, N4.anf_mul_self, anf_two_eq_zero,
      mul_zero, add_zero] <;> ring_nf <;> simp [anf_two_eq_zero]

/-- The returned section changes by an affine wire, hence its quotient and
target coordinates remain unchanged. -/
theorem ReturnFactorShear.section (s : ReturnFactorShear)
    (p : ZeroOneOffAxisHistoryParameters) :
    mixedReturnSection s.target (s.parameters p) =
      mixedReturnSection s.source p + linearANFTen p.leftShift := by
  cases s <;>
    simp only [ReturnFactorShear.target, ReturnFactorShear.source,
      ReturnFactorShear.parameters, mixedReturnSection,
      mixedReturnFirstProduct, mixedReturnShiftedProduct,
      MixedReturnFactorPair.leftTwo, MixedReturnFactorPair.rightTwo,
      MixedReturnFactorPair.rightLinear, quadraticCoordinateANF,
      quadraticANFOfForm_targetTwo, targetANF_add,
      quadraticANFOfForm_zero, zero_smul, zero_add, add_zero,
      linearANFTen_add] <;>
    ring_nf <;> simp only [pow_two, N4.anf_mul_self, anf_two_eq_zero,
      mul_zero, add_zero, zero_add] <;> ring_nf <;> simp

/-- The adjusted old high representative is literally the same ANF. -/
theorem ReturnFactorShear.correctedHigh (s : ReturnFactorShear)
    (p : ZeroOneOffAxisHistoryParameters) :
    mixedReturnCorrectedHigh s.target (s.parameters p) =
      mixedReturnCorrectedHigh s.source p := by
  simp only [mixedReturnCorrectedHigh, mixedReturnCorrection,
    s.firstProduct, s.section,
    ZeroOneOffAxisHistoryParameters.correctionTwo_eq_targetTwo,
    s.correctionCoeff, quadraticCoordinateANF,
    quadraticANFOfForm_targetTwo, targetANF_add]
  simp only [ReturnFactorShear.parameters, linearANFTen_add,
    linearANFTen_smul, zero_smul, zero_add, smul_add]
  ring_nf
  simp [anf_two_eq_zero]

/-- The later feedback gate is unchanged, in every rational direction. -/
theorem ReturnFactorShear.feedback (s : ReturnFactorShear)
    (direction : RationalFeedbackDirection) (p : ZeroOneOffAxisHistoryParameters) :
    mixedReturnFeedbackProduct s.target direction (s.parameters p) =
    mixedReturnFeedbackProduct s.source direction p := by
  rw [mixedReturnFeedbackProduct, mixedReturnFeedbackProduct, s.correctedHigh]
  rfl

/-- Package the complete semantic transport needed by the two basic charts. -/
theorem ReturnFactorShear.quadratic_history (s : ReturnFactorShear)
    (direction : RationalFeedbackDirection) (p : ZeroOneOffAxisHistoryParameters)
    (hr : mixedReturnSection s.source p ∈ N4.quadraticANFSpace 10)
    (hf : mixedReturnFeedbackProduct s.source direction p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (hc : quadraticProjection 10 (mixedReturnSection s.source p) +
      quadraticProjection 10 (mixedReturnFeedbackProduct s.source direction p) =
        targetTwo c) :
    mixedReturnSection s.target (s.parameters p) ∈ N4.quadraticANFSpace 10 ∧
    mixedReturnFeedbackProduct s.target direction (s.parameters p) ∈ N4.quadraticANFSpace 10 ∧
    quadraticProjection 10 (mixedReturnSection s.target (s.parameters p)) +
      quadraticProjection 10 (mixedReturnFeedbackProduct s.target direction (s.parameters p)) =
        targetTwo c := by
  rw [s.section, s.feedback]
  refine ⟨(N4.quadraticANFSpace 10).add_mem hr
    (N4.affine_le_quadraticANFSpace (linearANFTen_mem_affine _)), hf, ?_⟩
  simpa using hc

private theorem sup_span_add_old (W : Submodule F₂ (ANF 10))
    (g a : ANF 10) (ha : a ∈ W) :
    W ⊔ Submodule.span F₂ {g + a} = W ⊔ Submodule.span F₂ {g} := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    intro z hz
    have hz' : z = g + a := Set.mem_singleton_iff.mp hz
    rw [hz']
    exact Submodule.add_mem _
      (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
      (Submodule.mem_sup_left ha)
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    intro z hz
    have hz' : z = g := Set.mem_singleton_iff.mp hz
    rw [hz']
    change g ∈ W ⊔ Submodule.span F₂ {g + a}
    have h := (W ⊔ Submodule.span F₂ {g + a}).add_mem
      (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton (g + a))))
      (Submodule.mem_sup_left ha)
    simpa only [add_assoc, anf_add_self, add_zero] using h

/-- The shear preserves the actual intermediate wire state after the first
gate.  The added left factor was already available, so no AND is added. -/
theorem ReturnFactorShear.firstWireState (s : ReturnFactorShear)
    (p : ZeroOneOffAxisHistoryParameters) (W : Submodule F₂ (ANF 10))
    (hleft : quadraticCoordinateANF 0 p.ell (targetTwo rZeroCoeff) ∈ W) :
    W ⊔ Submodule.span F₂ {mixedReturnFirstProduct s.target (s.parameters p)} =
      W ⊔ Submodule.span F₂ {mixedReturnFirstProduct s.source p} := by
  rw [s.firstProduct]
  exact sup_span_add_old W _ _ hleft

/-- The state after the equal-high comparison is preserved as well, with
the old high representative still present. -/
theorem ReturnFactorShear.returnWireState (s : ReturnFactorShear)
    (p : ZeroOneOffAxisHistoryParameters) (W : Submodule F₂ (ANF 10))
    (hAff : affine 10 ≤ W)
    (hleft : quadraticCoordinateANF 0 p.ell (targetTwo rZeroCoeff) ∈ W) :
    (W ⊔ Submodule.span F₂ {mixedReturnFirstProduct s.target (s.parameters p)}) ⊔
      Submodule.span F₂ {mixedReturnSection s.target (s.parameters p)} =
    (W ⊔ Submodule.span F₂ {mixedReturnFirstProduct s.source p}) ⊔
      Submodule.span F₂ {mixedReturnSection s.source p} := by
  rw [s.firstWireState p W hleft, s.section]
  exact sup_span_add_old _ _ _
    (Submodule.mem_sup_left (hAff (linearANFTen_mem_affine _)))

end
end UnrestrictedBooleanMul.N5
