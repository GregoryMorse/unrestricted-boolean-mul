import UnrestrictedBooleanMul.N5.CapacityRestart
import UnrestrictedBooleanMul.N5.QuadraticReturnFeedback
import UnrestrictedBooleanMul.N5.DefectTwoCapacity
import UnrestrictedBooleanMul.N5.ANFSubstitution

/-!
# Charge the target row of a populated quadratic return

If a returned quadratic section has form `d + targetTwo c`, only the
decomposable form `d` may be appended to the intrinsic-capacity presentation.
The target row `c` is retained as a separate one-dimensional summand.  This
envelope contains the returned wire and has target rank at most capacity
plus one.  Keeping the old high wire does not increase that target rank.

These are local containment and rank bounds.  They do not assert stability
of an arbitrary subsequent suffix.
-/

namespace UnrestrictedBooleanMul.N5
noncomputable section

/-- One additional wire can add at most one target dimension. -/
theorem stateTargetRank_sup_singleton_le
    (V : Submodule F₂ (ANF 10)) (hAff : affine 10 ≤ V) (z : ANF 10) :
    stateTargetRank (V ⊔ Submodule.span F₂ {z}) ≤ stateTargetRank V + 1 := by
  have h := targetDefectRank_andExtend_le_succ V z 1 hAff
  have hd := flagDefectRank_mono (V := V)
    (W := andExtend V z 1) le_sup_left
  simp only [andExtend, mul_one] at h hd
  omega

/-- Capacity after appending the decomposable lift, with its target row
displayed separately. -/
def populatedReturnCapacity {j : Nat} (p : Fin j → TwoForm)
    (d : TwoForm) (c : TargetCoeff) : Submodule F₂ (ANF 10) :=
  intrinsicCapacityState (Fin.snoc p d) ⊔ Submodule.span F₂ {targetANF c}

theorem populatedReturnCapacity_targetRank {j : Nat}
    (p : Fin j → TwoForm) (d : TwoForm) (c : TargetCoeff) :
    stateTargetRank (populatedReturnCapacity p d c) ≤
      targetCapacity (presentationDefect (Fin.snoc p d)) + 1 := by
  exact (stateTargetRank_sup_singleton_le _ (affine_le_intrinsicCapacityState _)
    (targetANF c)).trans_eq (congrArg (· + 1) (intrinsicCapacityState_targetRank _))

theorem intrinsicCapacityState_le_populatedReturnCapacity {j : Nat}
    (p : Fin j → TwoForm) (d : TwoForm) (c : TargetCoeff) :
    intrinsicCapacityState p ≤ populatedReturnCapacity p d c := by
  apply le_trans (b := intrinsicCapacityState (Fin.snoc p d)) _ le_sup_left
  apply E2.quadraticEnvelopeState_mono
  apply defectCapacitySpan_mono
  rw [presentationDefect_snoc]
  exact le_sup_left

/-- The actual quadratic return belongs to the charged envelope. -/
theorem quadraticReturn_mem_populatedReturnCapacity {j : Nat}
    (p : Fin j → TwoForm) (hp : ∀ i, IsDecomposableTwo (p i))
    (z : ANF 10) (hz : z ∈ N4.quadraticANFSpace 10)
    (d : TwoForm) (hd : IsDecomposableTwo d) (c : TargetCoeff)
    (hprojection : quadraticProjection 10 z = d + targetTwo c) :
    z ∈ populatedReturnCapacity p d c := by
  have hdec : ∀ i, IsDecomposableTwo
      ((Fin.snoc (α := fun _ : Fin (j + 1) => TwoForm) p d) i) := by
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [hp, hd]
  have hdCap : d ∈ defectCapacitySpan (presentationDefect (Fin.snoc p d)) := by
    rw [defectCapacitySpan_eq_geometricCapacitySpan]
    simpa using decomposable_mem_geometricCapacitySpan (Fin.snoc p d) hdec (Fin.last j)
  have hdANF : quadraticANFOfForm d ∈ intrinsicCapacityState (Fin.snoc p d) := by
    exact Submodule.mem_sup_right ⟨d, hdCap, rfl⟩
  obtain ⟨a, ell, q, heq⟩ := exists_quadraticCoordinates hz
  have hq : q = d + targetTwo c := by simpa [heq] using hprojection
  have hANF : z = (a • (1 : ANF 10) + linearANFTen ell) +
      quadraticANFOfForm d + targetANF c := by
    rw [heq, quadraticCoordinateANF, hq]
    change _ + quadraticANFOfFormLinear (d + targetTwo c) = _
    rw [map_add]
    change _ + (quadraticANFOfForm d + quadraticANFOfForm (targetTwo c)) = _
    rw [quadraticANFOfForm_targetTwo]
    ac_rfl
  rw [hANF]
  apply (populatedReturnCapacity p d c).add_mem
  · apply Submodule.mem_sup_left
    exact (intrinsicCapacityState (Fin.snoc p d)).add_mem
      (affine_le_intrinsicCapacityState _ ((affine 10).add_mem
        ((affine 10).smul_mem a (one_mem_affine 10)) (linearANFTen_mem_affine ell))) hdANF
  · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))

theorem populatedReturnCapacity_quadratic {j : Nat}
    (p : Fin j → TwoForm) (d : TwoForm) (c : TargetCoeff) :
    populatedReturnCapacity p d c ≤ N4.quadraticANFSpace 10 := by
  apply sup_le (E2.quadraticEnvelopeState_le_quadraticANFSpace _)
  apply Submodule.span_le.mpr
  rintro z rfl
  exact pureQuadraticANFSpace_le_quadraticANFSpace (targetANF_mem_pure c)

/-- Retaining the genuinely high representative adds no target direction to
the quadratic envelope; its cost has not been erased by the restart. -/
theorem populatedReturnCapacity_with_high_targetRank {j : Nat}
    (p : Fin j → TwoForm) (d : TwoForm) (c : TargetCoeff)
    (U : ANF 10) (hU : U ∉ N4.quadraticANFSpace 10) :
    stateTargetRank (populatedReturnCapacity p d c ⊔ Submodule.span F₂ {U}) =
      stateTargetRank (populatedReturnCapacity p d c) := by
  have h := inf_unchanged_of_first_high_ten _ _ U
    (populatedReturnCapacity_quadratic p d c)
    targetAmbient_five_le_quadraticANFSpace hU
  exact congrArg (fun W : Submodule F₂ (ANF 10) =>
    Module.finrank F₂ W - Module.finrank F₂ (affine 10)) h

/-- A populated return into quadratic defect at most two, including its old
high representative, has charged target rank at most seven. -/
theorem populatedReturnCapacity_with_high_targetRank_le_seven {j : Nat}
    (p : Fin j → TwoForm) (d : TwoForm) (c : TargetCoeff)
    (hdef : Module.finrank F₂ (presentationDefect (Fin.snoc p d)) ≤ 2)
    (U : ANF 10) (hU : U ∉ N4.quadraticANFSpace 10) :
    stateTargetRank (populatedReturnCapacity p d c ⊔ Submodule.span F₂ {U}) ≤ 7 := by
  rw [populatedReturnCapacity_with_high_targetRank p d c U hU]
  have h := populatedReturnCapacity_targetRank p d c
  have hc := targetCapacity_le_six_of_finrank_le_two _ hdef
  omega

/-- The populated alternative supplies a charged capacity envelope containing
the actual returned section and retaining every old high wire. -/
theorem populatedReturn_charged_envelope {j : Nat}
    (p : Fin j → TwoForm) (hp : ∀ i, IsDecomposableTwo (p i))
    (z : ANF 10) (hz : z ∈ N4.quadraticANFSpace 10)
    (hpop : IsPopulatedFiber (quadraticQuotientProjection (quadraticProjection 10 z)))
    (U : ANF 10) :
    ∃ d c, IsDecomposableTwo d ∧ quadraticProjection 10 z = d + targetTwo c ∧
      (intrinsicCapacityState p ⊔ Submodule.span F₂ {z}) ⊔ Submodule.span F₂ {U} ≤
        populatedReturnCapacity p d c ⊔ Submodule.span F₂ {U} := by
  obtain ⟨d, c, hd, hc⟩ :=
    (populatedQuadraticSection_iff_exists_decomposable_add_target _).1 hpop
  refine ⟨d, c, hd, hc, sup_le_sup ?_ le_rfl⟩
  apply sup_le (intrinsicCapacityState_le_populatedReturnCapacity p d c)
  apply Submodule.span_le.mpr
  intro w hw
  have heq : w = z := Set.mem_singleton_iff.mp hw
  change w ∈ populatedReturnCapacity p d c
  rw [heq]
  exact quadraticReturn_mem_populatedReturnCapacity p hp z hz d hd c hc

end
end UnrestrictedBooleanMul.N5
