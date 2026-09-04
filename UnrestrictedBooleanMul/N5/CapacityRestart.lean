import UnrestrictedBooleanMul.N5.CapacityReplay

/-!
# Restarting intrinsic-capacity replay at a quadratic defect birth

After redundant gates have been deleted, the first retained gate from an
intrinsic quadratic capacity state has both factors in that quadratic state.
If its product is still quadratic, the scalar quadratic-product alternative
therefore makes its new quadratic form decomposable.  Appending that form to
the old presentation gives an honest decomposable presentation of the
enlarged defect and justifies the next replay restart.

This is the algebraic bridge that prevents a nonlinear suffix from silently
introducing an arbitrary, unpresented quadratic defect.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Appending one quadratic form enlarges the presentation defect by the
span of its quotient class. -/
theorem presentationDefect_snoc {j : Nat} (p : Fin j → TwoForm)
    (q : TwoForm) :
    presentationDefect (Fin.snoc p q) =
      presentationDefect p ⊔
        Submodule.span F₂ ({quadraticQuotientProjection q} :
          Set QuadraticQuotient) := by
  have hfun :
      (fun i : Fin (j + 1) =>
        quadraticQuotientProjection
          ((Fin.snoc (α := TwoForm) p q) i)) =
        Fin.snoc (α := QuadraticQuotient)
          (fun i : Fin j => quadraticQuotientProjection (p i))
          (quadraticQuotientProjection q) := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
  rw [presentationDefect, hfun, Fin.range_snoc, Submodule.span_insert]
  exact sup_comm _ _

/-- Populated fibers, and hence their geometric capacity spans, are monotone
in the quotient defect subspace. -/
theorem geometricCapacitySpan_mono
    {Q Q' : Submodule F₂ QuadraticQuotient} (hQQ' : Q ≤ Q') :
    geometricCapacitySpan Q ≤ geometricCapacitySpan Q' := by
  apply sup_le
  · exact le_sup_left
  · apply (Submodule.span_mono ?_).trans le_sup_right
    rintro x ⟨q, hx⟩
    let q' : PopulatedPoint Q' :=
      ⟨⟨q.1.1, hQQ' q.1.2⟩, q.2⟩
    exact ⟨q', by simpa [q', populatedQuotientPoint] using hx⟩

/-- The choice-independent intrinsic capacity span is monotone in the defect
subspace. -/
theorem defectCapacitySpan_mono
    {Q Q' : Submodule F₂ QuadraticQuotient} (hQQ' : Q ≤ Q') :
    defectCapacitySpan Q ≤ defectCapacitySpan Q' := by
  rw [defectCapacitySpan_eq_geometricCapacitySpan,
    defectCapacitySpan_eq_geometricCapacitySpan]
  exact geometricCapacitySpan_mono hQQ'

/-- Quadratic envelope states are monotone in their coordinate spaces. -/
theorem E2.quadraticEnvelopeState_mono
    {W W' : Submodule F₂ TwoForm} (hWW' : W ≤ W') :
    E2.quadraticEnvelopeState W ≤ E2.quadraticEnvelopeState W' := by
  unfold E2.quadraticEnvelopeState quadraticLiftSpace
  exact sup_le_sup le_rfl (Submodule.map_mono hWW')

/-- A quadratic product retained from an intrinsic capacity state has a
decomposable quadratic form.  The inherited-form alternative would put the
whole product back in the old state, contradicting retention. -/
theorem retainedQuadraticProduct_decomposable
    {j : Nat} (p : Fin j → TwoForm)
    {u v : ANF 10}
    (hu : u ∈ intrinsicCapacityState p)
    (hv : v ∈ intrinsicCapacityState p)
    (hquadratic : u * v ∈ N4.quadraticANFSpace 10)
    (hretained : u * v ∉ intrinsicCapacityState p) :
    IsDecomposableTwo (quadraticProjection 10 (u * v)) := by
  have huData := (E2.mem_quadraticEnvelopeState_iff
    (defectCapacitySpan (presentationDefect p)) u).1 hu
  have hvData := (E2.mem_quadraticEnvelopeState_iff
    (defectCapacitySpan (presentationDefect p)) v).1 hv
  rcases quadratic_product_projection_alternative_ten
      (p := u) (q := v) (g := u * v) rfl
      huData.1 hvData.1 hquadratic with hinherited | hdecomposable
  · exfalso
    apply hretained
    apply (E2.mem_quadraticEnvelopeState_iff
      (defectCapacitySpan (presentationDefect p)) (u * v)).2
    refine ⟨hquadratic, ?_⟩
    apply (Submodule.span_le.mpr ?_) hinherited
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact huData.2
    · exact hvData.2
  · exact hdecomposable

/-- The quotient class of a retained quadratic product is not already in the
old presentation defect.  Otherwise its decomposable quadratic form would
belong to the old intrinsic capacity span. -/
theorem retainedQuadraticProduct_projection_not_mem
    {j : Nat} (p : Fin j → TwoForm)
    {u v : ANF 10}
    (hu : u ∈ intrinsicCapacityState p)
    (hv : v ∈ intrinsicCapacityState p)
    (hquadratic : u * v ∈ N4.quadraticANFSpace 10)
    (hretained : u * v ∉ intrinsicCapacityState p) :
    quadraticQuotientProjection (quadraticProjection 10 (u * v)) ∉
      presentationDefect p := by
  let g₂ := quadraticProjection 10 (u * v)
  have hg₂dec : IsDecomposableTwo g₂ := by
    exact retainedQuadraticProduct_decomposable p hu hv hquadratic hretained
  intro hg₂Q
  have hg₂Old : g₂ ∈ defectCapacitySpan (presentationDefect p) := by
    rw [defectCapacitySpan_eq_geometricCapacitySpan]
    by_cases hg₂zero : quadraticQuotientProjection g₂ = 0
    · exact (le_sup_left : rationalTwoSpace ≤
        rationalTwoSpace ⊔
          Submodule.span F₂ (populatedFiberUnion (presentationDefect p)))
        (zeroFiber_le_rationalTwoSpace hg₂dec hg₂zero)
    · apply (le_sup_right :
        Submodule.span F₂ (populatedFiberUnion (presentationDefect p)) ≤
          rationalTwoSpace ⊔
            Submodule.span F₂
              (populatedFiberUnion (presentationDefect p)))
      apply Submodule.subset_span
      let q : PopulatedPoint (presentationDefect p) :=
        ⟨⟨quadraticQuotientProjection g₂, hg₂Q⟩,
          hg₂zero, ⟨g₂, hg₂dec, rfl⟩⟩
      refine ⟨q, ?_⟩
      simpa [q, populatedQuotientPoint, decomposableFiber] using
        (show IsDecomposableTwo g₂ ∧
            quadraticQuotientProjection g₂ =
              quadraticQuotientProjection g₂ from ⟨hg₂dec, rfl⟩)
  apply hretained
  exact (E2.mem_quadraticEnvelopeState_iff
    (defectCapacitySpan (presentationDefect p)) (u * v)).2
      ⟨hquadratic, hg₂Old⟩

/-- A retained quadratic product from an intrinsic capacity state raises the
target-quotient defect by exactly one.  If the defect image did not grow, the
new product would differ from an old quadratic wire by a target word; after
quadratic projection this would put its class back in the old presentation
defect, contradicting the preceding theorem. -/
theorem retainedQuadraticProduct_defectBirth
    {j : Nat} (p : Fin j → TwoForm)
    (hdec : ∀ i, IsDecomposableTwo (p i))
    {u v : ANF 10}
    (hu : u ∈ intrinsicCapacityState p)
    (hv : v ∈ intrinsicCapacityState p)
    (hquadratic : u * v ∈ N4.quadraticANFSpace 10)
    (hretained : u * v ∉ intrinsicCapacityState p) :
    N4.flagDefectRank
        (andExtend (intrinsicCapacityState p) u v) (mulTarget 5) =
      N4.flagDefectRank (intrinsicCapacityState p) (mulTarget 5) + 1 := by
  let B := intrinsicCapacityState p
  let g := u * v
  have hmono : N4.flagDefectRank B (mulTarget 5) ≤
      N4.flagDefectRank (andExtend B u v) (mulTarget 5) :=
    flagDefectRank_mono le_sup_left
  have hstep := flagDefectRank_andExtend_le_succ B u v
  by_contra hnotBirth
  have hdefEq : N4.flagDefectRank B (mulTarget 5) =
      N4.flagDefectRank (andExtend B u v) (mulTarget 5) := by
    apply Nat.le_antisymm hmono
    exact Nat.lt_succ_iff.mp (lt_of_le_of_ne hstep hnotBirth)
  have himageEq : stateDefectImage B =
      stateDefectImage (andExtend B u v) :=
    stateDefectImage_eq_of_le_of_flagDefectRank_eq le_sup_left hdefEq
  have hgExtend : g ∈ andExtend B u v := by
    apply Submodule.mem_sup_right
    apply Submodule.subset_span
    simp [g]
  have hgImageExtend :
      Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) g ∈
        stateDefectImage (andExtend B u v) :=
    ⟨g, hgExtend, rfl⟩
  have hgImageOld :
      Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) g ∈
        stateDefectImage B := by
    rw [himageEq]
    exact hgImageExtend
  rcases hgImageOld with ⟨b, hb, hbg⟩
  have hdifference : b - g ∈ N4.targetAmbient 10 (mulTarget 5) :=
    (Submodule.Quotient.eq (N4.targetAmbient 10 (mulTarget 5))).1 hbg
  have hprojectionTarget :
      quadraticProjection 10 (b - g) ∈ targetTwoSpace :=
    quadraticProjection_mem_targetTwoSpace_of_mem_targetAmbient hdifference
  have hbData := (E2.mem_quadraticEnvelopeState_iff
    (defectCapacitySpan (presentationDefect p)) b).1 hb
  have hbQ : quadraticQuotientProjection (quadraticProjection 10 b) ∈
      presentationDefect p := by
    rw [← intrinsicCapacityProjection_range p hdec]
    exact ⟨⟨quadraticProjection 10 b, hbData.2⟩, rfl⟩
  have hquotientEq :
      quadraticQuotientProjection (quadraticProjection 10 b) =
        quadraticQuotientProjection (quadraticProjection 10 g) := by
    apply (Submodule.Quotient.eq targetTwoSpace).2
    simpa using hprojectionTarget
  have hgQ : quadraticQuotientProjection (quadraticProjection 10 g) ∈
      presentationDefect p := by
    rw [← hquotientEq]
    exact hbQ
  exact (retainedQuadraticProduct_projection_not_mem p hu hv
    hquadratic hretained) (by simpa [g] using hgQ)

/-- Manuscript Lemma 9.2, restart clause.  A retained quadratic defect birth
from an intrinsic capacity state can be replaced by the intrinsic state of
the presentation obtained by appending that very gate.  The new state
contains the post-gate state and has exactly the same quotient-defect rank.

The preceding theorem derives the exact birth rank internally, so the restart
requires no extra circuit or presentation hypothesis beyond retention and
quadraticity. -/
theorem quadraticDefectBirth_intrinsicCapacityRestart
    {j : Nat} (p : Fin j → TwoForm)
    (hdec : ∀ i, IsDecomposableTwo (p i))
    {u v : ANF 10}
    (hu : u ∈ intrinsicCapacityState p)
    (hv : v ∈ intrinsicCapacityState p)
    (hquadratic : u * v ∈ N4.quadraticANFSpace 10)
    (hretained : u * v ∉ intrinsicCapacityState p) :
    let p' := Fin.snoc p (quadraticProjection 10 (u * v))
    (∀ i, IsDecomposableTwo (p' i)) ∧
      andExtend (intrinsicCapacityState p) u v ≤
        intrinsicCapacityState p' ∧
      N4.flagDefectRank
          (andExtend (intrinsicCapacityState p) u v) (mulTarget 5) =
        N4.flagDefectRank (intrinsicCapacityState p') (mulTarget 5) := by
  let g₂ := quadraticProjection 10 (u * v)
  let p' : Fin (j + 1) → TwoForm := Fin.snoc p g₂
  have hg₂dec : IsDecomposableTwo g₂ := by
    exact retainedQuadraticProduct_decomposable p hu hv hquadratic hretained
  have hp'dec : ∀ i, IsDecomposableTwo (p' i) := by
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa [p', g₂] using hg₂dec
    · simpa [p'] using hdec k
  have hQle : presentationDefect p ≤ presentationDefect p' := by
    change presentationDefect p ≤ presentationDefect (Fin.snoc p g₂)
    rw [presentationDefect_snoc]
    exact le_sup_left
  have hbaseLe : intrinsicCapacityState p ≤ intrinsicCapacityState p' := by
    apply E2.quadraticEnvelopeState_mono
    exact defectCapacitySpan_mono hQle
  have hg₂Capacity : g₂ ∈ defectCapacitySpan (presentationDefect p') := by
    rw [defectCapacitySpan_eq_geometricCapacitySpan]
    have hlast := decomposable_mem_geometricCapacitySpan p' hp'dec (Fin.last j)
    simpa [p', g₂] using hlast
  have hproductNew : u * v ∈ intrinsicCapacityState p' := by
    apply (E2.mem_quadraticEnvelopeState_iff
      (defectCapacitySpan (presentationDefect p')) (u * v)).2
    exact ⟨hquadratic, hg₂Capacity⟩
  have hextendLe : andExtend (intrinsicCapacityState p) u v ≤
      intrinsicCapacityState p' := by
    unfold andExtend
    apply sup_le hbaseLe
    rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hproductNew
  have hg₂notQ : quadraticQuotientProjection g₂ ∉
      presentationDefect p := by
    exact retainedQuadraticProduct_projection_not_mem p hu hv
      hquadratic hretained
  have hQrank : Module.finrank F₂ (presentationDefect p') =
      Module.finrank F₂ (presentationDefect p) + 1 := by
    change Module.finrank F₂ (presentationDefect (Fin.snoc p g₂)) =
      Module.finrank F₂ (presentationDefect p) + 1
    rw [presentationDefect_snoc,
      Submodule.finrank_sup_span_singleton hg₂notQ]
  have holdRank := intrinsicCapacityState_defectRank p hdec
  have hnewRank := intrinsicCapacityState_defectRank p' hp'dec
  have hbirth := retainedQuadraticProduct_defectBirth p hdec hu hv
    hquadratic hretained
  refine ⟨hp'dec, hextendLe, ?_⟩
  rw [hnewRank, hQrank, ← holdRank]
  exact hbirth

/-- Operational cost-preserving restart.  After the retained quadratic birth
has been replaced by its appended intrinsic capacity state, the remaining
suffix can again be replayed gate by gate, deleting every newly redundant
product and retaining the exact dimension growth of the surviving gates. -/
theorem CostedDefectLegalSuffix.prune_after_quadraticDefectBirth
    {j k : Nat} (p : Fin j → TwoForm)
    (hdec : ∀ i, IsDecomposableTwo (p i))
    {u v : ANF 10}
    (hu : u ∈ intrinsicCapacityState p)
    (hv : v ∈ intrinsicCapacityState p)
    (hquadratic : u * v ∈ N4.quadraticANFSpace 10)
    (hretained : u * v ∉ intrinsicCapacityState p)
    {V : Submodule F₂ (ANF 10)}
    (hreach : CostedDefectLegalSuffix
      (andExtend (intrinsicCapacityState p) u v) k V) :
    let p' := Fin.snoc (α := TwoForm) p
      (quadraticProjection 10 (u * v))
    ∃ k' ≤ k,
      CostedDefectLegalSuffix (intrinsicCapacityState p') k'
        (intrinsicCapacityState p' ⊔ V) ∧
      Module.finrank F₂ (intrinsicCapacityState p' ⊔ V) =
        Module.finrank F₂ (intrinsicCapacityState p') + k' := by
  let p' : Fin (j + 1) → TwoForm :=
    Fin.snoc p (quadraticProjection 10 (u * v))
  have hrestart := quadraticDefectBirth_intrinsicCapacityRestart
    p hdec hu hv hquadratic hretained
  have hpostDef : N4.flagDefectRank
      (andExtend (intrinsicCapacityState p) u v) (mulTarget 5) ≤ 3 :=
    (flagDefectRank_mono hreach.start_le).trans
      hreach.final_defect_le_three
  have hnewDef : N4.flagDefectRank (intrinsicCapacityState p')
      (mulTarget 5) ≤ 3 := by
    rw [← hrestart.2.2]
    exact hpostDef
  rcases hreach.prune_simulate_from_equal_defect
      hrestart.2.1 hrestart.2.2 hnewDef with
    ⟨k', hk', hreplay, hdim⟩
  exact ⟨k', hk', hreplay, hdim⟩

end
end N5
end UnrestrictedBooleanMul
