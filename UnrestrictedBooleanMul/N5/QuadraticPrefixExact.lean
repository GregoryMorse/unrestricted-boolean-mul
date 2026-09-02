import UnrestrictedBooleanMul.N5.QuadraticFlattening
import UnrestrictedBooleanMul.N5.E2.EnvelopeStates

/-!
# Exact coordinate model of an all-quadratic prefix

For an all-quadratic circuit prefix, projection to squarefree degree two loses
exactly the affine input space.  Thus its coordinate presentation defect is
equal to the semantic flag defect, not merely bounded by it.  The same
reconstruction gives a direct inclusion of the semantic state in any
coordinate envelope containing its projected span.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- An all-quadratic semantic prefix lies in the lift of every coordinate
space containing its quadratic image. -/
theorem circuitFlag_le_quadraticEnvelopeState_of_allQuadratic
    {r j : Nat} (C : Circuit 10 r)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10)
    (W : Submodule F₂ TwoForm)
    (himage : quadraticPrefixImage C j ≤ W) :
    N4.circuitFlag C j ≤ E2.quadraticEnvelopeState W := by
  intro p hp
  apply (E2.mem_quadraticEnvelopeState_iff W p).2
  constructor
  · exact N4.wireSpace_le_quadratic_of_prefix C.gate hall hp
  · exact himage ⟨p, hp, rfl⟩

/-- Quotient map from an all-quadratic semantic prefix to the quadratic
defect coordinates. -/
def quadraticPrefixDefectMap {r : Nat} (C : Circuit 10 r) (j : Nat) :
    N4.circuitFlag C j →ₗ[F₂] QuadraticQuotient :=
  quadraticQuotientProjection.comp
    ((quadraticProjection 10).domRestrict (N4.circuitFlag C j))

theorem quadraticPrefixDefectMap_range {r j : Nat}
    (C : Circuit 10 r) (hflat : QuadraticPrefixFlattening C j) :
    LinearMap.range (quadraticPrefixDefectMap C j) =
      presentationDefect hflat.generator := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    have hxImage : quadraticProjection 10 x.1 ∈ quadraticPrefixImage C j :=
      ⟨x.1, x.2, rfl⟩
    rw [← hflat.span_eq] at hxImage
    refine Submodule.span_induction (p := fun z _ =>
        quadraticQuotientProjection z ∈
          presentationDefect hflat.generator)
      ?_ ?_ ?_ ?_ hxImage
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · simp
    · intro u v _ _ hu hv
      simpa using (presentationDefect hflat.generator).add_mem hu hv
    · intro a u _ hu
      simpa using (presentationDefect hflat.generator).smul_mem a hu
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hiSpan : hflat.generator i ∈
        decomposablePresentationSpan hflat.generator :=
      Submodule.subset_span ⟨i, rfl⟩
    rw [hflat.span_eq] at hiSpan
    rcases hiSpan with ⟨x, hxV, hx⟩
    refine ⟨⟨x, hxV⟩, ?_⟩
    simpa [quadraticPrefixDefectMap] using
      congrArg quadraticQuotientProjection hx

/-- On an all-quadratic prefix, the kernel of the coordinate defect map is
exactly the pullback of `Aff + T`. -/
theorem quadraticPrefixDefectMap_ker {r j : Nat}
    (C : Circuit 10 r)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10) :
    LinearMap.ker (quadraticPrefixDefectMap C j) =
      (N4.targetAmbient 10 (mulTarget 5)).comap
        (N4.circuitFlag C j).subtype := by
  ext x
  constructor
  · intro hx
    have hprojection : quadraticProjection 10 x.1 ∈ targetTwoSpace := by
      apply (quadraticQuotientProjection_eq_zero_iff _).1
      exact LinearMap.mem_ker.mp hx
    have hxquad : x.1 ∈ N4.quadraticANFSpace 10 :=
      N4.wireSpace_le_quadratic_of_prefix C.gate hall x.2
    have hxEnvelope : x.1 ∈
        E2.quadraticEnvelopeState targetTwoSpace :=
      (E2.mem_quadraticEnvelopeState_iff targetTwoSpace x.1).2
        ⟨hxquad, hprojection⟩
    simpa [E2.quadraticEnvelopeState,
      E2.targetAmbient_eq_affine_sup_quadraticLift] using hxEnvelope
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply (quadraticQuotientProjection_eq_zero_iff _).2
    exact quadraticProjection_mem_targetTwoSpace_of_mem_targetAmbient hx

/-- For an all-quadratic prefix, the defect of its decomposable flattening is
exactly the semantic quotient defect of the circuit state. -/
theorem quadraticPrefixFlattening_defect_eq_flagDefect
    {r j : Nat} (C : Circuit 10 r)
    (hflat : QuadraticPrefixFlattening C j)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10) :
    Module.finrank F₂ (presentationDefect hflat.generator) =
      N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) := by
  let V := N4.circuitFlag C j
  let A := N4.targetAmbient 10 (mulTarget 5)
  let f := quadraticPrefixDefectMap C j
  have hrange : LinearMap.range f =
      presentationDefect hflat.generator :=
    quadraticPrefixDefectMap_range C hflat
  have hker : LinearMap.ker f = A.comap V.subtype := by
    exact quadraticPrefixDefectMap_ker C hall
  let e : ↥(A.comap V.subtype) ≃ₗ[F₂] ↥(V ⊓ A) := {
    toFun x := ⟨x.1.1, x.1.2, x.2⟩
    invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  have hkerRank : Module.finrank F₂ (LinearMap.ker f) =
      Module.finrank F₂ ↥(V ⊓ A) := by
    rw [hker]
    exact e.finrank_eq
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange, hkerRank] at hrank
  have hinterLe : Module.finrank F₂ ↥(V ⊓ A) ≤
      Module.finrank F₂ V := Submodule.finrank_mono inf_le_left
  unfold N4.flagDefectRank
  exact Nat.eq_sub_of_add_eq hrank

end
end N5
end UnrestrictedBooleanMul
