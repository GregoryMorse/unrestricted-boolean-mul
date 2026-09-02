import UnrestrictedBooleanMul.N5.QuadraticPrefixExact
import UnrestrictedBooleanMul.N5.FirstOrderState

/-!
# Low-defect quadratic prefixes enter the first-order envelope

The closed-place relation calculation already proves that the target part of
every capacity space of defect at most one lies in the codimension-one
first-order envelope.  This file transfers that coordinate statement to an
actual all-quadratic circuit prefix.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The target part of a flattened all-quadratic prefix of coordinate defect
at most one lies in the first-order ANF envelope. -/
theorem allQuadraticPrefix_target_le_firstOrder_of_presentationDefect_le_one
    {r j : Nat} (C : Circuit 10 r)
    (hflat : QuadraticPrefixFlattening C j)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10)
    (hdef : Module.finrank F₂ (presentationDefect hflat.generator) ≤ 1) :
    N4.circuitFlag C j ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState := by
  let Q := presentationDefect hflat.generator
  have himage : quadraticPrefixImage C j ≤ defectCapacitySpan Q := by
    rw [← hflat.span_eq, defectCapacitySpan_eq_geometricCapacitySpan]
    exact decomposablePresentationSpan_le_geometricCapacitySpan
      hflat.generator hflat.decomposable
  have htarget : targetTwoSpace ⊓ defectCapacitySpan Q ≤
      firstOrderEnvelopeTwoSpace :=
    targetCapacitySpace_le_firstOrderEnvelope_of_finrank_le_one Q hdef
  rintro p ⟨hpV, hpA⟩
  have hpquad : p ∈ N4.quadraticANFSpace 10 :=
    N4.wireSpace_le_quadratic_of_prefix C.gate hall hpV
  have hpProjectionTarget : quadraticProjection 10 p ∈ targetTwoSpace :=
    quadraticProjection_mem_targetTwoSpace_of_mem_targetAmbient hpA
  have hpProjectionImage : quadraticProjection 10 p ∈ quadraticPrefixImage C j :=
    ⟨p, hpV, rfl⟩
  have hpProjectionEnvelope : quadraticProjection 10 p ∈
      firstOrderEnvelopeTwoSpace :=
    htarget ⟨hpProjectionTarget, himage hpProjectionImage⟩
  change p ∈ E2.quadraticEnvelopeState firstOrderEnvelopeTwoSpace
  exact (E2.mem_quadraticEnvelopeState_iff
    firstOrderEnvelopeTwoSpace p).2 ⟨hpquad, hpProjectionEnvelope⟩

/-- Semantic form: flag defect at most one is exactly enough to invoke the
first-order base-envelope theorem. -/
theorem allQuadraticPrefix_target_le_firstOrder_of_flagDefect_le_one
    {r j : Nat} (C : Circuit 10 r)
    (hflat : QuadraticPrefixFlattening C j)
    (hall : ∀ i : Fin r, i.val < j →
      C.gate i ∈ N4.quadraticANFSpace 10)
    (hdef : N4.flagDefectRank (N4.circuitFlag C j) (mulTarget 5) ≤ 1) :
    N4.circuitFlag C j ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState := by
  apply allQuadraticPrefix_target_le_firstOrder_of_presentationDefect_le_one
    C hflat hall
  rw [quadraticPrefixFlattening_defect_eq_flagDefect C hflat hall]
  exact hdef

end
end N5
end UnrestrictedBooleanMul
