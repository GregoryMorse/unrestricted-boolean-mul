import UnrestrictedBooleanMul.N5.FirstOrderEscape
import UnrestrictedBooleanMul.N5.HighDefect

/-!
# Defect and high-colour budget at a target escape

If a newly adjoined product differs from an old wire by a target word, its
images both modulo the target ambient and modulo all quadratic ANFs were
already present.  Thus a target-producing step preserves both quotient
images exactly.  This is the algebraic form of the manuscript observation
that a first target escape is not a simultaneous defect birth.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Adjoining a vector whose image under a linear map is already represented
in the old state does not enlarge the mapped state. -/
theorem map_sup_span_singleton_eq_of_image_mem
    {E H : Type*} [AddCommGroup E] [Module F₂ E]
    [AddCommGroup H] [Module F₂ H]
    (f : E →ₗ[F₂] H) (V : Submodule F₂ E) (z : E)
    (hz : f z ∈ Submodule.map f V) :
    Submodule.map f (V ⊔ Submodule.span F₂ ({z} : Set E)) =
      Submodule.map f V := by
  apply le_antisymm
  · rw [Submodule.map_sup]
    apply sup_le le_rfl
    rw [Submodule.map_span, Submodule.span_le]
    rintro y ⟨x, rfl, rfl⟩
    exact hz
  · exact Submodule.map_mono le_sup_left

/-- A product equation with a target correction preserves the image modulo
`Aff + T`. -/
theorem stateDefectImage_andExtend_eq_of_target_add_old
    (V : Submodule F₂ (ANF 10)) (p q t v : ANF 10)
    (ht : t ∈ N4.targetAmbient 10 (mulTarget 5))
    (hv : v ∈ V) (heq : p * q = t + v) :
    stateDefectImage (andExtend V p q) = stateDefectImage V := by
  apply map_sup_span_singleton_eq_of_image_mem
  change Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) (p * q) ∈
    stateDefectImage V
  have htzero : Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5)) t = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ht
  rw [heq, map_add, htzero, zero_add]
  exact ⟨v, hv, rfl⟩

/-- A product equation with a target correction preserves the total quotient
defect exactly. -/
theorem flagDefectRank_andExtend_eq_of_target_add_old
    (V : Submodule F₂ (ANF 10)) (p q t v : ANF 10)
    (ht : t ∈ N4.targetAmbient 10 (mulTarget 5))
    (hv : v ∈ V) (heq : p * q = t + v) :
    N4.flagDefectRank (andExtend V p q) (mulTarget 5) =
      N4.flagDefectRank V (mulTarget 5) := by
  rw [← stateDefectImage_finrank, ← stateDefectImage_finrank,
    stateDefectImage_andExtend_eq_of_target_add_old V p q t v ht hv heq]

/-- The same target-correction equation preserves the literal high quotient
image modulo degree-at-most-two ANFs. -/
theorem stateHighImage_andExtend_eq_of_target_add_old
    (V : Submodule F₂ (ANF 10)) (p q t v : ANF 10)
    (ht : t ∈ N4.targetAmbient 10 (mulTarget 5))
    (hv : v ∈ V) (heq : p * q = t + v) :
    stateHighImage (andExtend V p q) = stateHighImage V := by
  apply map_sup_span_singleton_eq_of_image_mem
  change Submodule.mkQ (N4.quadraticANFSpace 10) (p * q) ∈
    stateHighImage V
  have htquad : t ∈ N4.quadraticANFSpace 10 :=
    targetAmbient_five_le_quadraticANFSpace ht
  have htzero : Submodule.mkQ (N4.quadraticANFSpace 10) t = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 htquad
  rw [heq, map_add, htzero, zero_add]
  exact ⟨v, hv, rfl⟩

/-- Pointwise form: the high class of a target-producing product was already
present before the target step. -/
theorem productHighClass_mem_stateHighImage_of_target_add_old
    (V : Submodule F₂ (ANF 10)) (p q t v : ANF 10)
    (ht : t ∈ N4.targetAmbient 10 (mulTarget 5))
    (hv : v ∈ V) (heq : p * q = t + v) :
    Submodule.mkQ (N4.quadraticANFSpace 10) (p * q) ∈
      stateHighImage V := by
  have htquad : t ∈ N4.quadraticANFSpace 10 :=
    targetAmbient_five_le_quadraticANFSpace ht
  have htzero : Submodule.mkQ (N4.quadraticANFSpace 10) t = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 htquad
  rw [heq, map_add, htzero, zero_add]
  exact ⟨v, hv, rfl⟩

/-- Consequently a target-producing step preserves the number of independent
high directions exactly. -/
theorem stateHighRank_andExtend_eq_of_target_add_old
    (V : Submodule F₂ (ANF 10)) (p q t v : ANF 10)
    (ht : t ∈ N4.targetAmbient 10 (mulTarget 5))
    (hv : v ∈ V) (heq : p * q = t + v) :
    stateHighRank (andExtend V p q) = stateHighRank V := by
  rw [← stateHighImage_finrank, ← stateHighImage_finrank,
    stateHighImage_andExtend_eq_of_target_add_old V p q t v ht hv heq]

/-- Since total defect and high rank are both preserved, the defect already
visible in the quadratic part is preserved as well. -/
theorem stateQuadraticDefectRank_andExtend_eq_of_target_add_old
    (V : Submodule F₂ (ANF 10)) (p q t v : ANF 10)
    (ht : t ∈ N4.targetAmbient 10 (mulTarget 5))
    (hv : v ∈ V) (heq : p * q = t + v) :
    stateQuadraticDefectRank (andExtend V p q) =
      stateQuadraticDefectRank V := by
  have htotal := flagDefectRank_andExtend_eq_of_target_add_old
    V p q t v ht hv heq
  have hhigh := stateHighRank_andExtend_eq_of_target_add_old
    V p q t v ht hv heq
  rw [flagDefectRank_eq_quadratic_add_high,
    flagDefectRank_eq_quadratic_add_high, hhigh] at htotal
  omega

/-- Any failing target-preservation step preserves both defect and high rank.
This version consumes only the first-escape hypotheses used by the induction
interface. -/
theorem targetStep_escape_preserves_quotient_budgets
    {V U : Submodule F₂ (ANF 10)} (p q : ANF 10)
    (hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤ U)
    (hescape : ¬ (andExtend V p q ⊓
      N4.targetAmbient 10 (mulTarget 5) ≤ U)) :
    N4.flagDefectRank (andExtend V p q) (mulTarget 5) =
        N4.flagDefectRank V (mulTarget 5) ∧
      stateHighRank (andExtend V p q) = stateHighRank V ∧
      stateQuadraticDefectRank (andExtend V p q) =
        stateQuadraticDefectRank V := by
  rcases exists_product_correction_of_targetStep_escape p q hold hescape with
    ⟨t, v, ht, _htU, hv, heq⟩
  exact ⟨flagDefectRank_andExtend_eq_of_target_add_old
      V p q t v ht hv heq,
    stateHighRank_andExtend_eq_of_target_add_old
      V p q t v ht hv heq,
    stateQuadraticDefectRank_andExtend_eq_of_target_add_old
      V p q t v ht hv heq⟩

end
end N5
end UnrestrictedBooleanMul
