import UnrestrictedBooleanMul.N5.HighDefect

/-!
# Quadratic returns after a high birth

A defect-raising gate need not itself have quadratic output.  Its high class
may already be present, while subtracting an old representative exposes a new
quadratic wire.  This module records that exact alternative.  It is the
correct circuit-facing input to the low-defect fixed-block classification;
the pure-quadratic restart lemma does not cover this case.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Quadratic defect is monotone under enlargement of the wire state. -/
theorem stateQuadraticDefectRank_mono
    {V W : Submodule F₂ (ANF 10)} (hVW : V ≤ W) :
    stateQuadraticDefectRank V ≤ stateQuadraticDefectRank W := by
  unfold stateQuadraticDefectRank
  apply flagDefectRank_mono
  exact inf_le_inf hVW le_rfl

/-- If one gate raises total defect by one, exactly one of the two summands
in the quadratic/high splitting rises: either a new high colour is born or
the quadratic defect rises while high rank stays fixed. -/
theorem defectBirth_high_or_quadratic
    (V : Submodule F₂ (ANF 10)) (p q : ANF 10)
    (hbirth : N4.flagDefectRank (andExtend V p q) (mulTarget 5) =
      N4.flagDefectRank V (mulTarget 5) + 1) :
    (stateHighRank (andExtend V p q) = stateHighRank V + 1 ∧
      stateQuadraticDefectRank (andExtend V p q) =
        stateQuadraticDefectRank V) ∨
    (stateHighRank (andExtend V p q) = stateHighRank V ∧
      stateQuadraticDefectRank (andExtend V p q) =
        stateQuadraticDefectRank V + 1) := by
  have hquadMono : stateQuadraticDefectRank V ≤
      stateQuadraticDefectRank (andExtend V p q) :=
    stateQuadraticDefectRank_mono le_sup_left
  have hhighMono : stateHighRank V ≤
      stateHighRank (andExtend V p q) :=
    stateHighRank_mono le_sup_left
  have hold := flagDefectRank_eq_quadratic_add_high V
  have hnew := flagDefectRank_eq_quadratic_add_high (andExtend V p q)
  omega

/-- If adjoining a product does not raise high rank, its high quotient image
was already present in the old state. -/
theorem stateHighImage_andExtend_eq_of_stateHighRank_eq
    (V : Submodule F₂ (ANF 10)) (p q : ANF 10)
    (hhigh : stateHighRank (andExtend V p q) = stateHighRank V) :
    stateHighImage (andExtend V p q) = stateHighImage V := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.map_mono le_sup_left
  · rw [stateHighImage_finrank, stateHighImage_finrank, hhigh]

private theorem sup_span_add_old_eq
    (V : Submodule F₂ (ANF 10)) (g v : ANF 10) (hv : v ∈ V) :
    V ⊔ Submodule.span F₂ ({g + v} : Set (ANF 10)) =
      V ⊔ Submodule.span F₂ ({g} : Set (ANF 10)) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact Submodule.add_mem _
      ((le_sup_right : Submodule.span F₂ ({g} : Set (ANF 10)) ≤ _)
        (Submodule.mem_span_singleton_self g))
      ((le_sup_left : V ≤ _) hv)
  · apply sup_le le_sup_left
    rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    let U : Submodule F₂ (ANF 10) :=
      V ⊔ Submodule.span F₂ ({g + v} : Set (ANF 10))
    have hsum : (g + v) + v ∈ U :=
      Submodule.add_mem _
        ((le_sup_right : Submodule.span F₂ ({g + v} : Set (ANF 10)) ≤ _)
          (Submodule.mem_span_singleton_self (g + v)))
        ((le_sup_left : V ≤ _) hv)
    change g ∈ U
    simpa only [add_assoc, anf_add_self, add_zero] using hsum

/-- A retained gate whose high rank does not grow has a literal quadratic
correction: subtracting an old representative of the same high class gives a
new quadratic wire, and adjoining that correction gives exactly the same
wire state as adjoining the original product. -/
theorem exists_quadraticReturn_of_stateHighRank_eq
    (V : Submodule F₂ (ANF 10)) (p q : ANF 10)
    (hretained : p * q ∉ V)
    (hhigh : stateHighRank (andExtend V p q) = stateHighRank V) :
    ∃ v z : ANF 10,
      v ∈ V ∧
      z = p * q + v ∧
      z ∈ N4.quadraticANFSpace 10 ∧
      z ∉ V ∧
      andExtend V p q =
        V ⊔ Submodule.span F₂ ({z} : Set (ANF 10)) := by
  have hproductNext :
      Submodule.mkQ (N4.quadraticANFSpace 10) (p * q) ∈
        stateHighImage (andExtend V p q) :=
    ⟨p * q,
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self (p * q)),
      rfl⟩
  have hproductOld :
      Submodule.mkQ (N4.quadraticANFSpace 10) (p * q) ∈
        stateHighImage V := by
    rw [← stateHighImage_andExtend_eq_of_stateHighRank_eq V p q hhigh]
    exact hproductNext
  rcases hproductOld with ⟨v, hv, hvq⟩
  let z := p * q + v
  have hzquad : z ∈ N4.quadraticANFSpace 10 := by
    apply (Submodule.Quotient.mk_eq_zero
      (N4.quadraticANFSpace 10)).mp
    change Submodule.mkQ (N4.quadraticANFSpace 10) (p * q + v) = 0
    calc
      Submodule.mkQ (N4.quadraticANFSpace 10) (p * q + v) =
          Submodule.mkQ (N4.quadraticANFSpace 10) (p * q) +
            Submodule.mkQ (N4.quadraticANFSpace 10) v := by
              rw [map_add]
      _ = Submodule.mkQ (N4.quadraticANFSpace 10) v +
            Submodule.mkQ (N4.quadraticANFSpace 10) v := by rw [← hvq]
      _ = Submodule.mkQ (N4.quadraticANFSpace 10) (v + v) := by
            rw [map_add]
      _ = 0 := by rw [anf_add_self, map_zero]
  have hznew : z ∉ V := by
    intro hzV
    apply hretained
    have hsum := V.add_mem hzV hv
    simpa only [z, add_assoc, anf_add_self, add_zero] using hsum
  refine ⟨v, z, hv, rfl, hzquad, hznew, ?_⟩
  unfold andExtend
  exact (sup_span_add_old_eq V (p * q) v hv).symm

/-- Complete normal form for a retained defect birth.  The high-birth branch
is literal.  In the other branch an old high representative exposes the new
quadratic return, whose quadratic defect rises by exactly one. -/
theorem defectBirth_high_or_exists_quadraticReturn
    (V : Submodule F₂ (ANF 10)) (p q : ANF 10)
    (hretained : p * q ∉ V)
    (hbirth : N4.flagDefectRank (andExtend V p q) (mulTarget 5) =
      N4.flagDefectRank V (mulTarget 5) + 1) :
    (stateHighRank (andExtend V p q) = stateHighRank V + 1 ∧
      stateQuadraticDefectRank (andExtend V p q) =
        stateQuadraticDefectRank V) ∨
    ∃ v z : ANF 10,
      stateHighRank (andExtend V p q) = stateHighRank V ∧
      stateQuadraticDefectRank (andExtend V p q) =
        stateQuadraticDefectRank V + 1 ∧
      v ∈ V ∧
      z = p * q + v ∧
      z ∈ N4.quadraticANFSpace 10 ∧
      z ∉ V ∧
      andExtend V p q =
        V ⊔ Submodule.span F₂ ({z} : Set (ANF 10)) := by
  rcases defectBirth_high_or_quadratic V p q hbirth with hhigh | hquad
  · exact Or.inl hhigh
  · rcases exists_quadraticReturn_of_stateHighRank_eq
      V p q hretained hquad.1 with
      ⟨v, z, hv, hz, hzquad, hznew, hextend⟩
    exact Or.inr
      ⟨v, z, hquad.1, hquad.2, hv, hz, hzquad, hznew, hextend⟩

end
end N5
end UnrestrictedBooleanMul
