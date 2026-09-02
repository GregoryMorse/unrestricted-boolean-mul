import UnrestrictedBooleanMul.N5.HighDefect
import UnrestrictedBooleanMul.N5.ColourNormalization

/-!
# Gate normal form with one high direction

When a wire state has at most one direction modulo the quadratic ANFs, choose
an actual representative `g` for it.  Every AND extension is then equal to
one generated either by two quadratic wires or by `g + x` times a quadratic
wire.  If both original factors carry `g`, Boolean idempotence replaces the
second factor by their sum without changing the generated wire space.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Joint normal form for one AND gate once a single high representative has
been selected. -/
theorem oneHigh_gate_normalForm
    (V : Submodule F₂ (ANF 10)) (g p q : ANF 10)
    (hgV : g ∈ V) (hpV : p ∈ V) (hqV : q ∈ V)
    (hnormal : ∀ z : ANF 10, z ∈ V →
      ∃ a : F₂, z + a • g ∈ N4.quadraticANFSpace 10) :
    ∃ x y : ANF 10,
      x ∈ V ⊓ N4.quadraticANFSpace 10 ∧
      y ∈ V ⊓ N4.quadraticANFSpace 10 ∧
      (andExtend V p q = andExtend V x y ∨
        andExtend V p q = andExtend V (g + x) y) := by
  rcases hnormal p hpV with ⟨a, hpa⟩
  rcases hnormal q hqV with ⟨b, hqb⟩
  rcases f2_eq_zero_or_one a with ha | ha <;>
    rcases f2_eq_zero_or_one b with hb | hb
  · have hpquad : p ∈ N4.quadraticANFSpace 10 := by
      simpa [ha] using hpa
    have hqquad : q ∈ N4.quadraticANFSpace 10 := by
      simpa [hb] using hqb
    exact ⟨p, q, ⟨hpV, hpquad⟩, ⟨hqV, hqquad⟩, Or.inl rfl⟩
  · let x := q + g
    have hxV : x ∈ V := V.add_mem hqV hgV
    have hxquad : x ∈ N4.quadraticANFSpace 10 := by
      simpa [x, hb] using hqb
    have hpquad : p ∈ N4.quadraticANFSpace 10 := by
      simpa [ha] using hpa
    have hgx : g + x = q := by
      calc
        g + x = (g + g) + q := by simp only [x]; ac_rfl
        _ = q := by rw [anf_add_self, zero_add]
    refine ⟨x, p, ⟨hxV, hxquad⟩, ⟨hpV, hpquad⟩, Or.inr ?_⟩
    rw [hgx]
    unfold andExtend
    rw [mul_comm]
  · let x := p + g
    have hxV : x ∈ V := V.add_mem hpV hgV
    have hxquad : x ∈ N4.quadraticANFSpace 10 := by
      simpa [x, ha] using hpa
    have hqquad : q ∈ N4.quadraticANFSpace 10 := by
      simpa [hb] using hqb
    have hgx : g + x = p := by
      calc
        g + x = (g + g) + p := by simp only [x]; ac_rfl
        _ = p := by rw [anf_add_self, zero_add]
    refine ⟨x, q, ⟨hxV, hxquad⟩, ⟨hqV, hqquad⟩, Or.inr ?_⟩
    rw [hgx]
  · let x := p + g
    let y := p + q
    have hxV : x ∈ V := V.add_mem hpV hgV
    have hyV : y ∈ V := V.add_mem hpV hqV
    have hxquad : x ∈ N4.quadraticANFSpace 10 := by
      simpa [x, ha] using hpa
    have hqgquad : q + g ∈ N4.quadraticANFSpace 10 := by
      simpa [hb] using hqb
    have hyquad : y ∈ N4.quadraticANFSpace 10 := by
      have hsum := (N4.quadraticANFSpace 10).add_mem hxquad hqgquad
      have heq : x + (q + g) = y := by
        calc
          x + (q + g) = (g + g) + (p + q) := by
            simp only [x]
            ac_rfl
          _ = y := by rw [anf_add_self, zero_add]
      rwa [heq] at hsum
    have hgx : g + x = p := by
      calc
        g + x = (g + g) + p := by simp only [x]; ac_rfl
        _ = p := by rw [anf_add_self, zero_add]
    refine ⟨x, y, ⟨hxV, hxquad⟩, ⟨hyV, hyquad⟩, Or.inr ?_⟩
    rw [hgx]
    exact (sup_span_mul_add_eq_sup_span_mul V p q hpV).symm

/-- Every gate at a legal suffix endpoint over a quadratic defect-two base
has the preceding low–low/high–low normal form for one jointly chosen `g`. -/
theorem DefectLegalSuffix.exists_oneHigh_gate_normalForms_of_defect_two
    {W V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix W V)
    (hWquad : W ≤ N4.quadraticANFSpace 10)
    (hWdef : N4.flagDefectRank W (mulTarget 5) = 2) :
    ∃ g : ANF 10, g ∈ V ∧
      ∀ p q : ANF 10, p ∈ V → q ∈ V →
        ∃ x y : ANF 10,
          x ∈ V ⊓ N4.quadraticANFSpace 10 ∧
          y ∈ V ⊓ N4.quadraticANFSpace 10 ∧
          (andExtend V p q = andExtend V x y ∨
            andExtend V p q = andExtend V (g + x) y) := by
  rcases hreach.exists_single_highRepresentative_of_defect_two
      hWquad hWdef with ⟨g, hgV, hnormal⟩
  refine ⟨g, hgV, ?_⟩
  intro p q hpV hqV
  exact oneHigh_gate_normalForm V g p q hgV hpV hqV hnormal

end
end N5
end UnrestrictedBooleanMul
