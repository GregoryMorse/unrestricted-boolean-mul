import UnrestrictedBooleanMul.N5.FirstOrderQuadraticPart
import UnrestrictedBooleanMul.N5.RankOneCorrectionColour

/-!
# Birth of the unique high direction

If a suffix endpoint has the same quadratic part as its quadratic base and at
most one high direction, every nonquadratic old wire has the high class of an
actual product of two base wires.  The proof follows the suffix derivation to
the birth step.  One-dimensionality rules out an unrelated earlier high
class, so both factors at that step are quadratic.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- A unique high class above a fixed quadratic base is represented by a
low-low product from that base. -/
theorem exists_base_lowProduct_of_unique_highClass
    {A V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix A V)
    (hAquad : A ≤ N4.quadraticANFSpace 10)
    (hquad : stateQuadraticPart V = A)
    (hhigh : stateHighRank V ≤ 1)
    (g : ANF 10) (hgV : g ∈ V)
    (hgHigh : g ∉ N4.quadraticANFSpace 10) :
    ∃ p q : ANF 10,
      p ∈ A ∧ q ∈ A ∧
      Submodule.mkQ (N4.quadraticANFSpace 10) g =
        Submodule.mkQ (N4.quadraticANFSpace 10) (p * q) ∧
      p * q ∈ V := by
  induction hreach generalizing g with
  | refl _ =>
      exact (hgHigh (hAquad hgV)).elim
  | @step W hreach x y hxW hyW hdef ih =>
      let W' := andExtend W x y
      change g ∈ W' at hgV
      by_cases hgW : g ∈ W
      · have hquadW : stateQuadraticPart W = A := by
          apply le_antisymm
          · intro z hz
            have hz' : z ∈ stateQuadraticPart W' :=
              ⟨(le_sup_left : W ≤ W') hz.1, hz.2⟩
            rw [hquad] at hz'
            exact hz'
          · intro z hz
            exact ⟨hreach.start_le hz, hAquad hz⟩
        have hhighW : stateHighRank W ≤ 1 := by
          have himage : stateHighImage W ≤ stateHighImage W' :=
            Submodule.map_mono le_sup_left
          have hdim := Submodule.finrank_mono himage
          rw [stateHighImage_finrank, stateHighImage_finrank] at hdim
          exact hdim.trans (by simpa [W'] using hhigh)
        rcases ih hquadW hhighW g hgW hgHigh with
          ⟨p, q, hpA, hqA, hclass, hpqW⟩
        exact ⟨p, q, hpA, hqA, hclass,
          (le_sup_left : W ≤ W') hpqW⟩
      · have hWquad : W ≤ N4.quadraticANFSpace 10 := by
          intro z hzW
          by_contra hzHigh
          have hzW' : z ∈ W' := (le_sup_left : W ≤ W') hzW
          have hzLine := highClass_mem_span_of_stateHighRank_le_one
            W' g z hgV hzW' hgHigh hhigh
          rcases Submodule.mem_span_singleton.mp hzLine with ⟨a, ha⟩
          rcases f2_eq_zero_or_one a with rfl | rfl
          · simp at ha
            exact hzHigh ((Submodule.Quotient.mk_eq_zero _).1 ha.symm)
          · simp at ha
            have hgzQuad : g + z ∈ N4.quadraticANFSpace 10 := by
              apply (Submodule.Quotient.mk_eq_zero _).1
              change Submodule.mkQ (N4.quadraticANFSpace 10) (g + z) = 0
              rw [map_add]
              have ha' : Submodule.mkQ (N4.quadraticANFSpace 10) g =
                  Submodule.mkQ (N4.quadraticANFSpace 10) z := ha
              rw [ha']
              calc
                Submodule.mkQ (N4.quadraticANFSpace 10) z +
                    Submodule.mkQ (N4.quadraticANFSpace 10) z =
                  ((1 : F₂) + 1) •
                    Submodule.mkQ (N4.quadraticANFSpace 10) z := by
                      rw [add_smul, one_smul]
                _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
            have hgzA : g + z ∈ A := by
              rw [← hquad]
              exact ⟨W'.add_mem hgV hzW', hgzQuad⟩
            have hgW' : g ∈ W := by
              have hgzW : g + z ∈ W := hreach.start_le hgzA
              have : (g + z) + z ∈ W := W.add_mem hgzW hzW
              simpa only [add_assoc, anf_add_self, add_zero] using this
            exact hgW hgW'
        have hxA : x ∈ A := by
          have hxPart : x ∈ stateQuadraticPart W' :=
            ⟨(le_sup_left : W ≤ W') hxW, hWquad hxW⟩
          rwa [hquad] at hxPart
        have hyA : y ∈ A := by
          have hyPart : y ∈ stateQuadraticPart W' :=
            ⟨(le_sup_left : W ≤ W') hyW, hWquad hyW⟩
          rwa [hquad] at hyPart
        rcases Submodule.mem_sup.mp hgV with ⟨z, hzW, u, hu, hzu⟩
        rcases Submodule.mem_span_singleton.mp hu with ⟨a, rfl⟩
        rcases f2_eq_zero_or_one a with rfl | rfl
        · exfalso
          apply hgW
          have hzg : z = g := by simpa using hzu
          exact hzg ▸ hzW
        · refine ⟨x, y, hxA, hyA, ?_, ?_⟩
          have hzZero : Submodule.mkQ (N4.quadraticANFSpace 10) z = 0 :=
            (Submodule.Quotient.mk_eq_zero _).2 (hWquad hzW)
          have hEq : z + x * y = g := by simpa using hzu
          have hmap := congrArg
            (Submodule.mkQ (N4.quadraticANFSpace 10)) hEq
          · simpa [map_add, hzZero] using hmap.symm
          · exact (le_sup_right :
              Submodule.span F₂ ({x * y} : Set (ANF 10)) ≤ W')
              (Submodule.mem_span_singleton_self (x * y))

/-- Equal high classes of two old wires differ by a quadratic word; when the
quadratic part is fixed, that difference lies in the base itself. -/
theorem add_mem_base_of_equal_highClass_of_fixed_quadraticPart
    {A V : Submodule F₂ (ANF 10)}
    (hquad : stateQuadraticPart V = A)
    {v w : ANF 10} (hv : v ∈ V) (hw : w ∈ V)
    (hclass : Submodule.mkQ (N4.quadraticANFSpace 10) v =
      Submodule.mkQ (N4.quadraticANFSpace 10) w) :
    v + w ∈ A := by
  have hvwQuad : v + w ∈ N4.quadraticANFSpace 10 := by
    apply (Submodule.Quotient.mk_eq_zero _).1
    change Submodule.mkQ (N4.quadraticANFSpace 10) (v + w) = 0
    rw [map_add, hclass]
    calc
      Submodule.mkQ (N4.quadraticANFSpace 10) w +
          Submodule.mkQ (N4.quadraticANFSpace 10) w =
        ((1 : F₂) + 1) •
          Submodule.mkQ (N4.quadraticANFSpace 10) w := by
            rw [add_smul, one_smul]
      _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  have hvwPart : v + w ∈ stateQuadraticPart V :=
    ⟨V.add_mem hv hw, hvwQuad⟩
  rwa [hquad] at hvwPart

/-- Every old wire in the unique-high regime is one actual base low-product
plus a base quadratic correction. -/
theorem exists_base_lowProduct_add_base_of_highRank_le_one
    {A V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix A V)
    (hAquad : A ≤ N4.quadraticANFSpace 10)
    (hquad : stateQuadraticPart V = A)
    (hhigh : stateHighRank V ≤ 1)
    (v : ANF 10) (hv : v ∈ V) :
    ∃ p q w : ANF 10,
      p ∈ A ∧ q ∈ A ∧ w ∈ A ∧ p * q ∈ V ∧
      v = p * q + w := by
  by_cases hvQuad : v ∈ N4.quadraticANFSpace 10
  · have hvA : v ∈ A := by
      have : v ∈ stateQuadraticPart V := ⟨hv, hvQuad⟩
      rwa [hquad] at this
    exact ⟨0, 0, v, A.zero_mem, A.zero_mem, hvA, V.zero_mem, by simp⟩
  · rcases exists_base_lowProduct_of_unique_highClass
      hreach hAquad hquad hhigh v hv hvQuad with
      ⟨p, q, hpA, hqA, hclass, hpqV⟩
    let w := v + p * q
    have hwA : w ∈ A :=
      add_mem_base_of_equal_highClass_of_fixed_quadraticPart
        hquad hv hpqV hclass
    refine ⟨p, q, w, hpA, hqA, hwA, hpqV, ?_⟩
    change v = p * q + (v + p * q)
    symm
    calc
      p * q + (v + p * q) =
          v + (p * q + p * q) := by ac_rfl
      _ = v := by rw [anf_add_self, add_zero]

end
end N5
end UnrestrictedBooleanMul
