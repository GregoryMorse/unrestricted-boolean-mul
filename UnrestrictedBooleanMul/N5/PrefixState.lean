import UnrestrictedBooleanMul.N5.QuadraticFlattening
import Mathlib.Data.Nat.Find

/-!
# The last quadratic prefix

This module chooses the last all-quadratic state of a circuit and proves the
defect-birth facts used by the suffix analysis.  In a nonredundant circuit
with at most twelve gates computing `Mul 5`, the final defect is at most
three, the circuit is not entirely quadratic, and its first high gate raises
defect by one.  Consequently the last quadratic prefix has defect at most
two.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- A prefix whose preceding gate outputs all have algebraic degree at most
two. -/
def AllQuadraticPrefix {r : Nat} (C : Circuit 10 r) (j : Nat) : Prop :=
  ∀ i : Fin r, i.val < j → C.gate i ∈ N4.quadraticANFSpace 10

/-- The greatest all-quadratic prefix length. -/
noncomputable def lastQuadraticPrefix {r : Nat} (C : Circuit 10 r) : Nat := by
  classical
  exact Nat.findGreatest (AllQuadraticPrefix C) r

theorem lastQuadraticPrefix_le {r : Nat} (C : Circuit 10 r) :
    lastQuadraticPrefix C ≤ r := by
  classical
  exact Nat.findGreatest_le r

theorem allQuadraticPrefix_last {r : Nat} (C : Circuit 10 r) :
    AllQuadraticPrefix C (lastQuadraticPrefix C) := by
  classical
  apply Nat.findGreatest_spec (m := 0) (n := r) (Nat.zero_le _)
  intro i hi
  omega

/-- If the maximal prefix is proper, its next gate is genuinely high. -/
theorem gate_lastQuadraticPrefix_not_quadratic {r : Nat}
    (C : Circuit 10 r) (hlast : lastQuadraticPrefix C < r) :
    C.gate ⟨lastQuadraticPrefix C, hlast⟩ ∉
      N4.quadraticANFSpace 10 := by
  classical
  intro hnext
  have hnot : ¬AllQuadraticPrefix C (lastQuadraticPrefix C + 1) :=
    Nat.findGreatest_is_greatest
      (P := AllQuadraticPrefix C) (n := r)
      (Nat.lt_succ_self _) (Nat.succ_le_of_lt hlast)
  apply hnot
  intro i hi
  by_cases hilt : i.val < lastQuadraticPrefix C
  · exact allQuadraticPrefix_last C i hilt
  · have hieq : i.val = lastQuadraticPrefix C := by omega
    have hiFin : i = ⟨lastQuadraticPrefix C, hlast⟩ := Fin.ext hieq
    simpa [hiFin] using hnext

/-! ## Five-term target dimensions -/

/-- The affine and five-term target subspaces meet trivially. -/
theorem affine_disjoint_mulTarget_five :
    Disjoint (affine 10) (mulTarget 5) := by
  rw [disjoint_iff_inf_le]
  intro p hp
  rcases exists_targetCoeff_of_mem_mulTarget hp.2 with ⟨c, hc⟩
  have hprojAffine : fiveTargetProjection p = 0 := by
    rw [← LinearMap.mem_ker]
    exact fiveTargetProjection_kills_affine hp.1
  have hprojTarget : fiveTargetProjection (targetANF c) = c := by
    calc
      fiveTargetProjection (targetANF c) =
          anchorRestriction (quadraticProjection 10 (targetANF c)) :=
        (anchorRestriction_quadraticProjection (targetANF c)).symm
      _ = anchorRestriction (targetTwo c) := by
        rw [quadraticProjection_targetANF]
      _ = c := anchorRestriction_targetTwo c
  have hc0 : c = 0 := by
    rw [hc] at hprojTarget
    exact hprojTarget.symm.trans hprojAffine
  rw [← hc, hc0]
  simp [targetANF]

/-- The target ambient has affine dimension plus nine. -/
theorem targetAmbient_five_finrank :
    Module.finrank F₂ (N4.targetAmbient 10 (mulTarget 5)) =
      Module.finrank F₂ (affine 10) + 9 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (affine 10) (mulTarget 5)
  rw [affine_disjoint_mulTarget_five.eq_bot, finrank_bot,
    add_zero, mulTarget_five_finrank] at hdim
  unfold N4.targetAmbient
  omega

/-- A circuit computing all outputs has final target rank nine. -/
theorem final_target_rank_five {r : Nat} (C : Circuit 10 r)
    (hC : C.Computes (Mul 5)) :
    N4.flagTargetRank C.finalWire (mulTarget 5) = 9 := by
  have hamb : N4.targetAmbient 10 (mulTarget 5) ≤ C.finalWire := by
    apply sup_le
    · simpa [Circuit.finalWire] using
        affine_le_wireSpace C.gate (j := r)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hC i
  have hinf : C.finalWire ⊓ N4.targetAmbient 10 (mulTarget 5) =
      N4.targetAmbient 10 (mulTarget 5) := inf_eq_right.mpr hamb
  unfold N4.flagTargetRank
  rw [hinf, targetAmbient_five_finrank]
  omega

/-- The final defect of an `r`-gate circuit computing `Mul 5` is at most
`r - 9`, without a nonredundancy assumption. -/
theorem final_defect_le_sub_nine {r : Nat} (C : Circuit 10 r)
    (hC : C.Computes (Mul 5)) :
    N4.flagDefectRank C.finalWire (mulTarget 5) ≤ r - 9 := by
  have hledger := N4.flag_rank_ledger
    (V := C.finalWire) (T := mulTarget 5)
    (by simpa [Circuit.finalWire] using
      affine_le_wireSpace C.gate (j := r))
  have ht := final_target_rank_five C hC
  have hdim := N4.finalWire_finrank_le_affine_add C
  rw [ht] at hledger
  omega

theorem final_defect_le_three {r : Nat} (C : Circuit 10 r)
    (hC : C.Computes (Mul 5)) (hr : r ≤ 12) :
    N4.flagDefectRank C.finalWire (mulTarget 5) ≤ 3 := by
  have h := final_defect_le_sub_nine C hC
  omega

/-! ## Defect as a quotient image -/

/-- Image of a wire state in the quotient by `Aff + T`. -/
def stateDefectImage (V : Submodule F₂ (ANF 10)) :
    Submodule F₂ ((ANF 10) ⧸ N4.targetAmbient 10 (mulTarget 5)) :=
  Submodule.map (Submodule.mkQ (N4.targetAmbient 10 (mulTarget 5))) V

/-- Quotient-image dimension is exactly the flag defect. -/
theorem stateDefectImage_finrank (V : Submodule F₂ (ANF 10)) :
    Module.finrank F₂ (stateDefectImage V) =
      N4.flagDefectRank V (mulTarget 5) := by
  let A := N4.targetAmbient 10 (mulTarget 5)
  let f : V →ₗ[F₂] (ANF 10 ⧸ A) := (Submodule.mkQ A).domRestrict V
  have hrange : LinearMap.range f = stateDefectImage V := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker f = A.comap V.subtype := by
    ext x
    simp [f, Submodule.Quotient.mk_eq_zero]
  let e : ↥(A.comap V.subtype) ≃ₗ[F₂] ↥(V ⊓ A) := {
    toFun x := ⟨x.1.1, x.1.2, x.2⟩
    invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  have hkerRank : Module.finrank F₂ (LinearMap.ker f) =
      Module.finrank F₂ ↑(V ⊓ A) := by
    rw [hker]
    exact e.finrank_eq
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange, hkerRank] at hrank
  change Module.finrank F₂ (stateDefectImage V) +
      Module.finrank F₂ ↑(V ⊓ A) = Module.finrank F₂ V at hrank
  have hinfLe : Module.finrank F₂ ↑(V ⊓ A) ≤ Module.finrank F₂ V :=
    Submodule.finrank_mono inf_le_left
  unfold N4.flagDefectRank
  change Module.finrank F₂ (stateDefectImage V) =
    Module.finrank F₂ V - Module.finrank F₂ ↑(V ⊓ A)
  omega

/-- Defect is monotone along inclusions of wire states. -/
theorem flagDefectRank_mono {V W : Submodule F₂ (ANF 10)}
    (hVW : V ≤ W) :
    N4.flagDefectRank V (mulTarget 5) ≤
      N4.flagDefectRank W (mulTarget 5) := by
  rw [← stateDefectImage_finrank, ← stateDefectImage_finrank]
  apply Submodule.finrank_mono
  exact Submodule.map_mono hVW

/-! ## The first high gate is a defect birth -/

theorem degreeLE_one_X_ten (i : Fin 10) : N4.DegreeLE 1 (X i) := by
  intro s hs
  rw [X, coeff_monomial]
  split
  · rename_i h
    have hc := congrArg Finset.card h
    simp at hc
    omega
  · rfl

/-- The five-term target ambient consists entirely of degree-at-most-two
ANFs. -/
theorem targetAmbient_five_le_quadraticANFSpace :
    N4.targetAmbient 10 (mulTarget 5) ≤ N4.quadraticANFSpace 10 := by
  apply sup_le N4.affine_le_quadraticANFSpace
  rw [mulTarget, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  rw [Mul, mulCoefficient]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  split
  · exact (degreeLE_one_X_ten (aCoord i)).mul
      (degreeLE_one_X_ten (bCoord j))
  · exact Submodule.zero_mem _

/-- Dimension-polymorphic first-high intersection lemma, specialized to the
ten-variable state used here. -/
theorem inf_unchanged_of_first_high_ten
    (V A : Submodule F₂ (ANF 10)) (g : ANF 10)
    (hV : V ≤ N4.quadraticANFSpace 10)
    (hA : A ≤ N4.quadraticANFSpace 10)
    (hg : g ∉ N4.quadraticANFSpace 10) :
    (V ⊔ Submodule.span F₂ {g}) ⊓ A = V ⊓ A := by
  apply le_antisymm
  · rintro p ⟨hpVA, hpA⟩
    rcases Submodule.mem_sup.mp hpVA with ⟨v, hv, w, hw, rfl⟩
    rcases Submodule.mem_span_singleton.mp hw with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with ha | ha
    · subst a
      exact ⟨by simpa using hv, hpA⟩
    · subst a
      exfalso
      apply hg
      have hvlow := hV hv
      have hsumlow : v + g ∈ N4.quadraticANFSpace 10 := by
        apply hA
        simpa using hpA
      have hcancel := (N4.quadraticANFSpace 10).add_mem hsumlow hvlow
      have heq : (v + g) + v = g := by
        calc
          (v + g) + v = (v + v) + g := by ac_rfl
          _ = g := by simp
      rwa [heq] at hcancel
  · exact inf_le_inf le_sup_left le_rfl

/-- A nonredundant first high gate raises defect by exactly one. -/
theorem firstHighGate_defect_succ {r : Nat} (C : Circuit 10 r)
    (i : Fin r)
    (hprev : ∀ k : Fin r, k.val < i.val →
      C.gate k ∈ N4.quadraticANFSpace 10)
    (hhigh : C.gate i ∉ N4.quadraticANFSpace 10)
    (hnr : N4.NonredundantAt C i) :
    N4.flagDefectRank (N4.circuitFlag C (i.val + 1)) (mulTarget 5) =
      N4.flagDefectRank (N4.circuitFlag C i.val) (mulTarget 5) + 1 := by
  have hV : wireSpace C.gate i.val ≤ N4.quadraticANFSpace 10 :=
    N4.wireSpace_le_quadratic_of_prefix C.gate hprev
  have hinf := inf_unchanged_of_first_high_ten
    (wireSpace C.gate i.val) (N4.targetAmbient 10 (mulTarget 5))
    (C.gate i) hV targetAmbient_five_le_quadraticANFSpace hhigh
  have hstep : wireSpace C.gate (i.val + 1) =
      wireSpace C.gate i.val ⊔ Submodule.span F₂ {C.gate i} := by
    simpa using N4.wireSpace_succ C.gate i.isLt
  have hdim : Module.finrank F₂
      ↑(wireSpace C.gate i.val ⊔ Submodule.span F₂ {C.gate i}) =
      Module.finrank F₂ (wireSpace C.gate i.val) + 1 := by
    rw [Submodule.finrank_sup_span_singleton]
    simpa [N4.NonredundantAt, N4.circuitFlag] using hnr
  have hinfLe : Module.finrank F₂
      ↑(wireSpace C.gate i.val ⊓ N4.targetAmbient 10 (mulTarget 5)) ≤
      Module.finrank F₂ (wireSpace C.gate i.val) :=
    Submodule.finrank_mono inf_le_left
  unfold N4.flagDefectRank N4.circuitFlag
  rw [hstep, hinf]
  omega

/-- No all-quadratic circuit with at most twelve gates computes `Mul 5`. -/
theorem no_all_quadratic_circuit_le_twelve {r : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) (hr : r ≤ 12)
    (hall : ∀ i : Fin r, C.gate i ∈ N4.quadraticANFSpace 10) : False := by
  let hflat := quadraticPrefixFlattening_of_all_quadratic C (le_refl r)
    (fun i _ => hall i)
  have hT : targetTwoSpace ≤
      decomposablePresentationSpan hflat.generator := by
    rw [hflat.span_eq]
    exact targetTwoSpace_le_quadraticPrefixImage_final C hC
  rcases capacity_obstruction hflat.generator hflat.decomposable hT with
    ⟨hQ, hcap⟩
  have hQ3 : Module.finrank F₂ (presentationDefect hflat.generator) ≤ 3 := by
    omega
  have hbound := targetCapacity_le_seven_of_finrank_le_three
    (presentationDefect hflat.generator) hQ3
  omega

/-- In the relevant nonredundant circuit, the last quadratic prefix has
defect `0`, `1`, or `2`. -/
theorem lastQuadraticPrefix_defect_le_two {r : Nat}
    (C : Circuit 10 r) (hC : C.Computes (Mul 5)) (hr : r ≤ 12)
    (hnr : ∀ i : Fin r, N4.NonredundantAt C i) :
    N4.flagDefectRank
      (N4.circuitFlag C (lastQuadraticPrefix C)) (mulTarget 5) ≤ 2 := by
  have hproper : lastQuadraticPrefix C < r := by
    by_contra hnot
    have heq : lastQuadraticPrefix C = r := by
      exact Nat.le_antisymm (lastQuadraticPrefix_le C) (Nat.le_of_not_gt hnot)
    apply no_all_quadratic_circuit_le_twelve C hC hr
    intro i
    exact allQuadraticPrefix_last C i (by simpa [heq] using i.isLt)
  let i : Fin r := ⟨lastQuadraticPrefix C, hproper⟩
  have hbirth := firstHighGate_defect_succ C i
    (fun k hk => allQuadraticPrefix_last C k hk)
    (gate_lastQuadraticPrefix_not_quadratic C hproper) (hnr i)
  have hmono : N4.flagDefectRank
      (N4.circuitFlag C (i.val + 1)) (mulTarget 5) ≤
      N4.flagDefectRank C.finalWire (mulTarget 5) := by
    apply flagDefectRank_mono
    change wireSpace C.gate (i.val + 1) ≤ wireSpace C.gate r
    exact N4.wireSpace_mono (Nat.succ_le_of_lt hproper)
  have hfinal := final_defect_le_three C hC hr
  change N4.flagDefectRank
    (N4.circuitFlag C (lastQuadraticPrefix C)) (mulTarget 5) ≤ 2
  change N4.flagDefectRank
      (N4.circuitFlag C (lastQuadraticPrefix C + 1)) (mulTarget 5) =
        N4.flagDefectRank
          (N4.circuitFlag C (lastQuadraticPrefix C)) (mulTarget 5) + 1 at hbirth
  change N4.flagDefectRank
      (N4.circuitFlag C (lastQuadraticPrefix C + 1)) (mulTarget 5) ≤
        N4.flagDefectRank C.finalWire (mulTarget 5) at hmono
  exact by omega

end

end N5
end UnrestrictedBooleanMul
