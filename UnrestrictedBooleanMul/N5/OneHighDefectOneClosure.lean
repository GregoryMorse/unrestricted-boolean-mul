import UnrestrictedBooleanMul.N5.ZeroColourExact
import UnrestrictedBooleanMul.N5.RankOneZeroQuadraticDefect
import UnrestrictedBooleanMul.N5.ColourCases
import UnrestrictedBooleanMul.N5.LowDefectPrefix
import UnrestrictedBooleanMul.N5.CircuitSuffix

/-!
# First-order closure after the unique high birth at total defect one

This is a cost-sensitive replacement for a small, valid part of the false
history-free saturation statement.  The base already contains one genuinely
high direction.  If total defect never exceeds one, high rank stays exactly
one and quadratic defect stays zero.  The checked zero-colour and rank-one
absorption theorems then exclude a first target escape, while rank-two factor
colours cannot fit in a one-dimensional high image.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private abbrev firstOrderZeroAnchor : Submodule F₂ (ANF 10) :=
  firstOrderAnchorState (0 : TwoForm)

private theorem firstOrderZeroAnchor_eq :
    firstOrderZeroAnchor = firstOrderEnvelopeState := by
  exact firstOrderAnchorState_eq_firstOrderEnvelope_of_mem_target
    0 decomposableTwo_zero (Submodule.zero_mem targetTwoSpace)

/-- Above a first-order state that already contains its unique high direction,
every suffix endpoint of total defect at most one remains in the eight-target
first-order envelope. -/
theorem oneHigh_defectOne_targetSubspace_closed
    (B : Submodule F₂ (ANF 10))
    (hbaseReach : DefectLegalSuffix firstOrderEnvelopeState B)
    (hbaseHigh : stateHighRank B = 1)
    (hbaseTarget : B ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState) :
    ∀ V, DefectLegalSuffix B V →
      N4.flagDefectRank V (mulTarget 5) ≤ 1 →
      V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
        firstOrderEnvelopeState := by
  intro V hreach
  induction hreach with
  | refl =>
      intro _hdef
      exact hbaseTarget
  | @step V hreach X Y hX hY hlegal ih =>
      intro hdefNext
      have hdefV : N4.flagDefectRank V (mulTarget 5) ≤ 1 :=
        (flagDefectRank_mono le_sup_left).trans hdefNext
      have hold : V ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
          firstOrderEnvelopeState := ih hdefV
      have hreachFromEnvelope :
          DefectLegalSuffix firstOrderEnvelopeState V :=
        hbaseReach.trans hreach
      have hhighLower : 1 ≤ stateHighRank V := by
        rw [← hbaseHigh]
        exact stateHighRank_mono hreach.start_le
      have hsplit := flagDefectRank_eq_quadratic_add_high V
      have hquadDefect : stateQuadraticDefectRank V = 0 := by omega
      have hhigh : stateHighRank V ≤ 1 := by omega
      have hanchorReach : DefectLegalSuffix firstOrderZeroAnchor V := by
        rw [firstOrderZeroAnchor_eq]
        exact hreachFromEnvelope
      have hanchorDefect : N4.flagDefectRank firstOrderZeroAnchor
          (mulTarget 5) = 0 := by
        rw [firstOrderZeroAnchor_eq, firstOrderEnvelopeState_defectRank]
      have hquadraticDefectEq : stateQuadraticDefectRank V =
          N4.flagDefectRank firstOrderZeroAnchor (mulTarget 5) := by
        rw [hquadDefect, hanchorDefect]
      have hquad : stateQuadraticPart V = firstOrderEnvelopeState := by
        have h := stateQuadraticPart_eq_firstOrderAnchor_of_equal_defect
          (V := V) (0 : TwoForm) hanchorReach hold hquadraticDefectEq
        simpa only [firstOrderZeroAnchor, firstOrderZeroAnchor_eq] using h
      rcases highQuotient_factor_trichotomy X Y with
        hzero | hone | htwo
      · exact zeroColour_step_closed_of_fixedFirstOrder_highRank_le_one
          V X Y hreachFromEnvelope hquad hhigh hX hY
            hzero.1 hzero.2 hold
      · rcases hone with ⟨g, hg, hpattern⟩
        have hclosed :=
          rankOne_step_closed_of_zero_quadraticDefect_highRank_le_one
            0 decomposableTwo_zero V X Y g hanchorReach hX hY hold
              hg hpattern hquadDefect hhigh
        simpa only [firstOrderZeroAnchor, firstOrderZeroAnchor_eq] using hclosed
      · have hXimage : Submodule.mkQ (N4.quadraticANFSpace 10) X ∈
            stateHighImage V := ⟨X, hX, rfl⟩
        have hYimage : Submodule.mkQ (N4.quadraticANFSpace 10) Y ∈
            stateHighImage V := ⟨Y, hY, rfl⟩
        have hspan : Submodule.span F₂
            (Set.range (pairDirections
              (Submodule.mkQ (N4.quadraticANFSpace 10) X)
              (Submodule.mkQ (N4.quadraticANFSpace 10) Y))) ≤
            stateHighImage V := by
          apply Submodule.span_le.mpr
          rintro z ⟨i, rfl⟩
          fin_cases i
          · exact hXimage
          · exact hYimage
        have hdim := Submodule.finrank_mono hspan
        rw [finrank_span_eq_card htwo, stateHighImage_finrank] at hdim
        norm_num at hdim
        omega

/-- A first genuinely high gate over a defect-zero last quadratic prefix,
followed by a tail of total defect at most one, cannot compute all nine target
coordinates.  This closes the entire final-defect-zero/one circuit regime. -/
theorem no_circuit_of_final_defect_le_one
    {r : Nat} (C : Circuit 10 r) (hC : C.Computes (Mul 5))
    (hr : r ≤ 12)
    (hfinalDefect : N4.flagDefectRank C.finalWire (mulTarget 5) ≤ 1) :
    False := by
  let j := lastQuadraticPrefix C
  have hj : j ≤ r := lastQuadraticPrefix_le C
  have hall : AllQuadraticPrefix C j := allQuadraticPrefix_last C
  have hproper : j < r := by
    by_contra hnot
    have hjr : j = r := Nat.le_antisymm hj (Nat.le_of_not_gt hnot)
    apply no_all_quadratic_circuit_le_twelve C hC hr
    intro i
    exact hall i (by omega)
  let i : Fin r := ⟨j, hproper⟩
  let W := N4.circuitFlag C j
  let X := C.left i
  let Y := C.right i
  let B := andExtend firstOrderEnvelopeState X Y
  have hgateHigh : X * Y ∉ N4.quadraticANFSpace 10 := by
    change C.left i * C.right i ∉ N4.quadraticANFSpace 10
    rw [← C.gate_eq i]
    change C.gate ⟨lastQuadraticPrefix C, hproper⟩ ∉
      N4.quadraticANFSpace 10
    exact gate_lastQuadraticPrefix_not_quadratic C hproper
  have hXW : X ∈ W := by
    simpa only [W, X, N4.circuitFlag, i] using C.left_mem i
  have hYW : Y ∈ W := by
    simpa only [W, Y, N4.circuitFlag, i] using C.right_mem i
  have hfirstBirth := firstHighGate_defect_succ C i
    (fun k hk => hall k hk)
    (gate_lastQuadraticPrefix_not_quadratic C hproper)
    (by
      intro hred
      apply gate_lastQuadraticPrefix_not_quadratic C hproper
      apply N4.wireSpace_le_quadratic_of_prefix C.gate hall
      simpa [N4.NonredundantAt, N4.circuitFlag, i] using hred)
  have hnextFinal : N4.flagDefectRank
      (N4.circuitFlag C (j + 1)) (mulTarget 5) ≤
      N4.flagDefectRank C.finalWire (mulTarget 5) := by
    apply flagDefectRank_mono
    change wireSpace C.gate (j + 1) ≤ wireSpace C.gate r
    exact N4.wireSpace_mono (Nat.succ_le_of_lt hproper)
  have hfirstBirth' : N4.flagDefectRank
      (N4.circuitFlag C (j + 1)) (mulTarget 5) =
      N4.flagDefectRank W (mulTarget 5) + 1 := by
    simpa only [i, W] using hfirstBirth
  have hWdefect : N4.flagDefectRank W (mulTarget 5) = 0 := by
    omega
  have hWquad : W ≤ N4.quadraticANFSpace 10 :=
    N4.wireSpace_le_quadratic_of_prefix C.gate hall
  have hWquadraticPart : stateQuadraticPart W = W := by
    exact inf_eq_left.mpr hWquad
  have hWquadraticDefect : stateQuadraticDefectRank W = 0 := by
    unfold stateQuadraticDefectRank
    rw [hWquadraticPart, hWdefect]
  have hWtarget : W ≤ N4.targetAmbient 10 (mulTarget 5) := by
    rw [← hWquadraticPart]
    exact stateQuadraticPart_le_targetAmbient_of_defectRank_eq_zero
      W hWquadraticDefect
  let hflat := quadraticPrefixFlattening_of_all_quadratic C hj hall
  have hWtargetEnvelope : W ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState :=
    allQuadraticPrefix_target_le_firstOrder_of_flagDefect_le_one
      C hflat hall (by rw [hWdefect]; omega)
  have hWEnvelope : W ≤ firstOrderEnvelopeState := by
    intro p hp
    exact hWtargetEnvelope ⟨hp, hWtarget hp⟩
  have hEnvelopeDefect : N4.flagDefectRank firstOrderEnvelopeState
      (mulTarget 5) = 0 := firstOrderEnvelopeState_defectRank
  have hsmallDefect : N4.flagDefectRank (andExtend W X Y)
      (mulTarget 5) = 1 := by
    have hwire : N4.circuitFlag C (j + 1) = andExtend W X Y := by
      change wireSpace C.gate (j + 1) =
        wireSpace C.gate j ⊔ Submodule.span F₂ ({X * Y} : Set (ANF 10))
      rw [show X * Y = C.gate i from (C.gate_eq i).symm]
      simpa only [i] using N4.wireSpace_succ C.gate hproper
    rw [← hwire]
    omega
  have hBdefect : N4.flagDefectRank B (mulTarget 5) = 1 := by
    have hsup := flagDefectRank_sup_eq_right_of_equal_base
      hWEnvelope (le_sup_left : W ≤ andExtend W X Y)
      (hWdefect.trans hEnvelopeDefect.symm)
    change N4.flagDefectRank
        (firstOrderEnvelopeState ⊔ andExtend W X Y) (mulTarget 5) =
      N4.flagDefectRank (andExtend W X Y) (mulTarget 5) at hsup
    have hBsup : B = firstOrderEnvelopeState ⊔ andExtend W X Y := by
      change firstOrderEnvelopeState ⊔
          Submodule.span F₂ ({X * Y} : Set (ANF 10)) =
        firstOrderEnvelopeState ⊔
          (W ⊔ Submodule.span F₂ ({X * Y} : Set (ANF 10)))
      rw [← sup_assoc, sup_eq_left.mpr hWEnvelope]
    rw [hBsup, hsup, hsmallDefect]
  have hbaseReach : DefectLegalSuffix firstOrderEnvelopeState B := by
    have hbase : N4.flagDefectRank firstOrderEnvelopeState
        (mulTarget 5) ≤ 3 := by omega
    have hnext : N4.flagDefectRank
        (andExtend firstOrderEnvelopeState X Y) (mulTarget 5) ≤ 3 := by
      simpa only [B] using hBdefect.le.trans (by omega)
    exact .step (.refl hbase) X Y (hWEnvelope hXW) (hWEnvelope hYW) hnext
  have hgateB : X * Y ∈ B :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hBhighPositive : 1 ≤ stateHighRank B := by
    by_contra hnot
    have hzero : stateHighRank B = 0 := by omega
    have himageRank : Module.finrank F₂ (stateHighImage B) = 0 := by
      rw [stateHighImage_finrank, hzero]
    have himageBot : stateHighImage B = ⊥ :=
      Submodule.finrank_eq_zero.mp himageRank
    exact hgateHigh ((stateHighImage_eq_bot_iff B).mp himageBot hgateB)
  have hBsplit := flagDefectRank_eq_quadratic_add_high B
  have hBhigh : stateHighRank B = 1 := by omega
  have hBtarget : B ⊓ N4.targetAmbient 10 (mulTarget 5) ≤
      firstOrderEnvelopeState := by
    rintro z ⟨hzB, hzTarget⟩
    change z ∈ firstOrderEnvelopeState ⊔
      Submodule.span F₂ ({X * Y} : Set (ANF 10)) at hzB
    rcases Submodule.mem_sup.mp hzB with ⟨u, hu, v, hv, rfl⟩
    rcases Submodule.mem_span_singleton.mp hv with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with rfl | rfl
    · simpa using hu
    · exfalso
      apply hgateHigh
      have hsumQuad : u + X * Y ∈ N4.quadraticANFSpace 10 :=
        targetAmbient_five_le_quadraticANFSpace (by simpa using hzTarget)
      have huQuad : u ∈ N4.quadraticANFSpace 10 :=
        E2.quadraticEnvelopeState_le_quadraticANFSpace
          firstOrderEnvelopeTwoSpace hu
      have hcancel := (N4.quadraticANFSpace 10).add_mem hsumQuad huQuad
      have heq : (u + X * Y) + u = X * Y := by
        calc
          (u + X * Y) + u = (u + u) + X * Y := by ac_rfl
          _ = X * Y := by simp
      rwa [heq] at hcancel
  have hsmallLeB : andExtend W X Y ≤ B := by
    exact sup_le_sup hWEnvelope le_rfl
  have hsmallLeFinal : andExtend W X Y ≤ C.finalWire := by
    have hwire : andExtend W X Y = N4.circuitFlag C (j + 1) := by
      change wireSpace C.gate j ⊔
          Submodule.span F₂ ({X * Y} : Set (ANF 10)) =
        wireSpace C.gate (j + 1)
      rw [show X * Y = C.gate i from (C.gate_eq i).symm]
      exact (N4.wireSpace_succ C.gate hproper).symm
    rw [hwire]
    change wireSpace C.gate (j + 1) ≤ wireSpace C.gate r
    exact N4.wireSpace_mono (Nat.succ_le_of_lt hproper)
  have htail : DefectLegalSuffix (andExtend W X Y) C.finalWire := by
    have hflag := circuitFlag_defectLegalSuffix C
      (j := j + 1) (k := r) (Nat.succ_le_of_lt hproper) (le_refl r)
      (fun l _hjl hlr => by
        have hle : N4.flagDefectRank (N4.circuitFlag C l)
            (mulTarget 5) ≤ 1 :=
          (flagDefectRank_mono (N4.wireSpace_mono hlr)).trans (by
            simpa [N4.circuitFlag, Circuit.finalWire] using hfinalDefect)
        omega)
    have hwire : N4.circuitFlag C (j + 1) = andExtend W X Y := by
      change wireSpace C.gate (j + 1) =
        wireSpace C.gate j ⊔ Submodule.span F₂ ({X * Y} : Set (ANF 10))
      rw [show X * Y = C.gate i from (C.gate_eq i).symm]
      simpa only [i] using N4.wireSpace_succ C.gate hproper
    rwa [hwire] at hflag
  have hsim : DefectLegalSuffix B (B ⊔ C.finalWire) :=
    htail.simulate_from_equal_defect hsmallLeB
      (hsmallDefect.trans hBdefect.symm) (by omega)
  have hsimDefect : N4.flagDefectRank (B ⊔ C.finalWire)
      (mulTarget 5) ≤ 1 := by
    rw [flagDefectRank_sup_eq_right_of_equal_base hsmallLeB
      hsmallLeFinal (hsmallDefect.trans hBdefect.symm)]
    exact hfinalDefect
  have hclosed := oneHigh_defectOne_targetSubspace_closed
    B hbaseReach hBhigh hBtarget (B ⊔ C.finalWire) hsim hsimDefect
  have htargetFinal : N4.targetAmbient 10 (mulTarget 5) ≤ C.finalWire := by
    apply sup_le
    · simpa [Circuit.finalWire] using affine_le_wireSpace C.gate (j := r)
    · rw [mulTarget, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hC k
  have hmissing : targetANF firstOrderMissingCoeff ∈
      firstOrderEnvelopeState :=
    hclosed ⟨(le_sup_right : C.finalWire ≤ B ⊔ C.finalWire) (htargetFinal
      (Submodule.mem_sup_right (targetANF_mem_mulTarget _))),
      Submodule.mem_sup_right (targetANF_mem_mulTarget _)⟩
  have hmissingTwo := ((E2.mem_quadraticEnvelopeState_iff
    firstOrderEnvelopeTwoSpace (targetANF firstOrderMissingCoeff)).1
      hmissing).2
  rw [quadraticProjection_targetANF] at hmissingTwo
  exact targetTwo_firstOrderMissingCoeff_not_mem hmissingTwo

end
end N5
end UnrestrictedBooleanMul
