import UnrestrictedBooleanMul.N5.ZeroColourAnchorSemantic
import UnrestrictedBooleanMul.N5.RegimeClosure

/-!
# Counterexample to the history-free anchored zero-colour reduction

The current rational-zero `001` representative obligation asserts a fixed
target-envelope closure that is stronger than the circuit lower bound needs.
The explicit Boolean identity below shows that two feedback gates can trade
one high-defect birth for the missing target coordinate, even from a genuine
quadratic prefix.  Keeping the counterexample kernel checked prevents the
final proof from silently depending on that false interface and identifies
the gate cost that a replacement deficit invariant must retain.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

private def ceP : LocalKleinCoord := ![1, 1, 0, 0, 1, 1]
private def ceEll : LinearForm := aLinear 0 + bLinear 0
private def ceM : LinearForm := aLinear 1 + bLinear 0 + bLinear 2
private def ceEll' : LinearForm := bLinear 0
private def ceM' : LinearForm :=
  aLinear 0 + aLinear 1 + aLinear 2 +
    bLinear 0 + bLinear 1 + bLinear 2

private def ceAnchor : TwoForm := localTwoForm 0 ceP
private def ceAnchorLeft : LinearForm := aLinear 0 + bLinear 1
private def ceAnchorRight : LinearForm := aLinear 1 + bLinear 0
private def ceAnchorWire : ANF 10 :=
  linearANFTen ceAnchorLeft * linearANFTen ceAnchorRight
private def ceAffineCorrection : ANF 10 :=
  1 + X (aCoord 2) + X (bCoord 0) + X (bCoord 1)

private theorem quadraticANFOfForm_zero :
    quadraticANFOfForm (0 : TwoForm) = 0 :=
  map_zero quadraticANFOfFormLinear

private theorem ce_left_first :
    quadraticCoordinateANF 1 ceEll 0 =
      1 + X (aCoord 0) + X (bCoord 0) := by
  simp [quadraticCoordinateANF, ceEll, linearANFTen_add,
    quadraticANFOfForm_zero]
  module

private theorem ce_left_second :
    quadraticCoordinateANF 1 ceM rationalZeroValueTwo =
      1 + X (aCoord 1) + X (bCoord 0) + X (bCoord 2) +
        X (aCoord 0) * X (bCoord 0) := by
  simp [quadraticCoordinateANF, ceM, linearANFTen_add,
    rationalZeroValueTwo, quadraticANFOfForm_targetPairTwo]
  ring

private theorem ce_right_first :
    quadraticCoordinateANF 1 ceEll' 0 =
      1 + X (bCoord 0) := by
  simp [quadraticCoordinateANF, ceEll', quadraticANFOfForm_zero]

private theorem ce_right_second :
    quadraticCoordinateANF 0 ceM' rationalZeroValueTwo =
      X (aCoord 0) + X (aCoord 1) + X (aCoord 2) +
        X (bCoord 0) + X (bCoord 1) + X (bCoord 2) +
        X (aCoord 0) * X (bCoord 0) := by
  simp [quadraticCoordinateANF, ceM', linearANFTen_add,
    rationalZeroValueTwo, quadraticANFOfForm_targetPairTwo]

private theorem ce_product_sum_explicit :
    quadraticCoordinateANF 1 ceEll 0 *
          quadraticCoordinateANF 1 ceM rationalZeroValueTwo +
        quadraticCoordinateANF 1 ceEll' 0 *
          quadraticCoordinateANF 0 ceM' rationalZeroValueTwo =
      1 + X (aCoord 2) + X (bCoord 0) + X (bCoord 1) +
        X (aCoord 0) * X (aCoord 1) +
        X (aCoord 0) * X (bCoord 2) +
        X (aCoord 0) * X (bCoord 0) +
        X (aCoord 2) * X (bCoord 0) +
        X (bCoord 0) * X (bCoord 1) := by
  rw [ce_left_first, ce_left_second, ce_right_first, ce_right_second]
  ring_nf
  simp [pow_two, N4.anf_mul_self]
  have hthree : (3 : ANF 10) = 1 := by
    calc
      (3 : ANF 10) = 2 + 1 := by norm_num
      _ = 0 + 1 := by rw [anf_two_eq_zero]
      _ = 1 := by rw [zero_add]
  rw [hthree]
  ring

private theorem ce_product_sum_mem_quadratic :
    quadraticCoordinateANF 1 ceEll 0 *
          quadraticCoordinateANF 1 ceM rationalZeroValueTwo +
        quadraticCoordinateANF 1 ceEll' 0 *
          quadraticCoordinateANF 0 ceM' rationalZeroValueTwo ∈
      N4.quadraticANFSpace 10 := by
  rw [ce_product_sum_explicit]
  let W := N4.quadraticANFSpace 10
  have hone : (1 : ANF 10) ∈ W :=
    N4.affine_le_quadraticANFSpace (one_mem_affine 10)
  have hX (i : Fin 10) : X i ∈ W :=
    N4.affine_le_quadraticANFSpace (X_mem_affine i)
  have hXX (i j : Fin 10) : X i * X j ∈ W := by
    exact (N5.degreeLE_one_X_ten i).mul (N5.degreeLE_one_X_ten j)
  exact W.add_mem
    (W.add_mem
      (W.add_mem
        (W.add_mem
          (W.add_mem
            (W.add_mem
              (W.add_mem
                (W.add_mem hone (hX (aCoord 2)))
                (hX (bCoord 0)))
              (hX (bCoord 1)))
            (hXX (aCoord 0) (aCoord 1)))
          (hXX (aCoord 0) (bCoord 2)))
        (hXX (aCoord 0) (bCoord 0)))
      (hXX (aCoord 2) (bCoord 0)))
    (hXX (bCoord 0) (bCoord 1))

private theorem ce_high :
    lowProductHighClass ceEll ceM 0 rationalZeroValueTwo =
      lowProductHighClass ceEll' ceM' 0 rationalZeroValueTwo := by
  exact lowProductHighClass_eq_of_product_sum_mem_quadratic
    1 1 1 0 ceEll ceM ceEll' ceM'
      0 rationalZeroValueTwo 0 rationalZeroValueTwo
      ce_product_sum_mem_quadratic

private theorem ce_localTwo :
    localTwoForm 0 ceP =
      squarefreeWedge (aLinear 0) (aLinear 1) +
        targetPairTwo 0 0 + targetPairTwo 1 1 +
        squarefreeWedge (bLinear 0) (bLinear 1) := by
  simp [ceP, localTwoForm, localKleinPair, closedPlaceLocalBasis,
    targetPairTwo, Fin.sum_univ_succ]
  module

private theorem ce_anchor_factorization :
    ceAnchor = squarefreeWedge ceAnchorLeft ceAnchorRight := by
  rw [ceAnchor, ce_localTwo]
  simp only [ceAnchorLeft, ceAnchorRight,
    squarefreeWedge_add_left, squarefreeWedge_add_right]
  rw [squarefreeWedge_comm_f2 (bLinear 1) (aLinear 1),
    squarefreeWedge_comm_f2 (bLinear 1) (bLinear 0)]
  simp only [targetPairTwo]
  module

private theorem ce_anchor_wire_quadratic :
    ceAnchorWire ∈ N4.quadraticANFSpace 10 := by
  exact ((linearANFTen_degreeLE_one ceAnchorLeft).mul
    (linearANFTen_degreeLE_one ceAnchorRight)).mono (by omega)

private theorem ce_anchor_wire_projection :
    quadraticProjection 10 ceAnchorWire = ceAnchor := by
  rw [ceAnchorWire,
    quadraticProjection_linearANFTen_mul_linearANFTen,
    ← ce_anchor_factorization]

private theorem ce_anchor_wire_explicit :
    ceAnchorWire =
      X (aCoord 0) * X (aCoord 1) +
        X (aCoord 0) * X (bCoord 0) +
        X (aCoord 1) * X (bCoord 1) +
        X (bCoord 0) * X (bCoord 1) := by
  simp [ceAnchorWire, ceAnchorLeft, ceAnchorRight,
    linearANFTen_add]
  ring

private theorem ce_missingTwo :
    targetTwo firstOrderMissingCoeff =
      targetPairTwo 0 2 + targetPairTwo 1 1 + targetPairTwo 2 0 := by
  rw [targetTwo_eq_double_sum]
  simp [firstOrderMissingCoeff, hankelIndex, Fin.sum_univ_succ]
  module

private theorem ce_target_missing_explicit :
    targetANF firstOrderMissingCoeff =
      X (aCoord 0) * X (bCoord 2) +
        X (aCoord 1) * X (bCoord 1) +
        X (aCoord 2) * X (bCoord 0) := by
  simp [targetANF, firstOrderMissingCoeff, Mul, mulCoefficient,
    Fin.sum_univ_succ, aVar_five_eq_X_aCoord,
    bVar_five_eq_X_bCoord]
  ring

private theorem ce_full_anf_identity :
    quadraticCoordinateANF 1 ceEll 0 *
          quadraticCoordinateANF 1 ceM rationalZeroValueTwo +
        quadraticCoordinateANF 1 ceEll' 0 *
          quadraticCoordinateANF 0 ceM' rationalZeroValueTwo +
        ceAnchorWire =
      targetANF firstOrderMissingCoeff + ceAffineCorrection := by
  rw [ce_product_sum_explicit, ce_anchor_wire_explicit,
    ce_target_missing_explicit]
  simp only [ceAffineCorrection]
  ring_nf
  simp [anf_two_eq_zero]

private theorem ce_shadow :
    lowProductQuadraticShadow 1 1 ceEll ceM 0 rationalZeroValueTwo +
        lowProductQuadraticShadow 1 0 ceEll' ceM' 0 rationalZeroValueTwo +
        localTwoForm 0 ceP =
      targetTwo firstOrderMissingCoeff := by
  have hproj := congrArg (quadraticProjection 10) ce_product_sum_explicit
  simp only [map_add,
    quadraticProjection_quadraticCoordinateANF_mul,
    quadraticProjection_one, quadraticProjection_X] at hproj
  simp only [quadraticProjection_X_mul_X'] at hproj
  have ha (i : Fin 5) :
      linearProjection 10 (X (aCoord i)) = aLinear i := by
    rw [← linearANFTen_aLinear i, linearProjection_linearANFTen]
  have hb (i : Fin 5) :
      linearProjection 10 (X (bCoord i)) = bLinear i := by
    rw [← linearANFTen_bLinear i, linearProjection_linearANFTen]
  simp_rw [ha, hb] at hproj
  rw [ce_localTwo, ce_missingTwo]
  rw [hproj]
  funext s
  simp only [Pi.add_apply, Pi.zero_apply, targetPairTwo]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

private theorem ceP_ne_zero : ceP ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 6)
  simp [ceP] at h0

private theorem ceP_satisfiesKlein : SatisfiesKlein ceP := by
  simp [SatisfiesKlein, ceP]

/-- The proposed `001` functional reduction is too strong: this explicit
algebraic collision satisfies all of its hypotheses but has clean value one. -/
theorem not_nonzeroRationalZeroAnchoredEnvelopeFunctionalCase_001 :
    ¬ NonzeroRationalZeroAnchoredEnvelopeFunctionalCase 0 0 1 := by
  intro hcase
  have hbase := hcase ceP ceP_ne_zero ceP_satisfiesKlein
    1 1 1 0 ceEll ceM ceEll' ceM'
    0 rationalZeroValueTwo 0 rationalZeroValueTwo
    (Submodule.zero_mem _) rationalZeroValueTwo_mem_firstOrderEnvelope
    (Submodule.zero_mem _) rationalZeroValueTwo_mem_firstOrderEnvelope
    (by simpa using ce_high)
    0 (Submodule.zero_mem _) (by
      simpa [rationalZeroAnchorShadowCorrection] using ce_shadow)
  have hanchor :
      secondJetCleanFunctional (localTwoForm 0 ceP) = 0 :=
    LinearMap.mem_ker.mp (targetCleanSecondJetSpace_le_kernel
      (rationalZero_localTwoForm_mem_targetClean ceP))
  have hevaluated := congrArg secondJetCleanFunctional ce_shadow
  simp only [map_add, secondJetCleanFunctional_targetTwo] at hevaluated
  rw [hanchor, firstOrderMissingFunctional_missing] at hevaluated
  simp only [add_zero] at hevaluated
  simp only [map_add] at hbase
  rw [hbase] at hevaluated
  norm_num at hevaluated

private theorem ce_coordinate_mem_anchor
    (a : F₂) (ell : LinearForm) (q : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace) :
    quadraticCoordinateANF a ell q ∈ firstOrderAnchorState ceAnchor := by
  exact (E2.mem_quadraticEnvelopeState_iff
    (firstOrderAnchorTwoSpace ceAnchor)
    (quadraticCoordinateANF a ell q)).2
    ⟨quadraticCoordinateANF_mem_quadraticANFSpace a ell q,
      by
        rw [quadraticProjection_quadraticCoordinateANF]
        exact Submodule.mem_sup_left hq⟩

private theorem ce_anchor_wire_mem_anchor :
    ceAnchorWire ∈ firstOrderAnchorState ceAnchor := by
  exact (E2.mem_quadraticEnvelopeState_iff
    (firstOrderAnchorTwoSpace ceAnchor) ceAnchorWire).2
    ⟨ce_anchor_wire_quadratic, by
      rw [ce_anchor_wire_projection]
      exact Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self ceAnchor)⟩

private theorem ce_affine_mem_anchor :
    ceAffineCorrection ∈ firstOrderAnchorState ceAnchor := by
  apply E2.affine_le_quadraticEnvelopeState
  exact (affine 10).add_mem
    ((affine 10).add_mem
      ((affine 10).add_mem (one_mem_affine 10)
        (X_mem_affine (aCoord 2)))
      (X_mem_affine (bCoord 0)))
    (X_mem_affine (bCoord 1))

private theorem ce_anchor_decomposable : IsDecomposableTwo ceAnchor := by
  exact localTwoForm_decomposable_of_satisfiesKlein 0 ceP
    ceP_satisfiesKlein

private theorem ce_anchor_defect_le_one :
    N4.flagDefectRank (firstOrderAnchorState ceAnchor) (mulTarget 5) ≤ 1 := by
  by_cases htarget : ceAnchor ∈ targetTwoSpace
  · rw [firstOrderAnchorState_defectRank_of_mem_target
      ceAnchor ce_anchor_decomposable htarget]
    omega
  · rw [firstOrderAnchorState_defectRank_of_not_mem_target
      ceAnchor ce_anchor_decomposable htarget]

private abbrev ceRightFirst : ANF 10 :=
  quadraticCoordinateANF 1 ceEll' 0
private abbrev ceRightSecond : ANF 10 :=
  quadraticCoordinateANF 0 ceM' rationalZeroValueTwo
private abbrev ceLeftFirst : ANF 10 :=
  quadraticCoordinateANF 1 ceEll 0
private abbrev ceLeftSecond : ANF 10 :=
  quadraticCoordinateANF 1 ceM rationalZeroValueTwo
private abbrev ceAfterRight : Submodule F₂ (ANF 10) :=
  andExtend (firstOrderAnchorState ceAnchor) ceRightFirst ceRightSecond
private abbrev ceAfterBoth : Submodule F₂ (ANF 10) :=
  andExtend ceAfterRight ceLeftFirst ceLeftSecond

private theorem ce_right_first_mem_anchor :
    ceRightFirst ∈ firstOrderAnchorState ceAnchor :=
  ce_coordinate_mem_anchor 1 ceEll' 0 (Submodule.zero_mem _)

private theorem ce_right_second_mem_anchor :
    ceRightSecond ∈ firstOrderAnchorState ceAnchor :=
  ce_coordinate_mem_anchor 0 ceM' rationalZeroValueTwo
    rationalZeroValueTwo_mem_firstOrderEnvelope

private theorem ce_left_first_mem_anchor :
    ceLeftFirst ∈ firstOrderAnchorState ceAnchor :=
  ce_coordinate_mem_anchor 1 ceEll 0 (Submodule.zero_mem _)

private theorem ce_left_second_mem_anchor :
    ceLeftSecond ∈ firstOrderAnchorState ceAnchor :=
  ce_coordinate_mem_anchor 1 ceM rationalZeroValueTwo
    rationalZeroValueTwo_mem_firstOrderEnvelope

private theorem ce_suffix :
    DefectLegalSuffix (firstOrderAnchorState ceAnchor) ceAfterBoth := by
  have hbaseDef := ce_anchor_defect_le_one
  have hrightDef :
      N4.flagDefectRank ceAfterRight (mulTarget 5) ≤ 2 :=
    (flagDefectRank_andExtend_le_succ
      (firstOrderAnchorState ceAnchor) ceRightFirst ceRightSecond).trans
      (by omega)
  have hright :
      DefectLegalSuffix (firstOrderAnchorState ceAnchor) ceAfterRight :=
    .step (.refl (ce_anchor_defect_le_one.trans (by omega)))
      ceRightFirst ceRightSecond
      ce_right_first_mem_anchor ce_right_second_mem_anchor
      (hrightDef.trans (by omega))
  have hleftFirst : ceLeftFirst ∈ ceAfterRight :=
    (le_sup_left : firstOrderAnchorState ceAnchor ≤ ceAfterRight)
      ce_left_first_mem_anchor
  have hleftSecond : ceLeftSecond ∈ ceAfterRight :=
    (le_sup_left : firstOrderAnchorState ceAnchor ≤ ceAfterRight)
      ce_left_second_mem_anchor
  exact .step hright ceLeftFirst ceLeftSecond hleftFirst hleftSecond
    ((flagDefectRank_andExtend_le_succ
      ceAfterRight ceLeftFirst ceLeftSecond).trans (by omega))

private theorem ce_target_missing_mem_afterBoth :
    targetANF firstOrderMissingCoeff ∈ ceAfterBoth := by
  have hleft : ceLeftFirst * ceLeftSecond ∈ ceAfterBoth :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hrightBase : ceRightFirst * ceRightSecond ∈ ceAfterRight :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hright : ceRightFirst * ceRightSecond ∈ ceAfterBoth :=
    (le_sup_left : ceAfterRight ≤ ceAfterBoth) hrightBase
  have hanchor : ceAnchorWire ∈ ceAfterBoth :=
    (le_sup_left : ceAfterRight ≤ ceAfterBoth)
      ((le_sup_left : firstOrderAnchorState ceAnchor ≤ ceAfterRight)
        ce_anchor_wire_mem_anchor)
  have haffine : ceAffineCorrection ∈ ceAfterBoth :=
    (le_sup_left : ceAfterRight ≤ ceAfterBoth)
      ((le_sup_left : firstOrderAnchorState ceAnchor ≤ ceAfterRight)
        ce_affine_mem_anchor)
  have hsum :
      ceLeftFirst * ceLeftSecond + ceRightFirst * ceRightSecond +
          ceAnchorWire + ceAffineCorrection ∈ ceAfterBoth :=
    ceAfterBoth.add_mem
      (ceAfterBoth.add_mem (ceAfterBoth.add_mem hleft hright) hanchor)
      haffine
  have heq :
      targetANF firstOrderMissingCoeff =
        ceLeftFirst * ceLeftSecond + ceRightFirst * ceRightSecond +
          ceAnchorWire + ceAffineCorrection := by
    calc
      targetANF firstOrderMissingCoeff =
          (targetANF firstOrderMissingCoeff + ceAffineCorrection) +
            ceAffineCorrection := by
        symm
        rw [add_assoc, anf_add_self, add_zero]
      _ = (ceLeftFirst * ceLeftSecond +
            ceRightFirst * ceRightSecond + ceAnchorWire) +
          ceAffineCorrection := by
        rw [← ce_full_anf_identity]
  rwa [heq]

private theorem ce_target_missing_not_mem_envelope :
    targetANF firstOrderMissingCoeff ∉
      affine 10 ⊔ firstOrderEnvelopeState := by
  rw [sup_eq_right.mpr affine_le_firstOrderEnvelopeState]
  intro hmem
  have htwo := ((E2.mem_quadraticEnvelopeState_iff
    firstOrderEnvelopeTwoSpace (targetANF firstOrderMissingCoeff)).1 hmem).2
  rw [quadraticProjection_targetANF] at htwo
  exact targetTwo_firstOrderMissingCoeff_not_mem htwo

/-- The same explicit collision refutes the full history-free stable-state
interface, not merely its reduced three-scalar sufficient condition.  The
two displayed AND extensions remain within total quotient defect three and
expose the missing target coordinate. -/
theorem not_anchoredFirstOrderStability : ¬ AnchoredFirstOrderStability := by
  intro hstable
  have hcontain := hstable ceAnchor ce_anchor_decomposable
    ceAfterBoth ce_suffix
  exact ce_target_missing_not_mem_envelope
    (hcontain ⟨ce_target_missing_mem_afterBoth,
      Submodule.mem_sup_right
        (targetANF_mem_mulTarget firstOrderMissingCoeff)⟩)

/-! ## The obstruction already starts from a genuine quadratic prefix -/

private def cePrefixLeft : Fin 2 → ANF 10 :=
  ![X (aCoord 0), linearANFTen ceAnchorLeft]

private def cePrefixRight : Fin 2 → ANF 10 :=
  ![X (bCoord 0), linearANFTen ceAnchorRight]

private theorem cePrefixLeft_affine (i : Fin 2) :
    cePrefixLeft i ∈ affine 10 := by
  fin_cases i
  · exact X_mem_affine (aCoord 0)
  · exact linearANFTen_mem_affine ceAnchorLeft

private theorem cePrefixRight_affine (i : Fin 2) :
    cePrefixRight i ∈ affine 10 := by
  fin_cases i
  · exact X_mem_affine (bCoord 0)
  · exact linearANFTen_mem_affine ceAnchorRight

private def cePrefix : Circuit 10 2 :=
  Circuit.ofAffineProducts cePrefixLeft cePrefixRight
    cePrefixLeft_affine cePrefixRight_affine

private abbrev cePrefixState : Submodule F₂ (ANF 10) :=
  N4.circuitFlag cePrefix 2

private theorem cePrefix_gate_zero :
    cePrefix.gate 0 = quadraticANFOfForm rationalZeroValueTwo := by
  simp [cePrefix, cePrefixLeft, cePrefixRight, rationalZeroValueTwo,
    quadraticANFOfForm_targetPairTwo]

private theorem cePrefix_gate_one : cePrefix.gate 1 = ceAnchorWire := by
  rfl

private theorem cePrefix_allQuadratic : AllQuadraticPrefix cePrefix 2 := by
  intro i _hi
  change N4.DegreeLE 2 (cePrefix.gate i)
  fin_cases i
  · simpa [cePrefix, cePrefixLeft, cePrefixRight] using
      ((degreeLE_one_X_ten (aCoord 0)).mul
        (degreeLE_one_X_ten (bCoord 0)))
  · simpa [cePrefix, cePrefixLeft, cePrefixRight, ceAnchorWire] using
      ((linearANFTen_degreeLE_one ceAnchorLeft).mul
        (linearANFTen_degreeLE_one ceAnchorRight)).mono (by omega)

private theorem cePrefixState_le_anchorState :
    cePrefixState ≤ firstOrderAnchorState ceAnchor := by
  change wireSpace cePrefix.gate 2 ≤ firstOrderAnchorState ceAnchor
  rw [wireSpace]
  apply sup_le (E2.affine_le_quadraticEnvelopeState _)
  rw [Submodule.span_le]
  rintro p ⟨i, _hi, rfl⟩
  fin_cases i
  · change cePrefix.gate 0 ∈ firstOrderAnchorState ceAnchor
    rw [cePrefix_gate_zero]
    exact (E2.mem_quadraticEnvelopeState_iff
      (firstOrderAnchorTwoSpace ceAnchor)
      (quadraticANFOfForm rationalZeroValueTwo)).2
      ⟨pureQuadraticANFSpace_le_quadraticANFSpace
          ⟨rationalZeroValueTwo, rfl⟩,
        by
          rw [quadraticProjection_quadraticANFOfForm]
          exact Submodule.mem_sup_left
            rationalZeroValueTwo_mem_firstOrderEnvelope⟩
  · change cePrefix.gate 1 ∈ firstOrderAnchorState ceAnchor
    rw [cePrefix_gate_one]
    exact ce_anchor_wire_mem_anchor

private theorem cePrefixState_defect_le_one :
    N4.flagDefectRank cePrefixState (mulTarget 5) ≤ 1 :=
  (flagDefectRank_mono cePrefixState_le_anchorState).trans
    ce_anchor_defect_le_one

private theorem ce_affine_mem_prefix : ceAffineCorrection ∈ cePrefixState := by
  exact affine_le_wireSpace cePrefix.gate
    (show ceAffineCorrection ∈ affine 10 from by
      exact (affine 10).add_mem
        ((affine 10).add_mem
          ((affine 10).add_mem (one_mem_affine 10)
            (X_mem_affine (aCoord 2)))
          (X_mem_affine (bCoord 0)))
        (X_mem_affine (bCoord 1)))

private theorem ce_anchor_wire_mem_prefix : ceAnchorWire ∈ cePrefixState := by
  rw [← cePrefix_gate_one]
  exact gate_mem_wireSpace cePrefix.gate (1 : Fin 2) (by omega)

private theorem ce_rationalZero_wire_mem_prefix :
    quadraticANFOfForm rationalZeroValueTwo ∈ cePrefixState := by
  rw [← cePrefix_gate_zero]
  exact gate_mem_wireSpace cePrefix.gate (0 : Fin 2) (by omega)

private theorem ce_coordinate_mem_prefix_of_zero_or_rationalZero
    (a : F₂) (ell : LinearForm) (q : TwoForm)
    (hq : q = 0 ∨ q = rationalZeroValueTwo) :
    quadraticCoordinateANF a ell q ∈ cePrefixState := by
  rcases hq with rfl | rfl
  · simp only [quadraticCoordinateANF, quadraticANFOfForm_zero, add_zero]
    exact (affine_le_wireSpace cePrefix.gate)
      ((affine 10).add_mem
        (Submodule.smul_mem _ _ (one_mem_affine 10))
        (linearANFTen_mem_affine ell))
  · exact cePrefixState.add_mem
      ((affine_le_wireSpace cePrefix.gate)
        ((affine 10).add_mem
          (Submodule.smul_mem _ _ (one_mem_affine 10))
          (linearANFTen_mem_affine ell)))
      ce_rationalZero_wire_mem_prefix

private abbrev cePrefixAfterRight : Submodule F₂ (ANF 10) :=
  andExtend cePrefixState ceRightFirst ceRightSecond
private abbrev cePrefixAfterBoth : Submodule F₂ (ANF 10) :=
  andExtend cePrefixAfterRight ceLeftFirst ceLeftSecond

private theorem ce_prefix_suffix :
    DefectLegalSuffix cePrefixState cePrefixAfterBoth := by
  have hrightFirst : ceRightFirst ∈ cePrefixState :=
    ce_coordinate_mem_prefix_of_zero_or_rationalZero 1 ceEll' 0 (Or.inl rfl)
  have hrightSecond : ceRightSecond ∈ cePrefixState :=
    ce_coordinate_mem_prefix_of_zero_or_rationalZero
      0 ceM' rationalZeroValueTwo (Or.inr rfl)
  have hrightDef :
      N4.flagDefectRank cePrefixAfterRight (mulTarget 5) ≤ 2 :=
    (flagDefectRank_andExtend_le_succ
      cePrefixState ceRightFirst ceRightSecond).trans (by
        have hbase := cePrefixState_defect_le_one
        omega)
  have hright : DefectLegalSuffix cePrefixState cePrefixAfterRight :=
    .step (.refl (cePrefixState_defect_le_one.trans (by omega)))
      ceRightFirst ceRightSecond hrightFirst hrightSecond
      (hrightDef.trans (by omega))
  have hleftFirst : ceLeftFirst ∈ cePrefixAfterRight :=
    (le_sup_left : cePrefixState ≤ cePrefixAfterRight)
      (ce_coordinate_mem_prefix_of_zero_or_rationalZero
        1 ceEll 0 (Or.inl rfl))
  have hleftSecond : ceLeftSecond ∈ cePrefixAfterRight :=
    (le_sup_left : cePrefixState ≤ cePrefixAfterRight)
      (ce_coordinate_mem_prefix_of_zero_or_rationalZero
        1 ceM rationalZeroValueTwo (Or.inr rfl))
  exact .step hright ceLeftFirst ceLeftSecond hleftFirst hleftSecond
    ((flagDefectRank_andExtend_le_succ
      cePrefixAfterRight ceLeftFirst ceLeftSecond).trans (by omega))

private theorem ce_target_missing_mem_prefixAfterBoth :
    targetANF firstOrderMissingCoeff ∈ cePrefixAfterBoth := by
  have hleft : ceLeftFirst * ceLeftSecond ∈ cePrefixAfterBoth :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hrightBase : ceRightFirst * ceRightSecond ∈ cePrefixAfterRight :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hright : ceRightFirst * ceRightSecond ∈ cePrefixAfterBoth :=
    (le_sup_left : cePrefixAfterRight ≤ cePrefixAfterBoth) hrightBase
  have hanchor : ceAnchorWire ∈ cePrefixAfterBoth :=
    (le_sup_left : cePrefixAfterRight ≤ cePrefixAfterBoth)
      ((le_sup_left : cePrefixState ≤ cePrefixAfterRight)
        ce_anchor_wire_mem_prefix)
  have haffine : ceAffineCorrection ∈ cePrefixAfterBoth :=
    (le_sup_left : cePrefixAfterRight ≤ cePrefixAfterBoth)
      ((le_sup_left : cePrefixState ≤ cePrefixAfterRight)
        ce_affine_mem_prefix)
  rw [show targetANF firstOrderMissingCoeff =
      ceLeftFirst * ceLeftSecond + ceRightFirst * ceRightSecond +
        ceAnchorWire + ceAffineCorrection by
    calc
      targetANF firstOrderMissingCoeff =
          (targetANF firstOrderMissingCoeff + ceAffineCorrection) +
            ceAffineCorrection := by
        symm
        rw [add_assoc, anf_add_self, add_zero]
      _ = (ceLeftFirst * ceLeftSecond +
            ceRightFirst * ceRightSecond + ceAnchorWire) +
          ceAffineCorrection := by
        rw [← ce_full_anf_identity]]
  exact cePrefixAfterBoth.add_mem
    (cePrefixAfterBoth.add_mem
      (cePrefixAfterBoth.add_mem hleft hright) hanchor)
    haffine

/-- The manuscript-level circuit-facing saturation premise is itself false,
not only its canonical-state sufficient condition.  A genuine two-gate
all-quadratic prefix of defect at most one admits the same defect-legal
two-gate escape from the fixed first-order envelope. -/
theorem not_firstOrderSaturation : ¬ FirstOrderSaturation := by
  intro hstable
  have hs := hstable cePrefix (j := 2) (by omega)
    cePrefix_allQuadratic cePrefixState_defect_le_one
  have hcontain := hs cePrefixAfterBoth ce_prefix_suffix
  exact ce_target_missing_not_mem_envelope
    (hcontain ⟨ce_target_missing_mem_prefixAfterBoth,
      Submodule.mem_sup_right
        (targetANF_mem_mulTarget firstOrderMissingCoeff)⟩)

end
end N5
end UnrestrictedBooleanMul
