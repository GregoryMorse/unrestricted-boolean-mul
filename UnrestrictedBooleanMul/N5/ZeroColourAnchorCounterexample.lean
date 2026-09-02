import UnrestrictedBooleanMul.N5.ZeroColourAnchorSemantic

/-!
# Counterexample to the history-free anchored zero-colour reduction

The current rational-zero `001` representative obligation forgets which
quadratic correction wires can coexist in a reachable prefix.  The explicit
Boolean identity below shows that the resulting history-free proposition is
false.  Keeping the counterexample kernel checked prevents the final proof
from silently depending on that over-strong interface.
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

private theorem ce_missingTwo :
    targetTwo firstOrderMissingCoeff =
      targetPairTwo 0 2 + targetPairTwo 1 1 + targetPairTwo 2 0 := by
  rw [targetTwo_eq_double_sum]
  simp [firstOrderMissingCoeff, hankelIndex, Fin.sum_univ_succ]
  module

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

end
end N5
end UnrestrictedBooleanMul
