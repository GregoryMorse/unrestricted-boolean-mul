import UnrestrictedBooleanMul.N5.TargetCleanMatrix

/-!
# Polarized kernel of the first-order envelope

This module gives the coordinate form of manuscript equation (11.3).  The
eight exact first-order target directions have 28 polarized pair products.
Their wedge map has precisely the three rational value--jet rotations in its
kernel.

The proof is a sparse algebraic pivot calculation.  It uses 25 named
four-form coordinates, not enumeration of coefficient assignments.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

abbrev CrossMatrix := Fin 5 → Fin 5 → F₂
abbrev TargetCrossFour := Fin 5 → Fin 5 → Fin 5 → Fin 5 → F₂
abbrev FirstOrderPairCoeff := Fin 28 → F₂

def crossOuter (x y : Fin 5 → F₂) : CrossMatrix :=
  fun i j => x i * y j

/-- The `2A,2B` block of the exterior product of two cross matrices. -/
def crossWedge (P Q : CrossMatrix) : TargetCrossFour :=
  fun i k j l =>
    P i j * Q k l + P i l * Q k j +
    Q i j * P k l + Q i l * P k j

theorem crossWedge_add_right (P Q R : CrossMatrix) :
    crossWedge P (Q + R) = crossWedge P Q + crossWedge P R := by
  funext i k j l
  simp only [crossWedge, Pi.add_apply]
  ring

theorem crossWedge_outer_shared_left
    (x y z : Fin 5 → F₂) :
    crossWedge (crossOuter x y) (crossOuter x z) = 0 := by
  funext i k j l
  simp only [crossWedge, crossOuter, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem crossWedge_outer_shared_right
    (x y z : Fin 5 → F₂) :
    crossWedge (crossOuter x y) (crossOuter z y) = 0 := by
  funext i k j l
  simp only [crossWedge, crossOuter, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

def crossBasisZero : Fin 5 → F₂ := ![1, 0, 0, 0, 0]
def crossBasisOne : Fin 5 → F₂ := ![0, 1, 0, 0, 0]
def crossBasisThree : Fin 5 → F₂ := ![0, 0, 0, 1, 0]
def crossBasisFour : Fin 5 → F₂ := ![0, 0, 0, 0, 1]
def crossValueOne : Fin 5 → F₂ := ![1, 1, 1, 1, 1]
def crossJetOne : Fin 5 → F₂ := ![0, 1, 0, 1, 0]

theorem hankelMatrix_rZeroCoeff :
    hankelMatrix rZeroCoeff = crossOuter crossBasisZero crossBasisZero := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem hankelMatrix_jZeroCoeff :
    hankelMatrix jZeroCoeff =
      crossOuter crossBasisZero crossBasisOne +
        crossOuter crossBasisOne crossBasisZero := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem hankelMatrix_rOneCoeff :
    hankelMatrix rOneCoeff = crossOuter crossValueOne crossValueOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem hankelMatrix_exactJOneCoeff :
    hankelMatrix exactJOneCoeff =
      crossOuter crossValueOne crossJetOne +
        crossOuter crossJetOne crossValueOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem hankelMatrix_rInfinityCoeff :
    hankelMatrix rInfinityCoeff = crossOuter crossBasisFour crossBasisFour := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem hankelMatrix_exactJInfinityCoeff :
    hankelMatrix exactJInfinityCoeff =
      crossOuter crossBasisFour crossBasisThree +
        crossOuter crossBasisThree crossBasisFour := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Exterior product of two Hankel target directions, restricted to the only
possibly nonzero four-form block. -/
def targetCrossWedge (c d : TargetCoeff) : TargetCrossFour :=
  crossWedge (hankelMatrix c) (hankelMatrix d)

theorem targetCrossWedge_rZero_jZero :
    targetCrossWedge rZeroCoeff jZeroCoeff = 0 := by
  rw [targetCrossWedge, hankelMatrix_rZeroCoeff,
    hankelMatrix_jZeroCoeff, crossWedge_add_right,
    crossWedge_outer_shared_left, crossWedge_outer_shared_right,
    add_zero]

theorem targetCrossWedge_rOne_exactJOne :
    targetCrossWedge rOneCoeff exactJOneCoeff = 0 := by
  rw [targetCrossWedge, hankelMatrix_rOneCoeff,
    hankelMatrix_exactJOneCoeff, crossWedge_add_right,
    crossWedge_outer_shared_left, crossWedge_outer_shared_right,
    add_zero]

theorem targetCrossWedge_rInfinity_exactJInfinity :
    targetCrossWedge rInfinityCoeff exactJInfinityCoeff = 0 := by
  rw [targetCrossWedge, hankelMatrix_rInfinityCoeff,
    hankelMatrix_exactJInfinityCoeff, crossWedge_add_right,
    crossWedge_outer_shared_left, crossWedge_outer_shared_right,
    add_zero]

/-- Lexicographic list of the 28 unordered pairs of the eight exact
first-order directions. -/
def firstOrderPairLeft : Fin 28 → Fin 8 :=
  ![0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2,
    3, 3, 3, 3,
    4, 4, 4,
    5, 5,
    6]

def firstOrderPairRight : Fin 28 → Fin 8 :=
  ![1, 2, 3, 4, 5, 6, 7,
    2, 3, 4, 5, 6, 7,
    3, 4, 5, 6, 7,
    4, 5, 6, 7,
    5, 6, 7,
    6, 7,
    7]

def firstOrderPairWedge (k : Fin 28) : TargetCrossFour :=
  targetCrossWedge
    (exactFirstOrderDirections (firstOrderPairLeft k))
    (exactFirstOrderDirections (firstOrderPairRight k))

/-- Polarized multiplication on the exact first-order envelope basis. -/
def firstOrderEnvelopePolarizedMap :
    FirstOrderPairCoeff →ₗ[F₂] TargetCrossFour where
  toFun α := ∑ k : Fin 28, α k •
    firstOrderPairWedge k
  map_add' α β := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' a α := by
    simp [Finset.smul_sum, smul_smul]

theorem firstOrderEnvelopePolarizedMap_basis (k : Fin 28) :
    firstOrderEnvelopePolarizedMap (Pi.basisFun F₂ (Fin 28) k) =
      firstOrderPairWedge k := by
  ext i j l m
  change (∑ x : Fin 28, (Pi.basisFun F₂ (Fin 28) k) x •
      firstOrderPairWedge x) i j l m = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single k]
  · simp [Pi.basisFun]
  · intro b hbk
    simp [Pi.basisFun, hbk]

/-- The three rational value--jet rotations, at pair indices `2,9,15`. -/
def firstOrderLocalKernelDirections : Fin 3 → FirstOrderPairCoeff :=
  ![Pi.basisFun F₂ (Fin 28) 2,
    Pi.basisFun F₂ (Fin 28) 9,
    Pi.basisFun F₂ (Fin 28) 15]

def firstOrderLocalKernelSpace : Submodule F₂ FirstOrderPairCoeff :=
  Submodule.span F₂ (Set.range firstOrderLocalKernelDirections)

theorem firstOrderLocalKernelDirection_mem_ker (i : Fin 3) :
    firstOrderLocalKernelDirections i ∈
      LinearMap.ker firstOrderEnvelopePolarizedMap := by
  rw [LinearMap.mem_ker]
  fin_cases i
  · change firstOrderEnvelopePolarizedMap
      (Pi.basisFun F₂ (Fin 28) 2) = 0
    rw [firstOrderEnvelopePolarizedMap_basis]
    simpa [firstOrderPairWedge, firstOrderPairLeft, firstOrderPairRight,
      exactFirstOrderDirections] using targetCrossWedge_rZero_jZero
  · change firstOrderEnvelopePolarizedMap
      (Pi.basisFun F₂ (Fin 28) 9) = 0
    rw [firstOrderEnvelopePolarizedMap_basis]
    simpa [firstOrderPairWedge, firstOrderPairLeft, firstOrderPairRight,
      exactFirstOrderDirections] using targetCrossWedge_rOne_exactJOne
  · change firstOrderEnvelopePolarizedMap
      (Pi.basisFun F₂ (Fin 28) 15) = 0
    rw [firstOrderEnvelopePolarizedMap_basis]
    simpa [firstOrderPairWedge, firstOrderPairLeft, firstOrderPairRight,
      exactFirstOrderDirections] using
      targetCrossWedge_rInfinity_exactJInfinity

theorem firstOrderLocalKernelSpace_le_ker :
    firstOrderLocalKernelSpace ≤
      LinearMap.ker firstOrderEnvelopePolarizedMap := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact firstOrderLocalKernelDirection_mem_ker i

private theorem firstOrderPairWedge_pivot11 (k : Fin 28) :
    firstOrderPairWedge k 0 1 2 3 = if k = 11 then 1 else 0 := by
  fin_cases k <;>
    decide

private theorem firstOrderPairWedge_pivot0 (k : Fin 28) :
    firstOrderPairWedge k 0 2 0 2 = if k = 0 then 1 else 0 := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot5 (k : Fin 28) :
    firstOrderPairWedge k 0 1 0 1 =
      (if k = 0 then 1 else 0) + (if k = 5 then 1 else 0) +
        (if k = 11 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot24 (k : Fin 28) :
    firstOrderPairWedge k 0 2 3 4 =
      (if k = 11 then 1 else 0) + (if k = 24 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot23 (k : Fin 28) :
    firstOrderPairWedge k 0 3 2 3 =
      (if k = 23 then 1 else 0) + (if k = 24 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot12 (k : Fin 28) :
    firstOrderPairWedge k 0 1 2 4 =
      (if k = 12 then 1 else 0) + (if k = 23 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot27 (k : Fin 28) :
    firstOrderPairWedge k 0 1 3 4 =
      (if k = 11 then 1 else 0) + (if k = 12 then 1 else 0) +
        (if k = 23 then 1 else 0) + (if k = 24 then 1 else 0) +
          (if k = 27 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot8 (k : Fin 28) :
    firstOrderPairWedge k 0 1 1 3 =
      (if k = 8 then 1 else 0) + (if k = 11 then 1 else 0) +
        (if k = 12 then 1 else 0) + (if k = 23 then 1 else 0) +
          (if k = 27 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot3 (k : Fin 28) :
    firstOrderPairWedge k 0 1 0 4 =
      (if k = 0 then 1 else 0) + (if k = 3 then 1 else 0) +
        (if k = 5 then 1 else 0) + (if k = 8 then 1 else 0) +
          (if k = 11 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot6 (k : Fin 28) :
    firstOrderPairWedge k 0 2 0 4 =
      (if k = 0 then 1 else 0) + (if k = 6 then 1 else 0) +
        (if k = 11 then 1 else 0) + (if k = 12 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot20 (k : Fin 28) :
    firstOrderPairWedge k 0 1 0 2 =
      (if k = 0 then 1 else 0) + (if k = 3 then 1 else 0) +
        (if k = 6 then 1 else 0) + (if k = 8 then 1 else 0) +
          (if k = 11 then 1 else 0) + (if k = 12 then 1 else 0) +
            (if k = 20 then 1 else 0) + (if k = 23 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot18 (k : Fin 28) :
    firstOrderPairWedge k 0 1 1 4 =
      (if k = 8 then 1 else 0) + (if k = 18 then 1 else 0) +
        (if k = 20 then 1 else 0) + (if k = 23 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot21 (k : Fin 28) :
    firstOrderPairWedge k 0 1 0 3 =
      (if k = 0 then 1 else 0) + (if k = 8 then 1 else 0) +
        (if k = 12 then 1 else 0) + (if k = 18 then 1 else 0) +
          (if k = 21 then 1 else 0) + (if k = 24 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot10 (k : Fin 28) :
    firstOrderPairWedge k 1 3 3 4 =
      (if k = 10 then 1 else 0) + (if k = 11 then 1 else 0) +
        (if k = 12 then 1 else 0) + (if k = 24 then 1 else 0) +
          (if k = 27 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot4 (k : Fin 28) :
    firstOrderPairWedge k 0 3 0 4 =
      (if k = 0 then 1 else 0) + (if k = 3 then 1 else 0) +
        (if k = 4 then 1 else 0) + (if k = 10 then 1 else 0) +
          (if k = 12 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot25 (k : Fin 28) :
    firstOrderPairWedge k 0 3 2 4 =
      (if k = 10 then 1 else 0) + (if k = 23 then 1 else 0) +
        (if k = 25 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot22 (k : Fin 28) :
    firstOrderPairWedge k 2 3 3 4 =
      (if k = 10 then 1 else 0) + (if k = 11 then 1 else 0) +
        (if k = 22 then 1 else 0) + (if k = 23 then 1 else 0) +
          (if k = 25 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot19 (k : Fin 28) :
    firstOrderPairWedge k 0 3 1 4 =
      (if k = 8 then 1 else 0) + (if k = 10 then 1 else 0) +
        (if k = 18 then 1 else 0) + (if k = 19 then 1 else 0) +
          (if k = 22 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot26 (k : Fin 28) :
    firstOrderPairWedge k 0 3 3 4 =
      (if k = 10 then 1 else 0) + (if k = 22 then 1 else 0) +
        (if k = 24 then 1 else 0) + (if k = 26 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot7 (k : Fin 28) :
    firstOrderPairWedge k 1 4 3 4 =
      (if k = 7 then 1 else 0) + (if k = 10 then 1 else 0) +
        (if k = 11 then 1 else 0) + (if k = 22 then 1 else 0) +
          (if k = 23 then 1 else 0) + (if k = 25 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot1 (k : Fin 28) :
    firstOrderPairWedge k 0 4 0 4 =
      (if k = 0 then 1 else 0) + (if k = 1 then 1 else 0) +
        (if k = 7 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot16 (k : Fin 28) :
    firstOrderPairWedge k 0 4 2 4 =
      (if k = 7 then 1 else 0) + (if k = 11 then 1 else 0) +
        (if k = 12 then 1 else 0) + (if k = 16 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot14 (k : Fin 28) :
    firstOrderPairWedge k 2 4 3 4 =
      (if k = 7 then 1 else 0) + (if k = 10 then 1 else 0) +
        (if k = 11 then 1 else 0) + (if k = 12 then 1 else 0) +
          (if k = 14 then 1 else 0) + (if k = 16 then 1 else 0) +
            (if k = 24 then 1 else 0) + (if k = 26 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot13 (k : Fin 28) :
    firstOrderPairWedge k 0 4 1 4 =
      (if k = 7 then 1 else 0) + (if k = 8 then 1 else 0) +
        (if k = 11 then 1 else 0) + (if k = 13 then 1 else 0) +
          (if k = 14 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderPairWedge_pivot17 (k : Fin 28) :
    firstOrderPairWedge k 0 4 3 4 =
      (if k = 7 then 1 else 0) + (if k = 10 then 1 else 0) +
        (if k = 12 then 1 else 0) + (if k = 14 then 1 else 0) +
          (if k = 17 then 1 else 0) := by
  fin_cases k <;> decide

private theorem firstOrderEnvelopePolarized_pivot11
    (α : FirstOrderPairCoeff)
    (h : firstOrderEnvelopePolarizedMap α = 0) :
    α 11 = 0 := by
  have hc := congrFun (congrFun (congrFun (congrFun h 0) 1) 2) 3
  change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 2 3 = 0 at hc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    firstOrderPairWedge_pivot11] at hc
  simpa [Fin.sum_univ_succ] using hc

/-- The reverse inclusion in the polarized first-order kernel calculation.
Each displayed coordinate is a sparse row pivot; the only unpivoted columns
are the three local rotations `2`, `9`, and `15`. -/
theorem firstOrderEnvelopePolarized_ker_le_local :
    LinearMap.ker firstOrderEnvelopePolarizedMap ≤
      firstOrderLocalKernelSpace := by
  intro α hα
  have hmap : firstOrderEnvelopePolarizedMap α = 0 :=
    (LinearMap.mem_ker).mp hα
  have h11 : α 11 = 0 :=
    firstOrderEnvelopePolarized_pivot11 α hmap
  have h0 : α 0 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 2) 0) 2
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 2 0 2 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot0] at hc
    simpa [Fin.sum_univ_succ] using hc
  have h5 : α 5 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 1) 0) 1
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 0 1 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot5] at hc
    simpa [Fin.sum_univ_succ, h0, h11] using hc
  have h24 : α 24 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 2) 3) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 2 3 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot24] at hc
    simpa [Fin.sum_univ_succ, h11] using hc
  have h23 : α 23 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 3) 2) 3
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 3 2 3 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot23] at hc
    simpa [Fin.sum_univ_succ, h24] using hc
  have h12 : α 12 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 1) 2) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 2 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot12] at hc
    simpa [Fin.sum_univ_succ, h23] using hc
  have h27 : α 27 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 1) 3) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 3 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot27] at hc
    simpa [Fin.sum_univ_succ, h11, h12, h23, h24] using hc
  have h8 : α 8 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 1) 1) 3
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 1 3 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot8] at hc
    simpa [Fin.sum_univ_succ, h11, h12, h23, h27] using hc
  have h3 : α 3 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 1) 0) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 0 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot3] at hc
    simpa [Fin.sum_univ_succ, h0, h5, h8, h11] using hc
  have h6 : α 6 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 2) 0) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 2 0 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot6] at hc
    simpa [Fin.sum_univ_succ, h0, h11, h12] using hc
  have h20 : α 20 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 1) 0) 2
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 0 2 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot20] at hc
    simpa [Fin.sum_univ_succ, h0, h3, h6, h8, h11, h12, h23] using hc
  have h18 : α 18 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 1) 1) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 1 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot18] at hc
    simpa [Fin.sum_univ_succ, h8, h20, h23] using hc
  have h21 : α 21 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 1) 0) 3
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 1 0 3 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot21] at hc
    simpa [Fin.sum_univ_succ, h0, h8, h12, h18, h24] using hc
  have h10 : α 10 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 1) 3) 3) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 1 3 3 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot10] at hc
    simpa [Fin.sum_univ_succ, h11, h12, h24, h27] using hc
  have h4 : α 4 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 3) 0) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 3 0 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot4] at hc
    simpa [Fin.sum_univ_succ, h0, h3, h10, h12] using hc
  have h25 : α 25 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 3) 2) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 3 2 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot25] at hc
    simpa [Fin.sum_univ_succ, h10, h23] using hc
  have h22 : α 22 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 2) 3) 3) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 2 3 3 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot22] at hc
    simpa [Fin.sum_univ_succ, h10, h11, h23, h25] using hc
  have h19 : α 19 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 3) 1) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 3 1 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot19] at hc
    simpa [Fin.sum_univ_succ, h8, h10, h18, h22] using hc
  have h26 : α 26 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 3) 3) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 3 3 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot26] at hc
    simpa [Fin.sum_univ_succ, h10, h22, h24] using hc
  have h7 : α 7 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 1) 4) 3) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 1 4 3 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot7] at hc
    simpa [Fin.sum_univ_succ, h10, h11, h22, h23, h25] using hc
  have h1 : α 1 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 4) 0) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 4 0 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot1] at hc
    simpa [Fin.sum_univ_succ, h0, h7] using hc
  have h16 : α 16 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 4) 2) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 4 2 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot16] at hc
    simpa [Fin.sum_univ_succ, h7, h11, h12] using hc
  have h14 : α 14 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 2) 4) 3) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 2 4 3 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot14] at hc
    simpa [Fin.sum_univ_succ, h7, h10, h11, h12, h16, h24, h26] using hc
  have h13 : α 13 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 4) 1) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 4 1 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot13] at hc
    simpa [Fin.sum_univ_succ, h7, h8, h11, h14] using hc
  have h17 : α 17 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun hmap 0) 4) 3) 4
    change (∑ k : Fin 28, α k • firstOrderPairWedge k) 0 4 3 4 = 0 at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      firstOrderPairWedge_pivot17] at hc
    simpa [Fin.sum_univ_succ, h7, h10, h12, h14] using hc
  have heq : α =
      α 2 • Pi.basisFun F₂ (Fin 28) 2 +
        α 9 • Pi.basisFun F₂ (Fin 28) 9 +
          α 15 • Pi.basisFun F₂ (Fin 28) 15 := by
    funext k
    fin_cases k <;>
      simp [Pi.basisFun, h0, h1, h3, h4, h5, h6, h7, h8,
        h10, h11, h12, h13, h14, h16, h17, h18, h19, h20,
        h21, h22, h23, h24, h25, h26, h27]
  have hb2 : Pi.basisFun F₂ (Fin 28) 2 ∈ firstOrderLocalKernelSpace := by
    apply Submodule.subset_span
    exact ⟨0, rfl⟩
  have hb9 : Pi.basisFun F₂ (Fin 28) 9 ∈ firstOrderLocalKernelSpace := by
    apply Submodule.subset_span
    exact ⟨1, rfl⟩
  have hb15 : Pi.basisFun F₂ (Fin 28) 15 ∈ firstOrderLocalKernelSpace := by
    apply Submodule.subset_span
    exact ⟨2, rfl⟩
  rw [heq]
  exact firstOrderLocalKernelSpace.add_mem
    (firstOrderLocalKernelSpace.add_mem
      (firstOrderLocalKernelSpace.smul_mem _ hb2)
      (firstOrderLocalKernelSpace.smul_mem _ hb9))
    (firstOrderLocalKernelSpace.smul_mem _ hb15)

/-- Manuscript equation (11.3): the only polarized relations among the eight
exact first-order target directions are the three local value--jet rotations. -/
theorem firstOrderEnvelopePolarized_ker_eq_local :
    LinearMap.ker firstOrderEnvelopePolarizedMap =
      firstOrderLocalKernelSpace :=
  le_antisymm firstOrderEnvelopePolarized_ker_le_local
    firstOrderLocalKernelSpace_le_ker

/-! ## Decomposable elements of the kernel -/

/-- Pluecker coordinates of the plane generated by two vectors in the exact
first-order basis. -/
def firstOrderPlaneCoeff (x y : Fin 8 → F₂) : FirstOrderPairCoeff :=
  fun k =>
    x (firstOrderPairLeft k) * y (firstOrderPairRight k) +
      x (firstOrderPairRight k) * y (firstOrderPairLeft k)

private theorem firstOrderPlaneCoeff_plucker_0134 (x y : Fin 8 → F₂) :
    firstOrderPlaneCoeff x y 0 * firstOrderPlaneCoeff x y 18 +
      firstOrderPlaneCoeff x y 2 * firstOrderPlaneCoeff x y 9 +
        firstOrderPlaneCoeff x y 3 * firstOrderPlaneCoeff x y 8 = 0 := by
  simp [firstOrderPlaneCoeff, firstOrderPairLeft, firstOrderPairRight]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

private theorem firstOrderPlaneCoeff_plucker_0235 (x y : Fin 8 → F₂) :
    firstOrderPlaneCoeff x y 1 * firstOrderPlaneCoeff x y 19 +
      firstOrderPlaneCoeff x y 2 * firstOrderPlaneCoeff x y 15 +
        firstOrderPlaneCoeff x y 4 * firstOrderPlaneCoeff x y 13 = 0 := by
  simp [firstOrderPlaneCoeff, firstOrderPairLeft, firstOrderPairRight]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

private theorem firstOrderPlaneCoeff_plucker_1245 (x y : Fin 8 → F₂) :
    firstOrderPlaneCoeff x y 7 * firstOrderPlaneCoeff x y 22 +
      firstOrderPlaneCoeff x y 9 * firstOrderPlaneCoeff x y 15 +
        firstOrderPlaneCoeff x y 10 * firstOrderPlaneCoeff x y 14 = 0 := by
  simp [firstOrderPlaneCoeff, firstOrderPairLeft, firstOrderPairRight]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Coordinate normal form for an arbitrary member of the local kernel. -/
theorem firstOrderLocalKernelSpace_normalForm
    {α : FirstOrderPairCoeff} (hα : α ∈ firstOrderLocalKernelSpace) :
    ∃ a b c : F₂,
      α = a • Pi.basisFun F₂ (Fin 28) 2 +
        b • Pi.basisFun F₂ (Fin 28) 9 +
          c • Pi.basisFun F₂ (Fin 28) 15 := by
  rcases (Submodule.mem_span_range_iff_exists_fun
      (R := F₂) (v := firstOrderLocalKernelDirections) (x := α)).mp hα with
    ⟨s, hs⟩
  refine ⟨s 0, s 1, s 2, ?_⟩
  rw [← hs]
  funext k
  fin_cases k <;>
    simp [firstOrderLocalKernelDirections, Pi.basisFun,
      Fin.sum_univ_succ]

/-- A decomposable element of the polarized kernel is zero or one of the
three rational local rotations.  The three Pluecker equations above exclude
chains of two rotations and the putative weight-three element. -/
theorem firstOrderPlaneCoeff_kernel_classification
    (x y : Fin 8 → F₂)
    (hzero : firstOrderEnvelopePolarizedMap
      (firstOrderPlaneCoeff x y) = 0) :
    firstOrderPlaneCoeff x y = 0 ∨
      firstOrderPlaneCoeff x y = Pi.basisFun F₂ (Fin 28) 2 ∨
      firstOrderPlaneCoeff x y = Pi.basisFun F₂ (Fin 28) 9 ∨
      firstOrderPlaneCoeff x y = Pi.basisFun F₂ (Fin 28) 15 := by
  have hmem : firstOrderPlaneCoeff x y ∈ firstOrderLocalKernelSpace := by
    rw [← firstOrderEnvelopePolarized_ker_eq_local,
      LinearMap.mem_ker]
    exact hzero
  rcases firstOrderLocalKernelSpace_normalForm hmem with ⟨a, b, c, habc⟩
  have hab := firstOrderPlaneCoeff_plucker_0134 x y
  have hac := firstOrderPlaneCoeff_plucker_0235 x y
  have hbc := firstOrderPlaneCoeff_plucker_1245 x y
  rw [habc] at hab hac hbc ⊢
  simp [Pi.basisFun] at hab hac hbc
  rcases f2_eq_zero_or_one a with rfl | rfl <;>
    rcases f2_eq_zero_or_one b with rfl | rfl <;>
      rcases f2_eq_zero_or_one c with rfl | rfl <;>
        simp_all

/-- Nonzero coordinate form of the preceding classification: the only
independent zero-wedge planes are the three rational value--jet planes. -/
theorem firstOrderPlaneCoeff_eq_local_of_kernel_of_ne_zero
    (x y : Fin 8 → F₂)
    (hzero : firstOrderEnvelopePolarizedMap
      (firstOrderPlaneCoeff x y) = 0)
    (hne : firstOrderPlaneCoeff x y ≠ 0) :
    ∃ i : Fin 3,
      firstOrderPlaneCoeff x y = firstOrderLocalKernelDirections i := by
  rcases firstOrderPlaneCoeff_kernel_classification x y hzero with
    h | h | h | h
  · exact (hne h).elim
  · exact ⟨0, by simpa [firstOrderLocalKernelDirections] using h⟩
  · exact ⟨1, by simpa [firstOrderLocalKernelDirections] using h⟩
  · exact ⟨2, by simpa [firstOrderLocalKernelDirections] using h⟩

end

end N5
end UnrestrictedBooleanMul
