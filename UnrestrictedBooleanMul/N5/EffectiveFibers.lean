import UnrestrictedBooleanMul.N5.LocalKlein

/-!
# The closed-place quotient atlas

This module embeds the four local Klein quotients into the global quadratic
quotient.  The canonical remainder from `QuadraticSpace` makes equality in
the quotient testable by ordinary squarefree coordinates.  The atlas is
ordered as `2P_0, 2P_1, 2P_infinity, P_*`.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Evaluation and first-Hasse-jet coordinates at the rational point one. -/
def aOneEval : LinearForm := ∑ i : Fin 5, aLinear i
def aOneJet : LinearForm := aLinear 1 + aLinear 3
def bOneEval : LinearForm := ∑ i : Fin 5, bLinear i
def bOneJet : LinearForm := bLinear 1 + bLinear 3

/-- Residue coordinates modulo `z^2+z+1` on the two input sides. -/
def aStarZero : LinearForm := aLinear 0 + aLinear 2 + aLinear 3
def aStarOne : LinearForm := aLinear 1 + aLinear 2 + aLinear 4
def bStarZero : LinearForm := bLinear 0 + bLinear 2 + bLinear 3
def bStarOne : LinearForm := bLinear 1 + bLinear 2 + bLinear 4

/-- Ordered bases `(x,x',y,y')` or `(u,v,U,V)` for the four local
four-spaces. -/
def closedPlaceLocalBasis : Fin 4 → Fin 4 → LinearForm :=
  ![![aLinear 0, aLinear 1, bLinear 0, bLinear 1],
    ![aOneEval, aOneJet, bOneEval, bOneJet],
    ![aLinear 4, aLinear 3, bLinear 4, bLinear 3],
    ![aStarZero, aStarOne, bStarZero, bStarOne]]

/-- Coordinate pairs `(01,02,03,12,13,23)` in a local exterior square. -/
def localKleinPair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Embed six local Pluecker coordinates in the global 45-dimensional
squarefree quadratic space. -/
def localTwoForm (place : Fin 4) (p : LocalKleinCoord) : TwoForm :=
  ∑ s : Fin 6, p s •
    squarefreeWedge
      (closedPlaceLocalBasis place (localKleinPair s).1)
      (closedPlaceLocalBasis place (localKleinPair s).2)

/-- The local exterior-square embedding is linear in its six Pluecker
coordinates. -/
def localTwoFormLinear (place : Fin 4) : LocalKleinCoord →ₗ[F₂] TwoForm where
  toFun := localTwoForm place
  map_add' p q := by
    ext s
    simp [localTwoForm, add_smul, Finset.sum_add_distrib]
  map_smul' a p := by
    ext s
    simp only [localTwoForm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_assoc]

/-- Canonical quotient section for a doubled rational place. -/
def rationalCanonicalCoord (q : LocalKleinParam) : LocalKleinCoord :=
  ![q 0, 0, q 1, 0, q 2, q 3]

/-- Canonical quotient section for the degree-two place. -/
def degreeTwoCanonicalCoord (q : LocalKleinParam) : LocalKleinCoord :=
  ![q 0, 0, 0, q 1, q 2, q 3]

def closedPlaceCanonicalCoord (place : Fin 4) (q : LocalKleinParam) :
    LocalKleinCoord :=
  ![rationalCanonicalCoord q, rationalCanonicalCoord q,
    rationalCanonicalCoord q, degreeTwoCanonicalCoord q] place

theorem closedPlaceCanonicalCoord_basis_sum (place : Fin 4)
    (q : LocalKleinParam) :
    closedPlaceCanonicalCoord place q =
      ∑ i : Fin 4, q i •
        closedPlaceCanonicalCoord place ((Pi.basisFun F₂ (Fin 4)) i) := by
  funext s
  fin_cases place <;> fin_cases s <;>
    simp [closedPlaceCanonicalCoord, rationalCanonicalCoord,
      degreeTwoCanonicalCoord, Pi.basisFun, Pi.single_apply]

/-- A chosen global lift of a local quotient parameter. -/
def closedPlaceLift (place : Fin 4) (q : LocalKleinParam) : TwoForm :=
  localTwoForm place (closedPlaceCanonicalCoord place q)

/-- Expansion of a local lift in its four canonical atlas directions. -/
theorem closedPlaceLift_basis_sum (place : Fin 4) (q : LocalKleinParam) :
    closedPlaceLift place q =
      ∑ i : Fin 4, q i •
        closedPlaceLift place ((Pi.basisFun F₂ (Fin 4)) i) := by
  change localTwoFormLinear place (closedPlaceCanonicalCoord place q) = _
  rw [closedPlaceCanonicalCoord_basis_sum, map_sum]
  simp only [map_smul]
  rfl

/-- Its global quadratic quotient point. -/
def closedPlaceQuotientPoint (place : Fin 4) (q : LocalKleinParam) :
    QuadraticQuotient :=
  quadraticQuotientProjection (closedPlaceLift place q)

/-- The sixteen global quotient directions supplied by the four local
four-dimensional quotient sections. -/
def closedPlaceAtlasDirection (i : Fin 4 × Fin 4) : TwoForm :=
  quotientRemainder
    (closedPlaceLift i.1 ((Pi.basisFun F₂ (Fin 4)) i.2))

/-- Canonical remainder coordinates of an arbitrary local quotient lift. -/
theorem quotientRemainder_closedPlaceLift (place : Fin 4)
    (q : LocalKleinParam) :
    quotientRemainder (closedPlaceLift place q) =
      ∑ i : Fin 4, q i • closedPlaceAtlasDirection (place, i) := by
  rw [closedPlaceLift_basis_sum, map_sum]
  simp [closedPlaceAtlasDirection]

/-- Flatten the `(place,coordinate)` atlas index in row-major order. -/
def atlasFlatIndex (i : Fin 4 × Fin 4) : Fin 16 :=
  ⟨4 * i.1.val + i.2.val, by omega⟩

/-- Inverse row-major decomposition of a sixteen-coordinate atlas index. -/
def atlasUnflatIndex (i : Fin 16) : Fin 4 × Fin 4 :=
  (⟨i.val / 4, by omega⟩, ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩)

/-- Row-major indexing is an equivalence between the four local four-spaces
and sixteen flat coordinates. -/
def atlasIndexEquiv : (Fin 4 × Fin 4) ≃ Fin 16 where
  toFun := atlasFlatIndex
  invFun := atlasUnflatIndex
  left_inv i := by
    rcases i with ⟨ip, ic⟩
    apply Prod.ext <;> apply Fin.ext
    all_goals
      simp [atlasFlatIndex, atlasUnflatIndex] <;> omega
  right_inv i := by
    apply Fin.ext
    simp [atlasFlatIndex, atlasUnflatIndex]
    omega

/-- Sixteen coordinate probes used by the atlas rank certificate. -/
def atlasProbePair : Fin 16 → Fin 10 × Fin 10 :=
  ![(0, 1), (0, 2), (0, 3), (1, 5),
    (1, 6), (1, 7), (1, 8), (2, 5),
    (2, 6), (3, 4), (3, 8), (4, 8),
    (5, 6), (5, 7), (5, 8), (8, 9)]

def atlasProbe (i : Fin 16) : QuadraticIndex 10 :=
  ![quadraticPair (aCoord 0) (aCoord 1) (by decide),
    quadraticPair (aCoord 0) (aCoord 2) (by decide),
    quadraticPair (aCoord 0) (aCoord 3) (by decide),
    quadraticPair (aCoord 1) (bCoord 0) (aCoord_ne_bCoord 1 0),
    quadraticPair (aCoord 1) (bCoord 1) (aCoord_ne_bCoord 1 1),
    quadraticPair (aCoord 1) (bCoord 2) (aCoord_ne_bCoord 1 2),
    quadraticPair (aCoord 1) (bCoord 3) (aCoord_ne_bCoord 1 3),
    quadraticPair (aCoord 2) (bCoord 0) (aCoord_ne_bCoord 2 0),
    quadraticPair (aCoord 2) (bCoord 1) (aCoord_ne_bCoord 2 1),
    quadraticPair (aCoord 3) (aCoord 4) (by decide),
    quadraticPair (aCoord 3) (bCoord 3) (aCoord_ne_bCoord 3 3),
    quadraticPair (aCoord 4) (bCoord 3) (aCoord_ne_bCoord 4 3),
    quadraticPair (bCoord 0) (bCoord 1) (by decide),
    quadraticPair (bCoord 0) (bCoord 2) (by decide),
    quadraticPair (bCoord 0) (bCoord 3) (by decide),
    quadraticPair (bCoord 3) (bCoord 4) (by decide)] i

/-- The 16-by-16 probe matrix, recorded as an algebraic certificate. -/
def atlasProbeMatrixData : Matrix (Fin 16) (Fin 16) F₂ :=
  ![![1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
    ![0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0],
    ![0,0,1,0,0,1,1,0,0,0,0,0,0,0,1,0],
    ![0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0],
    ![0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0],
    ![0,0,0,0,0,1,1,0,0,0,1,0,0,0,1,0],
    ![0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0],
    ![0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1]]

/-- A displayed inverse for `atlasProbeMatrixData`. -/
def atlasProbeMatrixInverse : Matrix (Fin 16) (Fin 16) F₂ :=
  ![![1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,1,1,1,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,1,0,1,1,0,0,0,0,0,0,0],
    ![0,0,0,0,0,1,1,0,1,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0],
    ![0,0,0,0,0,1,0,0,1,0,0,1,0,0,0,0],
    ![0,0,0,0,0,0,1,1,1,0,1,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1],
    ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0]]

/-- Kernel-checked inverse certificate for the atlas probe matrix. -/
theorem atlasProbeMatrixInverse_mul :
    atlasProbeMatrixInverse * atlasProbeMatrixData = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    decide

set_option maxHeartbeats 400000

local macro "finish_atlas_probe_row" : tactic =>
  `(tactic|
    simp [closedPlaceAtlasDirection, closedPlaceLift, localTwoForm,
      closedPlaceCanonicalCoord, rationalCanonicalCoord,
      degreeTwoCanonicalCoord, closedPlaceLocalBasis, localKleinPair,
      atlasProbe, atlasFlatIndex,
      atlasProbeMatrixData, aOneEval, aOneJet, bOneEval, bOneJet,
      aStarZero, aStarOne, bStarZero, bStarOne,
      hankelIndex, anchorLeftIndex, anchorRightIndex,
      aLinear, bLinear, Pi.basisFun, Pi.single_apply,
      squarefreeWedge_pair, Fin.sum_univ_succ] <;> decide)

private theorem closedPlaceAtlas_probe_row_0 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 0) =
      atlasProbeMatrixData 0 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_1 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 1) =
      atlasProbeMatrixData 1 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_2 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 2) =
      atlasProbeMatrixData 2 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_3 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 3) =
      atlasProbeMatrixData 3 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_4 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 4) =
      atlasProbeMatrixData 4 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_5 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 5) =
      atlasProbeMatrixData 5 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_6 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 6) =
      atlasProbeMatrixData 6 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_7 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 7) =
      atlasProbeMatrixData 7 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_8 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 8) =
      atlasProbeMatrixData 8 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_9 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 9) =
      atlasProbeMatrixData 9 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_10 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 10) =
      atlasProbeMatrixData 10 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_11 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 11) =
      atlasProbeMatrixData 11 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_12 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 12) =
      atlasProbeMatrixData 12 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_13 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 13) =
      atlasProbeMatrixData 13 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_14 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 14) =
      atlasProbeMatrixData 14 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

private theorem closedPlaceAtlas_probe_row_15 (c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe 15) =
      atlasProbeMatrixData 15 (atlasFlatIndex c) := by
  rcases c with ⟨cp, ci⟩
  fin_cases cp <;> fin_cases ci <;> finish_atlas_probe_row

/-- Every displayed matrix entry is the corresponding coordinate of the
global closed-place atlas direction.  This is the exact Hermite rank
certificate, proved from the named local bases rather than assumed as a
table. -/
theorem closedPlaceAtlas_probe_table (r c : Fin 4 × Fin 4) :
    closedPlaceAtlasDirection c (atlasProbe (atlasFlatIndex r)) =
      atlasProbeMatrixData (atlasFlatIndex r) (atlasFlatIndex c) := by
  rcases r with ⟨rp, ri⟩
  fin_cases rp <;> fin_cases ri
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_0 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_1 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_2 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_3 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_4 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_5 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_6 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_7 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_8 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_9 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_10 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_11 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_12 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_13 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_14 c
  · simpa [atlasFlatIndex] using closedPlaceAtlas_probe_row_15 c

/-- The same atlas family with a flat sixteen-element index. -/
def flatAtlasDirection (i : Fin 16) : TwoForm :=
  closedPlaceAtlasDirection (atlasIndexEquiv.symm i)

@[simp] theorem atlasFlatIndex_equiv_symm (i : Fin 16) :
    atlasFlatIndex (atlasIndexEquiv.symm i) = i :=
  atlasIndexEquiv.apply_symm_apply i

@[simp] theorem flatAtlasDirection_equiv (i : Fin 4 × Fin 4) :
    flatAtlasDirection (atlasIndexEquiv i) = closedPlaceAtlasDirection i := by
  simp [flatAtlasDirection]

theorem flatAtlas_probe_table (r c : Fin 16) :
    flatAtlasDirection c (atlasProbe r) = atlasProbeMatrixData r c := by
  simpa only [flatAtlasDirection, atlasFlatIndex_equiv_symm] using
    closedPlaceAtlas_probe_table (atlasIndexEquiv.symm r) (atlasIndexEquiv.symm c)

/-- The inverse certificate proves that all sixteen local quotient directions
are independent in the global quadratic quotient complement. -/
theorem flatAtlasDirection_linearIndependent :
    LinearIndependent F₂ flatAtlasDirection := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  have hM : Matrix.mulVec atlasProbeMatrixData f = 0 := by
    funext r
    have hr := congrFun h (atlasProbe r)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hr
    simpa [Matrix.mulVec, dotProduct, flatAtlas_probe_table, mul_comm] using hr
  have hN := congrArg (fun v => Matrix.mulVec atlasProbeMatrixInverse v) hM
  have hi := congrFun hN i
  simpa [Matrix.mulVec_mulVec, atlasProbeMatrixInverse_mul] using hi

/-- The four closed-place quotient charts occupy a direct sixteen-dimensional
sum in the global quotient complement. -/
theorem closedPlaceAtlasDirection_linearIndependent :
    LinearIndependent F₂ closedPlaceAtlasDirection := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  let g : Fin 16 → F₂ := fun k => f (atlasIndexEquiv.symm k)
  have hg : ∑ k, g k • flatAtlasDirection k = 0 := by
    calc
      ∑ k, g k • flatAtlasDirection k =
          ∑ k, f (atlasIndexEquiv.symm k) •
            closedPlaceAtlasDirection (atlasIndexEquiv.symm k) := by
              rfl
      _ = ∑ j, f j • closedPlaceAtlasDirection j :=
        atlasIndexEquiv.symm.sum_comp
          (fun j => f j • closedPlaceAtlasDirection j)
      _ = 0 := h
  have hi := Fintype.linearIndependent_iff.mp
    flatAtlasDirection_linearIndependent g hg (atlasIndexEquiv i)
  simpa [g] using hi

/-- Coefficient vector of one four-dimensional local chart inside the global
sixteen-direction atlas. -/
def atlasCoefficient (place : Fin 4) (q : LocalKleinParam)
    (c : Fin 4 × Fin 4) : F₂ :=
  if c.1 = place then q c.2 else 0

theorem atlasCoefficient_sum (place : Fin 4) (q : LocalKleinParam) :
    ∑ c : Fin 4 × Fin 4,
        atlasCoefficient place q c • closedPlaceAtlasDirection c =
      ∑ i : Fin 4, q i • closedPlaceAtlasDirection (place, i) := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single place]
  · simp [atlasCoefficient]
  · intro other hne
    simp [atlasCoefficient, hne]

/-- Equality of global quotient points is exactly equality of their sixteen
atlas coefficients. -/
theorem closedPlaceQuotientPoint_eq_iff_atlasCoefficient_eq
    (place place' : Fin 4) (q q' : LocalKleinParam) :
    closedPlaceQuotientPoint place q = closedPlaceQuotientPoint place' q' ↔
      atlasCoefficient place q = atlasCoefficient place' q' := by
  constructor
  · intro h
    have hrem : quotientRemainder (closedPlaceLift place q) =
        quotientRemainder (closedPlaceLift place' q') :=
      (quadraticQuotientProjection_eq_iff_remainder_eq _ _).1 (by
        simpa [closedPlaceQuotientPoint] using h)
    rw [quotientRemainder_closedPlaceLift,
      quotientRemainder_closedPlaceLift] at hrem
    have hzero :
        ∑ c : Fin 4 × Fin 4,
            (atlasCoefficient place q c - atlasCoefficient place' q' c) •
              closedPlaceAtlasDirection c = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, atlasCoefficient_sum,
        atlasCoefficient_sum, hrem, sub_self]
    funext c
    have hc := Fintype.linearIndependent_iff.mp
      closedPlaceAtlasDirection_linearIndependent _ hzero c
    exact sub_eq_zero.mp hc
  · intro hcoeff
    apply (quadraticQuotientProjection_eq_iff_remainder_eq _ _).2
    rw [quotientRemainder_closedPlaceLift,
      quotientRemainder_closedPlaceLift,
      ← atlasCoefficient_sum, ← atlasCoefficient_sum, hcoeff]

/-- Effective local quotient parameters at one of the four closed places. -/
def effectiveParamsAt (place : Fin 4) : Finset LocalKleinParam :=
  if place = 3 then degreeTwoEffectiveParams else rationalEffectiveParams

abbrev EffectiveParamAt (place : Fin 4) :=
  {q : LocalKleinParam // q ∈ effectiveParamsAt place}

/-- Disjoint union of the three rational and one degree-two effective charts. -/
abbrev ClosedPlaceEffectiveParam :=
  Σ place : Fin 4, EffectiveParamAt place

theorem effectiveParamsAt_ne_zero (place : Fin 4) {q : LocalKleinParam}
    (hq : q ∈ effectiveParamsAt place) : q ≠ 0 := by
  intro hzero
  subst q
  fin_cases place <;>
    simp [effectiveParamsAt, rationalEffectiveParams,
      degreeTwoEffectiveParams, RationalLocalEffective,
      DegreeTwoLocalEffective] at hq

theorem closedPlaceEffectiveParam_card :
    Fintype.card ClosedPlaceEffectiveParam = 43 := by
  rw [Fintype.card_sigma]
  change (∑ place : Fin 4, (effectiveParamsAt place).card) = 43
  simp [effectiveParamsAt, rationalEffectiveParams_card,
    degreeTwoEffectiveParams_card, Fin.sum_univ_succ]

/-- Global quotient point represented by an effective local parameter. -/
def closedPlaceEffectivePoint (x : ClosedPlaceEffectiveParam) :
    QuadraticQuotient :=
  closedPlaceQuotientPoint x.1 x.2.1

theorem closedPlaceEffectivePoint_injective :
    Function.Injective closedPlaceEffectivePoint := by
  rintro ⟨place, ⟨q, hq⟩⟩ ⟨place', ⟨q', hq'⟩⟩ hpoint
  have hcoeff :=
    (closedPlaceQuotientPoint_eq_iff_atlasCoefficient_eq
      place place' q q').1 hpoint
  have hplace : place = place' := by
    by_contra hne
    have hqzero : q = 0 := by
      funext i
      have hi := congrFun hcoeff (place, i)
      simpa [atlasCoefficient, hne] using hi
    exact effectiveParamsAt_ne_zero place hq hqzero
  subst place'
  have hqq : q = q' := by
    funext i
    have hi := congrFun hcoeff (place, i)
    simpa [atlasCoefficient] using hi
  subst q'
  rfl

/-- The explicitly embedded effective closed-place quotient points. -/
noncomputable def effectiveFiberAtlas : Finset QuadraticQuotient := by
  classical
  exact Finset.univ.image closedPlaceEffectivePoint

/-- The four effective local charts give exactly 43 distinct global quotient
points. -/
theorem effectiveFiberAtlas_card : effectiveFiberAtlas.card = 43 := by
  classical
  rw [effectiveFiberAtlas,
    Finset.card_image_of_injective _ closedPlaceEffectivePoint_injective,
    Finset.card_univ, closedPlaceEffectiveParam_card]

end

end N5
end UnrestrictedBooleanMul
