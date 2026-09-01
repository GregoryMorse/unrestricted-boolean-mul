import UnrestrictedBooleanMul.N5.ThreePlaceDegreeTwo

/-!
# Explicit rational-place symmetries

Translation `t ↦ t + 1` and coefficient reversal generate the permutation
group of the three rational places.  This module lifts the substitution
pattern from `N4.PlaceSymmetry` to the ten input coordinates and, crucially,
constructs its exterior-square action on `TwoForm`.  The action is algebraic:
it is a finite sum of transported basis wedges, not an enumeration of
quotient fibers.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The two generators: translation and reversal, applied in parallel to
the `a` and `b` coefficient blocks. -/
def rationalPlaceInputChange : Fin 2 → Fin 10 → LinearForm :=
  ![
    ![![1,1,1,1,1,0,0,0,0,0],
      ![0,1,0,1,0,0,0,0,0,0],
      ![0,0,1,1,0,0,0,0,0,0],
      ![0,0,0,1,0,0,0,0,0,0],
      ![0,0,0,0,1,0,0,0,0,0],
      ![0,0,0,0,0,1,1,1,1,1],
      ![0,0,0,0,0,0,1,0,1,0],
      ![0,0,0,0,0,0,0,1,1,0],
      ![0,0,0,0,0,0,0,0,1,0],
      ![0,0,0,0,0,0,0,0,0,1]],
    ![![0,0,0,0,1,0,0,0,0,0],
      ![0,0,0,1,0,0,0,0,0,0],
      ![0,0,1,0,0,0,0,0,0,0],
      ![0,1,0,0,0,0,0,0,0,0],
      ![1,0,0,0,0,0,0,0,0,0],
      ![0,0,0,0,0,0,0,0,0,1],
      ![0,0,0,0,0,0,0,0,1,0],
      ![0,0,0,0,0,0,0,1,0,0],
      ![0,0,0,0,0,0,1,0,0,0],
      ![0,0,0,0,0,1,0,0,0,0]]]

/-- A chosen pair of endpoints for a squarefree quadratic coordinate. -/
noncomputable def quadraticFirst (s : QuadraticIndex 10) : Fin 10 :=
  Classical.choose (QuadraticIndex.exists_pair s)

noncomputable def quadraticSecond (s : QuadraticIndex 10) : Fin 10 :=
  Classical.choose (Classical.choose_spec (QuadraticIndex.exists_pair s))

theorem quadraticFirst_ne_second (s : QuadraticIndex 10) :
    quadraticFirst s ≠ quadraticSecond s :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec (QuadraticIndex.exists_pair s)))

theorem quadraticPair_chosen (s : QuadraticIndex 10) :
    s = quadraticPair (quadraticFirst s) (quadraticSecond s)
      (quadraticFirst_ne_second s) :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec (QuadraticIndex.exists_pair s)))

private abbrev linearFormBasis : Module.Basis (Fin 10) F₂ LinearForm :=
  Pi.basisFun F₂ (Fin 10)

private abbrev twoFormBasis :
    Module.Basis (QuadraticIndex 10) F₂ TwoForm :=
  Pi.basisFun F₂ (QuadraticIndex 10)

/-- Linear action of a rational-place substitution on input coefficient
forms. -/
def rationalPlaceLinear (θ : Fin 2) : LinearForm →ₗ[F₂] LinearForm :=
  linearFormBasis.constr F₂ (rationalPlaceInputChange θ)

@[simp] theorem rationalPlaceLinear_basis (θ : Fin 2) (i : Fin 10) :
    rationalPlaceLinear θ (linearFormBasis i) =
      rationalPlaceInputChange θ i := by
  exact linearFormBasis.constr_basis F₂ (rationalPlaceInputChange θ) i

theorem rationalPlaceLinear_apply (θ : Fin 2) (u : LinearForm) :
    rationalPlaceLinear θ u =
      ∑ i : Fin 10, u i • rationalPlaceInputChange θ i := by
  have hu : ∑ i : Fin 10, u i • linearFormBasis i = u := by
    simpa [linearFormBasis] using linearFormBasis.sum_repr u
  calc
    rationalPlaceLinear θ u =
        rationalPlaceLinear θ
          (∑ i : Fin 10, u i • linearFormBasis i) := by rw [hu]
    _ = ∑ i : Fin 10, u i • rationalPlaceInputChange θ i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, rationalPlaceLinear_basis]

theorem rationalPlaceLinear_aLinear (θ : Fin 2) (i : Fin 5) :
    rationalPlaceLinear θ (aLinear i) =
      rationalPlaceInputChange θ (aCoord i) := by
  exact rationalPlaceLinear_basis θ (aCoord i)

theorem rationalPlaceLinear_bLinear (θ : Fin 2) (i : Fin 5) :
    rationalPlaceLinear θ (bLinear i) =
      rationalPlaceInputChange θ (bCoord i) := by
  exact rationalPlaceLinear_basis θ (bCoord i)

private theorem squarefreeWedge_comm_f2 (u v : LinearForm) :
    squarefreeWedge u v = squarefreeWedge v u := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair]
  ring

private theorem squarefreeWedge_self_f2 (u : LinearForm) :
    squarefreeWedge u u = 0 := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair, Pi.zero_apply]
  simpa [mul_comm] using CharTwo.add_self_eq_zero (u i * u j)

private theorem finset_pair_eq_pair_iff {m : Nat}
    {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) :
    ({i, j} : Finset (Fin m)) = {k, l} ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    have hi : i = k ∨ i = l := by
      have : i ∈ ({k, l} : Finset (Fin m)) := by
        rw [← h]
        simp
      simpa using this
    rcases hi with hik | hil
    · left
      refine ⟨hik, ?_⟩
      have hj : j = k ∨ j = l := by
        have : j ∈ ({k, l} : Finset (Fin m)) := by
          rw [← h]
          simp
        simpa using this
      exact hj.resolve_left (fun hjk => hij (hik.trans hjk.symm))
    · right
      refine ⟨hil, ?_⟩
      have hj : j = k ∨ j = l := by
        have : j ∈ ({k, l} : Finset (Fin m)) := by
          rw [← h]
          simp
        simpa using this
      exact hj.resolve_right (fun hjl => hij (hil.trans hjl.symm))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

private theorem squarefreeWedge_linearFormBasis
    (i j : Fin 10) (hij : i ≠ j) :
    squarefreeWedge (linearFormBasis i) (linearFormBasis j) =
      twoFormBasis (quadraticPair i j hij) := by
  ext s
  rcases QuadraticIndex.exists_pair s with ⟨k, l, hkl, rfl⟩
  simp only [squarefreeWedge_pair]
  by_cases hpair : quadraticPair k l hkl = quadraticPair i j hij
  · have hset := congrArg Subtype.val hpair
    have hcases : (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
      exact (finset_pair_eq_pair_iff hkl hij).mp hset
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [linearFormBasis, twoFormBasis, Pi.basisFun, hij, hkl, hpair]
  · have hset : ({k, l} : Finset (Fin 10)) ≠ {i, j} := by
      intro h
      apply hpair
      apply Subtype.ext
      simpa [quadraticPair] using h
    by_cases hki : k = i
    · subst k
      have hlj : l ≠ j := by
        intro hlj
        subst l
        exact hset rfl
      simp [linearFormBasis, twoFormBasis, Pi.basisFun, hpair, hkl, hij, hlj]
    · by_cases hkj : k = j
      · subst k
        have hli : l ≠ i := by
          intro hli
          subst l
          exact hset (Finset.pair_comm _ _)
        simp [linearFormBasis, twoFormBasis, Pi.basisFun, hpair, hkl, hij, hli]
      · simp [linearFormBasis, twoFormBasis, Pi.basisFun, hpair, hki, hkj]

/-- Exterior-square action of a rational-place substitution.  It is defined
by the universal basis construction, so linearity is intrinsic and does not
expand a 100-term coordinate sum. -/
def rationalPlaceTwoFormLinear (θ : Fin 2) : TwoForm →ₗ[F₂] TwoForm :=
  twoFormBasis.constr F₂ (fun s =>
    squarefreeWedge
      (rationalPlaceInputChange θ (quadraticFirst s))
      (rationalPlaceInputChange θ (quadraticSecond s)))

private theorem rationalPlaceTwoFormLinear_basisWedge
    (θ : Fin 2) (i j : Fin 10) :
    rationalPlaceTwoFormLinear θ
        (squarefreeWedge (linearFormBasis i) (linearFormBasis j)) =
      squarefreeWedge (rationalPlaceInputChange θ i)
        (rationalPlaceInputChange θ j) := by
  by_cases hij : i = j
  · subst j
    rw [squarefreeWedge_self_f2, map_zero, squarefreeWedge_self_f2]
  · rw [squarefreeWedge_linearFormBasis i j hij,
      rationalPlaceTwoFormLinear, twoFormBasis.constr_basis]
    have hpair := quadraticPair_chosen (quadraticPair i j hij)
    have hset := congrArg Subtype.val hpair
    have hcases :
        (quadraticFirst (quadraticPair i j hij) = i ∧
          quadraticSecond (quadraticPair i j hij) = j) ∨
        (quadraticFirst (quadraticPair i j hij) = j ∧
          quadraticSecond (quadraticPair i j hij) = i) := by
      exact (finset_pair_eq_pair_iff
        (quadraticFirst_ne_second (quadraticPair i j hij)) hij).mp hset.symm
    rcases hcases with ⟨hfi, hsj⟩ | ⟨hfj, hsi⟩
    · rw [hfi, hsj]
    · rw [hfj, hsi, squarefreeWedge_comm_f2]

/-- The exterior-square action sends a decomposable form to the wedge of the
transformed factors. -/
theorem rationalPlaceTwoFormLinear_squarefreeWedge
    (θ : Fin 2) (u v : LinearForm) :
    rationalPlaceTwoFormLinear θ (squarefreeWedge u v) =
      squarefreeWedge
        (∑ i : Fin 10, u i • rationalPlaceInputChange θ i)
        (∑ i : Fin 10, v i • rationalPlaceInputChange θ i) := by
  have hu : ∑ i : Fin 10, u i • linearFormBasis i = u := by
    simpa [linearFormBasis] using linearFormBasis.sum_repr u
  have hv : ∑ i : Fin 10, v i • linearFormBasis i = v := by
    simpa [linearFormBasis] using linearFormBasis.sum_repr v
  calc
    _ = rationalPlaceTwoFormLinear θ
        (squarefreeWedge
          (∑ i : Fin 10, u i • linearFormBasis i)
          (∑ i : Fin 10, v i • linearFormBasis i)) := by rw [hu, hv]
    _ = ∑ i : Fin 10, u i •
        ∑ j : Fin 10, v j •
          squarefreeWedge (rationalPlaceInputChange θ i)
            (rationalPlaceInputChange θ j) := by
      rw [squarefreeWedge_sum_left, map_sum]
      congr 1
      funext i
      rw [squarefreeWedge_smul_left, map_smul,
        squarefreeWedge_sum_right, map_sum]
      simp_rw [squarefreeWedge_smul_right, map_smul,
        rationalPlaceTwoFormLinear_basisWedge]
    _ = _ := by
      rw [squarefreeWedge_sum_left]
      congr 1
      funext i
      rw [squarefreeWedge_smul_left, squarefreeWedge_sum_right]
      simp_rw [squarefreeWedge_smul_right]

theorem rationalPlaceTwoFormLinear_squarefreeWedge'
    (θ : Fin 2) (u v : LinearForm) :
    rationalPlaceTwoFormLinear θ (squarefreeWedge u v) =
      squarefreeWedge (rationalPlaceLinear θ u)
        (rationalPlaceLinear θ v) := by
  rw [rationalPlaceLinear_apply, rationalPlaceLinear_apply]
  exact rationalPlaceTwoFormLinear_squarefreeWedge θ u v

/-- Permutation of the four closed-place labels induced by translation and
reversal.  The degree-two place is fixed. -/
def rationalPlacePerm : Fin 2 → Fin 4 → Fin 4 :=
  ![![1, 0, 2, 3], ![2, 1, 0, 3]]

/-- Coordinates of a transformed local basis vector in the basis at the
permuted place.  Only the degree-two residue basis is non-permutational. -/
def rationalPlaceLocalBasisChange : Fin 2 → Fin 4 → Fin 4 → LocalKleinParam :=
  ![
    ![![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]],
       ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]],
       ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]],
       ![![1,1,0,0], ![0,1,0,0], ![0,0,1,1], ![0,0,0,1]]],
    ![![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]],
       ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]],
       ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]],
       ![![0,1,0,0], ![1,0,0,0], ![0,0,0,1], ![0,0,1,0]]]]

private theorem rationalPlaceLinear_translation_a (i : Fin 5) :
    rationalPlaceLinear 0 (aLinear i) =
      ![aOneEval, aOneJet, aLinear 2 + aLinear 3,
        aLinear 3, aLinear 4] i := by
  rw [rationalPlaceLinear_aLinear]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [aOneEval, aOneJet, rationalPlaceInputChange,
      aLinear, aCoord, Pi.basisFun, Fin.sum_univ_succ]

private theorem rationalPlaceLinear_translation_b (i : Fin 5) :
    rationalPlaceLinear 0 (bLinear i) =
      ![bOneEval, bOneJet, bLinear 2 + bLinear 3,
        bLinear 3, bLinear 4] i := by
  rw [rationalPlaceLinear_bLinear]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [bOneEval, bOneJet, rationalPlaceInputChange,
      bLinear, bCoord, Pi.basisFun, Fin.sum_univ_succ]

private theorem rationalPlaceLinear_reversal_a (i : Fin 5) :
    rationalPlaceLinear 1 (aLinear i) =
      ![aLinear 4, aLinear 3, aLinear 2, aLinear 1, aLinear 0] i := by
  rw [rationalPlaceLinear_aLinear]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [rationalPlaceInputChange, aLinear, aCoord, Pi.basisFun]

private theorem rationalPlaceLinear_reversal_b (i : Fin 5) :
    rationalPlaceLinear 1 (bLinear i) =
      ![bLinear 4, bLinear 3, bLinear 2, bLinear 1, bLinear 0] i := by
  rw [rationalPlaceLinear_bLinear]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [rationalPlaceInputChange, bLinear, bCoord, Pi.basisFun]

theorem rationalPlaceLinear_closedPlaceLocalBasis
    (θ : Fin 2) (place i : Fin 4) :
    rationalPlaceLinear θ (closedPlaceLocalBasis place i) =
      ∑ j : Fin 4, rationalPlaceLocalBasisChange θ place i j •
        closedPlaceLocalBasis (rationalPlacePerm θ place) j := by
  fin_cases θ <;> fin_cases place <;> fin_cases i <;>
    simp [rationalPlaceLocalBasisChange, rationalPlacePerm,
      closedPlaceLocalBasis, aOneEval, aOneJet, bOneEval, bOneJet,
      aStarZero, aStarOne, bStarZero, bStarOne,
      rationalPlaceLinear_translation_a, rationalPlaceLinear_translation_b,
      rationalPlaceLinear_reversal_a, rationalPlaceLinear_reversal_b,
      Fin.sum_univ_succ] <;>
    ext k <;> fin_cases k <;>
    simp [aLinear, bLinear, aCoord, bCoord, Pi.basisFun,
      CharTwo.add_self_eq_zero]

/-- Exterior coordinates induced on a local six-dimensional Klein chart.
The rational charts are transported unchanged; the degree-two chart records
the two explicit residue-basis changes. -/
def rationalPlaceLocalTwoCoordChange (θ : Fin 2) (place : Fin 4)
    (p : LocalKleinCoord) : LocalKleinCoord :=
  ![
    ![p, p, p,
      ![p 0, p 1, p 1 + p 2, p 1 + p 3,
        p 1 + p 2 + p 3 + p 4, p 5]],
    ![p, p, p, ![p 0, p 4, p 3, p 2, p 1, p 5]]
  ] θ place

/-- The global exterior action agrees with the displayed local coordinate
action at every closed place. -/
private theorem rationalPlaceLinear_closedPlaceLocalBasis_rational
    (θ : Fin 2) (place i : Fin 4) (hplace : place ≠ 3) :
    rationalPlaceLinear θ (closedPlaceLocalBasis place i) =
      closedPlaceLocalBasis (rationalPlacePerm θ place) i := by
  rw [rationalPlaceLinear_closedPlaceLocalBasis]
  fin_cases θ <;> fin_cases place <;> fin_cases i <;>
    simp_all [rationalPlaceLocalBasisChange, rationalPlacePerm,
      Fin.sum_univ_succ]

private theorem rationalPlaceTwoFormLinear_localTwoForm_rational
    (θ : Fin 2) (place : Fin 4) (hplace : place ≠ 3)
    (p : LocalKleinCoord) :
    rationalPlaceTwoFormLinear θ (localTwoForm place p) =
      localTwoForm (rationalPlacePerm θ place)
        (rationalPlaceLocalTwoCoordChange θ place p) := by
  rw [localTwoForm, map_sum]
  simp_rw [map_smul, rationalPlaceTwoFormLinear_squarefreeWedge',
    rationalPlaceLinear_closedPlaceLocalBasis_rational θ place _ hplace]
  have hcoord : rationalPlaceLocalTwoCoordChange θ place p = p := by
    fin_cases θ <;> fin_cases place <;>
      simp_all [rationalPlaceLocalTwoCoordChange]
  rw [hcoord]
  rfl

private theorem rationalPlaceTwoFormLinear_localTwoForm_translation_degreeTwo
    (p : LocalKleinCoord) :
    rationalPlaceTwoFormLinear 0 (localTwoForm 3 p) =
      localTwoForm (rationalPlacePerm 0 3)
        (rationalPlaceLocalTwoCoordChange 0 3 p) := by
  rw [localTwoForm, map_sum]
  simp_rw [map_smul, rationalPlaceTwoFormLinear_squarefreeWedge',
    rationalPlaceLinear_closedPlaceLocalBasis]
  simp [rationalPlaceLocalTwoCoordChange, rationalPlaceLocalBasisChange,
    rationalPlacePerm, localTwoForm, localKleinPair, Fin.sum_univ_succ,
    squarefreeWedge_add_left, squarefreeWedge_add_right,
    squarefreeWedge_smul_left, squarefreeWedge_smul_right,
    squarefreeWedge_self_f2]
  match_scalars <;> ring_nf

private theorem rationalPlaceTwoFormLinear_localTwoForm_reversal_degreeTwo
    (p : LocalKleinCoord) :
    rationalPlaceTwoFormLinear 1 (localTwoForm 3 p) =
      localTwoForm (rationalPlacePerm 1 3)
        (rationalPlaceLocalTwoCoordChange 1 3 p) := by
  rw [localTwoForm, map_sum]
  simp_rw [map_smul, rationalPlaceTwoFormLinear_squarefreeWedge',
    rationalPlaceLinear_closedPlaceLocalBasis]
  simp [rationalPlaceLocalTwoCoordChange, rationalPlaceLocalBasisChange,
    rationalPlacePerm, localTwoForm, localKleinPair, Fin.sum_univ_succ,
    squarefreeWedge_add_left, squarefreeWedge_add_right,
    squarefreeWedge_smul_left, squarefreeWedge_smul_right]
  rw [squarefreeWedge_comm_f2
      (closedPlaceLocalBasis 3 1) (closedPlaceLocalBasis 3 0),
    squarefreeWedge_comm_f2
      (closedPlaceLocalBasis 3 3) (closedPlaceLocalBasis 3 2)]
  module

theorem rationalPlaceTwoFormLinear_localTwoForm
    (θ : Fin 2) (place : Fin 4) (p : LocalKleinCoord) :
    rationalPlaceTwoFormLinear θ (localTwoForm place p) =
      localTwoForm (rationalPlacePerm θ place)
        (rationalPlaceLocalTwoCoordChange θ place p) := by
  fin_cases θ <;> fin_cases place
  · exact rationalPlaceTwoFormLinear_localTwoForm_rational 0 0 (by decide) p
  · exact rationalPlaceTwoFormLinear_localTwoForm_rational 0 1 (by decide) p
  · exact rationalPlaceTwoFormLinear_localTwoForm_rational 0 2 (by decide) p
  · exact rationalPlaceTwoFormLinear_localTwoForm_translation_degreeTwo p
  · exact rationalPlaceTwoFormLinear_localTwoForm_rational 1 0 (by decide) p
  · exact rationalPlaceTwoFormLinear_localTwoForm_rational 1 1 (by decide) p
  · exact rationalPlaceTwoFormLinear_localTwoForm_rational 1 2 (by decide) p
  · exact rationalPlaceTwoFormLinear_localTwoForm_reversal_degreeTwo p

/-- Induced action on the nine multiplication-output coefficients.  The
translation rows are the mod-two Pascal rows; reversal reverses degree. -/
def rationalTargetCoeffChange : Fin 2 → TargetCoeff → TargetCoeff :=
  ![
    fun c => ![
      c 0,
      c 0 + c 1,
      c 0 + c 2,
      c 0 + c 1 + c 2 + c 3,
      c 0 + c 4,
      c 0 + c 1 + c 4 + c 5,
      c 0 + c 2 + c 4 + c 6,
      c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7,
      c 0 + c 8],
    fun c => ![c 8, c 7, c 6, c 5, c 4, c 3, c 2, c 1, c 0]
  ]

private theorem rationalPlaceLinear_a_at_b
    (θ : Fin 2) (i j : Fin 5) :
    rationalPlaceLinear θ (aLinear i) (bCoord j) = 0 := by
  rw [rationalPlaceLinear_aLinear]
  fin_cases θ <;> fin_cases i <;> fin_cases j <;>
    simp [rationalPlaceInputChange, aCoord, bCoord]

private theorem rationalPlaceLinear_b_at_a
    (θ : Fin 2) (i j : Fin 5) :
    rationalPlaceLinear θ (bLinear i) (aCoord j) = 0 := by
  rw [rationalPlaceLinear_bLinear]
  fin_cases θ <;> fin_cases i <;> fin_cases j <;>
    simp [rationalPlaceInputChange, aCoord, bCoord]

private def rationalInputCoeffChange : Fin 2 → Fin 5 → Fin 5 → F₂ :=
  ![
    ![![1,1,1,1,1], ![0,1,0,1,0], ![0,0,1,1,0],
      ![0,0,0,1,0], ![0,0,0,0,1]],
    ![![0,0,0,0,1], ![0,0,0,1,0], ![0,0,1,0,0],
      ![0,1,0,0,0], ![1,0,0,0,0]]]

private theorem rationalPlaceLinear_a_at_a
    (θ : Fin 2) (i j : Fin 5) :
    rationalPlaceLinear θ (aLinear i) (aCoord j) =
      rationalInputCoeffChange θ i j := by
  rw [rationalPlaceLinear_aLinear]
  fin_cases θ <;> fin_cases i <;> fin_cases j <;>
    simp [rationalPlaceInputChange, rationalInputCoeffChange, aCoord]

private theorem rationalPlaceLinear_b_at_b
    (θ : Fin 2) (i j : Fin 5) :
    rationalPlaceLinear θ (bLinear i) (bCoord j) =
      rationalInputCoeffChange θ i j := by
  rw [rationalPlaceLinear_bLinear]
  fin_cases θ <;> fin_cases i <;> fin_cases j <;>
    simp [rationalPlaceInputChange, rationalInputCoeffChange, bCoord]

private theorem rationalPlaceTwoFormLinear_targetPairTwo
    (θ : Fin 2) (i j : Fin 5) :
    rationalPlaceTwoFormLinear θ (targetPairTwo i j) =
      squarefreeWedge (rationalPlaceLinear θ (aLinear i))
        (rationalPlaceLinear θ (bLinear j)) := by
  exact rationalPlaceTwoFormLinear_squarefreeWedge' θ (aLinear i) (bLinear j)

private theorem rationalPlaceTwoFormLinear_targetTwo_expansion
    (θ : Fin 2) (c : TargetCoeff) :
    rationalPlaceTwoFormLinear θ (targetTwo c) =
      ∑ x : Fin 5, ∑ y : Fin 5,
        c (hankelIndex x y) •
          squarefreeWedge (rationalPlaceLinear θ (aLinear x))
            (rationalPlaceLinear θ (bLinear y)) := by
  rw [targetTwo_eq_double_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [map_smul, rationalPlaceTwoFormLinear_targetPairTwo]

private theorem rationalPlaceTwoFormLinear_targetTwo_cross_translation
    (c : TargetCoeff) (i j : Fin 5) :
    rationalPlaceTwoFormLinear 0 (targetTwo c)
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)) =
      targetTwo (rationalTargetCoeffChange 0 c)
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)) := by
  rw [rationalPlaceTwoFormLinear_targetTwo_expansion, targetTwo_cross]
  fin_cases i <;> fin_cases j <;>
    simp [rationalTargetCoeffChange, hankelIndex, Fin.sum_univ_succ,
      squarefreeWedge_pair, rationalInputCoeffChange,
      rationalPlaceLinear_a_at_a, rationalPlaceLinear_b_at_b,
      rationalPlaceLinear_a_at_b, rationalPlaceLinear_b_at_a] <;>
    ring_nf <;> simp [N3Certificate.two_eq_zero_f2,
      show (3 : F₂) = 1 by decide, show (4 : F₂) = 0 by decide]

private theorem rationalPlaceTwoFormLinear_targetTwo_cross_reversal
    (c : TargetCoeff) (i j : Fin 5) :
    rationalPlaceTwoFormLinear 1 (targetTwo c)
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)) =
      targetTwo (rationalTargetCoeffChange 1 c)
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)) := by
  rw [rationalPlaceTwoFormLinear_targetTwo_expansion, targetTwo_cross]
  fin_cases i <;> fin_cases j <;>
    simp [rationalTargetCoeffChange, hankelIndex, Fin.sum_univ_succ,
      squarefreeWedge_pair, rationalInputCoeffChange,
      rationalPlaceLinear_a_at_a, rationalPlaceLinear_b_at_b,
      rationalPlaceLinear_a_at_b, rationalPlaceLinear_b_at_a]

/-- Rational-place substitution preserves the Hankel multiplication target
and acts on it by `rationalTargetCoeffChange`. -/
theorem rationalPlaceTwoFormLinear_targetTwo
    (θ : Fin 2) (c : TargetCoeff) :
    rationalPlaceTwoFormLinear θ (targetTwo c) =
      targetTwo (rationalTargetCoeffChange θ c) := by
  apply twoForm_ext_blocks
  · intro i j hij
    have hrhs := targetTwo_sameA (rationalTargetCoeffChange θ c) i j hij
    rw [rationalPlaceTwoFormLinear_targetTwo_expansion]
    rw [hrhs]
    simp [Finset.sum_apply, squarefreeWedge_pair,
      rationalPlaceLinear_b_at_a]
  · intro i j hij
    have hrhs := targetTwo_sameB (rationalTargetCoeffChange θ c) i j hij
    rw [rationalPlaceTwoFormLinear_targetTwo_expansion]
    rw [hrhs]
    simp [Finset.sum_apply, squarefreeWedge_pair,
      rationalPlaceLinear_a_at_b]
  · intro i j
    fin_cases θ
    · exact rationalPlaceTwoFormLinear_targetTwo_cross_translation c i j
    · exact rationalPlaceTwoFormLinear_targetTwo_cross_reversal c i j

/-- Quotient parameter induced on the fixed degree-two place. -/
def degreeTwoSymmetryParam (q : LocalKleinParam) : LocalKleinParam :=
  ![q 0, q 1, q 1 + q 2, q 3]

/-- Target-plane correction required when the degree-two canonical section
is transported.  Translation needs none; reversal needs one explicit local
target vector. -/
def degreeTwoSymmetryTarget : Fin 2 → LocalKleinParam → LocalTargetParam :=
  ![fun _ => 0, fun q => ![q 2, q 1]]

private theorem degreeTwoCanonicalCoord_symmetry
    (θ : Fin 2) (q : LocalKleinParam) :
    rationalPlaceLocalTwoCoordChange θ 3 (degreeTwoCanonicalCoord q) =
      degreeTwoCanonicalCoord (degreeTwoSymmetryParam q) +
        closedPlaceTargetCoord 3 (degreeTwoSymmetryTarget θ q) := by
  funext s
  fin_cases θ <;> fin_cases s <;>
    simp [rationalPlaceLocalTwoCoordChange, degreeTwoCanonicalCoord,
      degreeTwoSymmetryParam, degreeTwoSymmetryTarget,
      closedPlaceTargetCoord, CharTwo.add_self_eq_zero] <;>
    ring_nf <;> simp [N3Certificate.two_eq_zero_f2]

/-- Canonical rational-place lifts are carried to canonical lifts at the
permuted rational place. -/
theorem rationalPlaceTwoFormLinear_rationalLift
    (θ : Fin 2) (place : Fin 4) (hplace : place ≠ 3)
    (q : LocalKleinParam) :
    rationalPlaceTwoFormLinear θ (closedPlaceLift place q) =
      closedPlaceLift (rationalPlacePerm θ place) q := by
  rw [closedPlaceLift, rationalPlaceTwoFormLinear_localTwoForm]
  congr 1
  fin_cases θ <;> fin_cases place <;>
    simp_all [rationalPlaceLocalTwoCoordChange,
      closedPlaceCanonicalCoord, rationalPlacePerm]

/-- The degree-two canonical lift transforms into the canonical lift of the
new quotient parameter plus the displayed target-plane correction. -/
theorem rationalPlaceTwoFormLinear_degreeTwoLift
    (θ : Fin 2) (q : LocalKleinParam) :
    rationalPlaceTwoFormLinear θ (closedPlaceLift 3 q) =
      closedPlaceLift 3 (degreeTwoSymmetryParam q) +
        targetTwo (closedPlaceTargetCoeff 3
          (degreeTwoSymmetryTarget θ q)) := by
  unfold closedPlaceLift
  rw [rationalPlaceTwoFormLinear_localTwoForm]
  have hperm : rationalPlacePerm θ 3 = 3 := by
    fin_cases θ <;> rfl
  rw [hperm]
  change localTwoForm 3
      (rationalPlaceLocalTwoCoordChange θ 3 (degreeTwoCanonicalCoord q)) = _
  rw [degreeTwoCanonicalCoord_symmetry]
  rw [targetTwo_closedPlaceTargetCoeff]
  exact (localTwoFormLinear 3).map_add _ _

theorem degreeTwoSymmetryParam_effective
    (q : LocalKleinParam) (hq : DegreeTwoLocalEffective q) :
    DegreeTwoLocalEffective (degreeTwoSymmetryParam q) := by
  change q 0 * q 3 = (q 2 + 1) * (q 1 + 1) at hq
  change q 0 * q 3 = (q 1 + q 2 + 1) * (q 1 + 1)
  rw [show (q 1 + q 2 + 1) * (q 1 + 1) =
      (q 2 + 1) * (q 1 + 1) by
    calc
      (q 1 + q 2 + 1) * (q 1 + 1) =
          q 1 * q 1 + q 1 + (q 2 + 1) * (q 1 + 1) := by ring
      _ = (q 2 + 1) * (q 1 + 1) := by
        rw [N3Certificate.mul_self_f2 (q 1)]
        simp [CharTwo.add_self_eq_zero]]
  exact hq

/-- Rational-place substitutions preserve decomposability. -/
theorem rationalPlaceTwoFormLinear_decomposable
    (θ : Fin 2) {p : TwoForm} (hp : IsDecomposableTwo p) :
    IsDecomposableTwo (rationalPlaceTwoFormLinear θ p) := by
  rcases hp with ⟨u, v, rfl⟩
  exact ⟨_, _, rationalPlaceTwoFormLinear_squarefreeWedge θ u v⟩

/-- Transport of a two-rational-plus-degree-two candidate, including the
canonical-section correction absorbed into the Hankel target. -/
theorem rationalPlaceTwoFormLinear_threePlaceCandidate
    (θ : Fin 2) (place₀ place₁ : Fin 4)
    (hplace₀ : place₀ ≠ 3) (hplace₁ : place₁ ≠ 3)
    (q r s : LocalKleinParam) (c : TargetCoeff) :
    rationalPlaceTwoFormLinear θ
        (closedPlaceLift place₀ q + closedPlaceLift place₁ r +
          closedPlaceLift 3 s + targetTwo c) =
      closedPlaceLift (rationalPlacePerm θ place₀) q +
        closedPlaceLift (rationalPlacePerm θ place₁) r +
        closedPlaceLift 3 (degreeTwoSymmetryParam s) +
        targetTwo
          (rationalTargetCoeffChange θ c +
            closedPlaceTargetCoeff 3 (degreeTwoSymmetryTarget θ s)) := by
  rw [map_add, map_add, map_add,
    rationalPlaceTwoFormLinear_rationalLift θ place₀ hplace₀,
    rationalPlaceTwoFormLinear_rationalLift θ place₁ hplace₁,
    rationalPlaceTwoFormLinear_degreeTwoLift,
    rationalPlaceTwoFormLinear_targetTwo]
  have htadd :
      targetTwo
          (rationalTargetCoeffChange θ c +
            closedPlaceTargetCoeff 3 (degreeTwoSymmetryTarget θ s)) =
        targetTwo (rationalTargetCoeffChange θ c) +
          targetTwo (closedPlaceTargetCoeff 3
            (degreeTwoSymmetryTarget θ s)) := by
    exact targetTwoLinear.map_add _ _
  rw [htadd]
  module

/-- Transported algebraic obstruction for `2P₁,2P_∞,P_*`. -/
theorem three123_not_decomposable
    (q r s : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (hs : DegreeTwoLocalEffective s) (c : TargetCoeff) :
    ¬ IsDecomposableTwo
      (closedPlaceLift 1 q + closedPlaceLift 2 r +
        closedPlaceLift 3 s + targetTwo c) := by
  intro hdec
  have htransport := rationalPlaceTwoFormLinear_decomposable 1 hdec
  rw [rationalPlaceTwoFormLinear_threePlaceCandidate
    1 1 2 (by decide) (by decide) q r s c] at htransport
  let c' := rationalTargetCoeffChange 1 c +
    closedPlaceTargetCoeff 3 (degreeTwoSymmetryTarget 1 s)
  have hrepresentative : IsDecomposableTwo
      (closedPlaceLift 0 r + closedPlaceLift 1 q +
        closedPlaceLift 3 (degreeTwoSymmetryParam s) + targetTwo c') := by
    rcases htransport with ⟨u, v, huv⟩
    refine ⟨u, v, ?_⟩
    calc
      closedPlaceLift 0 r + closedPlaceLift 1 q +
          closedPlaceLift 3 (degreeTwoSymmetryParam s) + targetTwo c' =
        closedPlaceLift (rationalPlacePerm 1 1) q +
          closedPlaceLift (rationalPlacePerm 1 2) r +
          closedPlaceLift 3 (degreeTwoSymmetryParam s) +
          targetTwo
            (rationalTargetCoeffChange 1 c +
              closedPlaceTargetCoeff 3 (degreeTwoSymmetryTarget 1 s)) := by
            simp [c', rationalPlacePerm]
            module
      _ = squarefreeWedge u v := huv
  exact three013_not_decomposable r q (degreeTwoSymmetryParam s)
    hr hq (degreeTwoSymmetryParam_effective s hs) c' hrepresentative

/-- Transported algebraic obstruction for `2P₀,2P_∞,P_*`. -/
theorem three023_not_decomposable
    (q r s : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (hs : DegreeTwoLocalEffective s) (c : TargetCoeff) :
    ¬ IsDecomposableTwo
      (closedPlaceLift 0 q + closedPlaceLift 2 r +
        closedPlaceLift 3 s + targetTwo c) := by
  intro hdec
  have htransport := rationalPlaceTwoFormLinear_decomposable 0 hdec
  rw [rationalPlaceTwoFormLinear_threePlaceCandidate
    0 0 2 (by decide) (by decide) q r s c] at htransport
  let c' := rationalTargetCoeffChange 0 c +
    closedPlaceTargetCoeff 3 (degreeTwoSymmetryTarget 0 s)
  have hprofile : IsDecomposableTwo
      (closedPlaceLift 1 q + closedPlaceLift 2 r +
        closedPlaceLift 3 (degreeTwoSymmetryParam s) + targetTwo c') := by
    simpa [c', rationalPlacePerm] using htransport
  exact three123_not_decomposable q r (degreeTwoSymmetryParam s)
    hq hr (degreeTwoSymmetryParam_effective s hs) c' hprofile

theorem rational12_degreeTwo_mixed_decomposableFiber_empty
    (q r s : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (hs : DegreeTwoLocalEffective s) :
    decomposableFiber
      (closedPlaceQuotientPoint 1 q + closedPlaceQuotientPoint 2 r +
        closedPlaceQuotientPoint 3 s) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_threePlaceCandidate_of_mem_decomposableFiber
      1 q 2 r 3 s p hp with ⟨c, hc⟩
  apply three123_not_decomposable q r s hq hr hs c
  rw [← hc]
  exact hp.1

theorem rational02_degreeTwo_mixed_decomposableFiber_empty
    (q r s : LocalKleinParam)
    (hq : RationalLocalEffective q) (hr : RationalLocalEffective r)
    (hs : DegreeTwoLocalEffective s) :
    decomposableFiber
      (closedPlaceQuotientPoint 0 q + closedPlaceQuotientPoint 2 r +
        closedPlaceQuotientPoint 3 s) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rcases exists_threePlaceCandidate_of_mem_decomposableFiber
      0 q 2 r 3 s p hp with ⟨c, hc⟩
  apply three023_not_decomposable q r s hq hr hs c
  rw [← hc]
  exact hp.1

end

end N5
end UnrestrictedBooleanMul
