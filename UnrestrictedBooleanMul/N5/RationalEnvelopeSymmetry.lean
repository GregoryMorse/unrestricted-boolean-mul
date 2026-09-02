import UnrestrictedBooleanMul.N5.EnvelopeLocalSymmetry

/-!
# Rational-place symmetry of the first-order envelope

Translation and reversal already act on linear forms, two-forms, and the
nine Hankel coefficients.  Here we record that both generators preserve the
missing functional.  Consequently they preserve the first-order envelope
and transport its unique missing affine coset to itself.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Translation and reversal preserve the defining functional of the
codimension-one first-order coefficient envelope. -/
theorem firstOrderMissingFunctional_rationalTargetCoeffChange
    (theta : Fin 2) (c : TargetCoeff) :
    firstOrderMissingFunctional (rationalTargetCoeffChange theta c) =
      firstOrderMissingFunctional c := by
  fin_cases theta <;>
    simp [rationalTargetCoeffChange, firstOrderMissingFunctional] <;>
    ring_nf;
    simp [N3Certificate.two_eq_zero_f2,
      show (3 : F₂) = 1 by decide, show (4 : F₂) = 0 by decide]

/-- The correction which returns the transformed missing representative to
the chosen representative is an old first-order coefficient. -/
def rationalMissingCorrection (theta : Fin 2) : TargetCoeff :=
  rationalTargetCoeffChange theta firstOrderMissingCoeff +
    firstOrderMissingCoeff

theorem rationalMissingCorrection_mem
    (theta : Fin 2) :
    rationalMissingCorrection theta ∈ firstOrderEnvelopeCoeffSpace := by
  rw [mem_firstOrderEnvelopeCoeffSpace]
  simp only [rationalMissingCorrection, map_add,
    firstOrderMissingFunctional_rationalTargetCoeffChange,
    firstOrderMissingFunctional_missing,
    CharTwo.add_self_eq_zero]

/-- The displayed coefficient substitutions are additive.  Keeping this as
a lemma avoids repeatedly expanding all nine coordinates. -/
theorem rationalTargetCoeffChange_add
    (theta : Fin 2) (c d : TargetCoeff) :
    rationalTargetCoeffChange theta (c + d) =
      rationalTargetCoeffChange theta c + rationalTargetCoeffChange theta d := by
  fin_cases theta <;>
    funext i <;> fin_cases i <;>
    simp [rationalTargetCoeffChange] <;> abel

/-- Exact coefficient identity for transport of the missing affine coset. -/
theorem rationalTargetCoeffChange_missing_add
    (theta : Fin 2) (u : TargetCoeff) :
    rationalTargetCoeffChange theta (firstOrderMissingCoeff + u) =
      firstOrderMissingCoeff +
        (rationalMissingCorrection theta +
          rationalTargetCoeffChange theta u) := by
  have hadd : rationalTargetCoeffChange theta
      (firstOrderMissingCoeff + u) =
      rationalTargetCoeffChange theta firstOrderMissingCoeff +
        rationalTargetCoeffChange theta u :=
    rationalTargetCoeffChange_add theta firstOrderMissingCoeff u
  have hmissingSelf : firstOrderMissingCoeff + firstOrderMissingCoeff = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (firstOrderMissingCoeff i)
  rw [hadd, rationalMissingCorrection]
  calc
    rationalTargetCoeffChange theta firstOrderMissingCoeff +
        rationalTargetCoeffChange theta u =
      (firstOrderMissingCoeff + firstOrderMissingCoeff) +
        (rationalTargetCoeffChange theta firstOrderMissingCoeff +
          rationalTargetCoeffChange theta u) := by
      rw [hmissingSelf, zero_add]
    _ = firstOrderMissingCoeff +
        (rationalTargetCoeffChange theta firstOrderMissingCoeff +
          firstOrderMissingCoeff + rationalTargetCoeffChange theta u) := by
      ac_rfl

/-- Two-form form: rational-place symmetry preserves the missing affine
target coset, with an explicit old-envelope correction. -/
theorem rationalPlaceTwoFormLinear_missingCoset
    (theta : Fin 2) (u : TargetCoeff) :
    rationalPlaceTwoFormLinear theta
        (targetTwo (firstOrderMissingCoeff + u)) =
      targetTwo (firstOrderMissingCoeff +
        (rationalMissingCorrection theta +
          rationalTargetCoeffChange theta u)) := by
  rw [rationalPlaceTwoFormLinear_targetTwo,
    rationalTargetCoeffChange_missing_add]

/-! ## Transported target-clean second jets -/

/-- The target-clean second-jet space transported from the rational-zero
normalization by one rational-place generator. -/
def rationalTargetCleanSecondJetSpace (theta : Fin 2) :
    Submodule F₂ TwoForm :=
  targetCleanSecondJetSpace.map (rationalPlaceTwoFormLinear theta)

/-- Membership in a transported clean space is tested by applying the same
involutive generator once more. -/
theorem mem_rationalTargetCleanSecondJetSpace_iff
    (theta : Fin 2) (q : TwoForm) :
    q ∈ rationalTargetCleanSecondJetSpace theta ↔
      rationalPlaceTwoFormLinear theta q ∈ targetCleanSecondJetSpace := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ targetCleanSecondJetSpace at hz
    simpa only [rationalPlaceTwoFormLinear_involutive] using hz
  · intro hq
    exact ⟨rationalPlaceTwoFormLinear theta q, hq,
      rationalPlaceTwoFormLinear_involutive theta q⟩

/-- The multiplication target meets every rational transport of the clean
second jet in precisely the old first-order envelope. -/
theorem targetTwoSpace_inf_rationalTargetCleanSecondJetSpace
    (theta : Fin 2) :
    targetTwoSpace ⊓ rationalTargetCleanSecondJetSpace theta =
      firstOrderEnvelopeTwoSpace := by
  apply le_antisymm
  · rintro p ⟨hpTarget, hpClean⟩
    have htransTarget : rationalPlaceTwoFormLinear theta p ∈
        targetTwoSpace := by
      rcases hpTarget with ⟨c, rfl⟩
      change rationalPlaceTwoFormLinear theta (targetTwo c) ∈ targetTwoSpace
      rw [rationalPlaceTwoFormLinear_targetTwo]
      exact ⟨rationalTargetCoeffChange theta c, rfl⟩
    have htransClean : rationalPlaceTwoFormLinear theta p ∈
        targetCleanSecondJetSpace :=
      (mem_rationalTargetCleanSecondJetSpace_iff theta p).1 hpClean
    have htransFirst : rationalPlaceTwoFormLinear theta p ∈
        firstOrderEnvelopeTwoSpace :=
      (target_mem_targetCleanSecondJetSpace_iff_firstOrder
        (rationalPlaceTwoFormLinear theta p) htransTarget).1 htransClean
    have hback := rationalPlaceTwoFormLinear_mem_firstOrderEnvelope
      theta (rationalPlaceTwoFormLinear theta p) htransFirst
    simpa only [rationalPlaceTwoFormLinear_involutive] using hback
  · intro p hpFirst
    have hpTarget : p ∈ targetTwoSpace :=
      firstOrderEnvelopeTwoSpace_le_targetTwoSpace hpFirst
    have htransFirst : rationalPlaceTwoFormLinear theta p ∈
        firstOrderEnvelopeTwoSpace :=
      rationalPlaceTwoFormLinear_mem_firstOrderEnvelope theta p hpFirst
    have htransTarget : rationalPlaceTwoFormLinear theta p ∈
        targetTwoSpace :=
      firstOrderEnvelopeTwoSpace_le_targetTwoSpace htransFirst
    have htransClean : rationalPlaceTwoFormLinear theta p ∈
        targetCleanSecondJetSpace :=
      (target_mem_targetCleanSecondJetSpace_iff_firstOrder
        (rationalPlaceTwoFormLinear theta p) htransTarget).2 htransFirst
    exact ⟨hpTarget,
      (mem_rationalTargetCleanSecondJetSpace_iff theta p).2 htransClean⟩

theorem rationalTargetCoeffChange_missing
    (theta : Fin 2) :
    rationalTargetCoeffChange theta firstOrderMissingCoeff =
      firstOrderMissingCoeff + rationalMissingCorrection theta := by
  fin_cases theta <;>
    funext i <;> fin_cases i <;>
    simp [rationalTargetCoeffChange, firstOrderMissingCoeff,
      rationalMissingCorrection, CharTwo.add_self_eq_zero]

/-- The affine nondecomposability part of the target-clean certificate is
also invariant under rational-place transport. -/
theorem firstOrderMissing_add_rationalTargetClean_not_decomposable
    (theta : Fin 2) (z : TwoForm)
    (hz : z ∈ rationalTargetCleanSecondJetSpace theta) :
    ¬ IsDecomposableTwo (targetTwo firstOrderMissingCoeff + z) := by
  intro hdec
  have htransZ : rationalPlaceTwoFormLinear theta z ∈
      targetCleanSecondJetSpace :=
    (mem_rationalTargetCleanSecondJetSpace_iff theta z).1 hz
  have hcorrectionFirst : targetTwo (rationalMissingCorrection theta) ∈
      firstOrderEnvelopeTwoSpace :=
    ⟨rationalMissingCorrection theta,
      rationalMissingCorrection_mem theta, rfl⟩
  have hcorrectionClean : targetTwo (rationalMissingCorrection theta) ∈
      targetCleanSecondJetSpace := by
    have htarget : targetTwo (rationalMissingCorrection theta) ∈
        targetTwoSpace :=
      firstOrderEnvelopeTwoSpace_le_targetTwoSpace hcorrectionFirst
    exact (target_mem_targetCleanSecondJetSpace_iff_firstOrder
      (targetTwo (rationalMissingCorrection theta)) htarget).2
        hcorrectionFirst
  let z' := targetTwo (rationalMissingCorrection theta) +
    rationalPlaceTwoFormLinear theta z
  have hz' : z' ∈ targetCleanSecondJetSpace :=
    targetCleanSecondJetSpace.add_mem hcorrectionClean htransZ
  have htransEq :
      rationalPlaceTwoFormLinear theta
          (targetTwo firstOrderMissingCoeff + z) =
        targetTwo firstOrderMissingCoeff + z' := by
    rw [map_add, rationalPlaceTwoFormLinear_targetTwo,
      rationalTargetCoeffChange_missing]
    have htargetAdd :
        targetTwo
            (firstOrderMissingCoeff + rationalMissingCorrection theta) =
          targetTwo firstOrderMissingCoeff +
            targetTwo (rationalMissingCorrection theta) := by
      exact targetTwoLinear.map_add _ _
    rw [htargetAdd]
    change
      (targetTwo firstOrderMissingCoeff +
          targetTwo (rationalMissingCorrection theta)) +
          rationalPlaceTwoFormLinear theta z =
        targetTwo firstOrderMissingCoeff +
          (targetTwo (rationalMissingCorrection theta) +
            rationalPlaceTwoFormLinear theta z)
    exact add_assoc _ _ _
  have htransDec : IsDecomposableTwo
      (targetTwo firstOrderMissingCoeff + z') := by
    rw [← htransEq]
    exact rationalPlaceTwoFormLinear_decomposable theta hdec
  exact firstOrderMissing_add_targetClean_not_decomposable z' hz' htransDec

/-- Equation (11.7) transported to either of the other rational second-jet
normalizations.  The optional defect is transported along with the clean
space and remains decomposable. -/
theorem targetTwoSpace_inf_rationalTargetClean_sup_decomposable
    (theta : Fin 2) (q : TwoForm) (hqdec : IsDecomposableTwo q) :
    targetTwoSpace ⊓
        (rationalTargetCleanSecondJetSpace theta ⊔
          Submodule.span F₂ ({q} : Set TwoForm)) =
      firstOrderEnvelopeTwoSpace := by
  apply le_antisymm
  · rintro p ⟨hpTarget, hpSup⟩
    rcases Submodule.mem_sup.mp hpSup with ⟨z, hz, r, hr, hzr⟩
    rcases Submodule.mem_span_singleton.mp hr with ⟨alpha, rfl⟩
    subst p
    have htransTarget : rationalPlaceTwoFormLinear theta
        (z + alpha • q) ∈ targetTwoSpace := by
      rcases hpTarget with ⟨c, hc⟩
      rw [← hc]
      change rationalPlaceTwoFormLinear theta (targetTwo c) ∈ targetTwoSpace
      rw [rationalPlaceTwoFormLinear_targetTwo]
      exact ⟨rationalTargetCoeffChange theta c, rfl⟩
    have htransZ : rationalPlaceTwoFormLinear theta z ∈
        targetCleanSecondJetSpace :=
      (mem_rationalTargetCleanSecondJetSpace_iff theta z).1 hz
    have htransQ : rationalPlaceTwoFormLinear theta q ∈
        Submodule.span F₂
          ({rationalPlaceTwoFormLinear theta q} : Set TwoForm) :=
      Submodule.mem_span_singleton_self _
    have htransSup : rationalPlaceTwoFormLinear theta
        (z + alpha • q) ∈
        targetCleanSecondJetSpace ⊔
          Submodule.span F₂
            ({rationalPlaceTwoFormLinear theta q} : Set TwoForm) := by
      rw [map_add, map_smul]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left htransZ)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ htransQ))
    have htransFirst : rationalPlaceTwoFormLinear theta
        (z + alpha • q) ∈ firstOrderEnvelopeTwoSpace := by
      have hinter : rationalPlaceTwoFormLinear theta
          (z + alpha • q) ∈
          targetTwoSpace ⊓
            (targetCleanSecondJetSpace ⊔
              Submodule.span F₂
                ({rationalPlaceTwoFormLinear theta q} : Set TwoForm)) :=
        ⟨htransTarget, htransSup⟩
      rw [targetTwoSpace_inf_targetClean_sup_decomposable
        (rationalPlaceTwoFormLinear theta q)
        (rationalPlaceTwoFormLinear_decomposable theta hqdec)] at hinter
      exact hinter
    have hback := rationalPlaceTwoFormLinear_mem_firstOrderEnvelope
      theta (rationalPlaceTwoFormLinear theta (z + alpha • q)) htransFirst
    simpa only [rationalPlaceTwoFormLinear_involutive] using hback
  · intro p hpFirst
    have hpInf : p ∈
        targetTwoSpace ⊓ rationalTargetCleanSecondJetSpace theta := by
      rw [targetTwoSpace_inf_rationalTargetCleanSecondJetSpace]
      exact hpFirst
    exact ⟨hpInf.1, Submodule.mem_sup_left hpInf.2⟩

/-! ## The three rational clean normalizations -/

/-- Target-clean second-jet space at rational places zero, one, and infinity.
The latter two are the translation and reversal transports of the first. -/
def rationalPlaceTargetCleanSecondJetSpace (place : Fin 3) :
    Submodule F₂ TwoForm :=
  ![targetCleanSecondJetSpace,
    rationalTargetCleanSecondJetSpace 0,
    rationalTargetCleanSecondJetSpace 1] place

/-- The two-dimensional first-jet extension at each rational place, obtained
from the zero-place extension by the same substitutions used for the clean
quadratic spaces. -/
def rationalPlaceSecondJetExtensionSpace (place : Fin 3) :
    Submodule F₂ LinearForm :=
  ![secondJetExtensionSpace,
    secondJetExtensionSpace.map (rationalPlaceLinear 0),
    secondJetExtensionSpace.map (rationalPlaceLinear 1)] place

/-- Boolean contraction of a decomposable two-form distributes the diagonal
coordinate product across its two exterior factors. -/
theorem ambientBooleanContraction_squarefreeWedge
    (ell u v : LinearForm) :
    ambientBooleanContraction ell (squarefreeWedge u v) =
      squarefreeWedge (ambientDiagonalProduct ell u) v +
        squarefreeWedge u (ambientDiagonalProduct ell v) := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [ambientBooleanContraction, squarefreeWedge_pair, Pi.add_apply]
  simp [quadraticPair, hij, ambientDiagonalProduct]
  ring

/-- Coordinatewise multiplication by an arbitrary linear form preserves a
coordinate support subspace. -/
theorem ambientDiagonalProduct_mem_linearCoordinateSubspace
    (S : Set (Fin 10)) (ell u : LinearForm)
    (hu : u ∈ linearCoordinateSubspace S) :
    ambientDiagonalProduct ell u ∈ linearCoordinateSubspace S := by
  intro i hi
  simp [ambientDiagonalProduct, hu i hi]

/-- Hadamard multiplication of a coordinate exterior basis vector merely
rescales that same basis vector. -/
theorem ambientTwoHadamard_squarefreeWedge_basis
    (i j : Fin 10) (hij : i ≠ j) (q : TwoForm) :
    ambientTwoHadamard
        (squarefreeWedge
          ((Pi.basisFun F₂ (Fin 10)) i)
          ((Pi.basisFun F₂ (Fin 10)) j)) q =
      q (quadraticPair i j hij) •
        squarefreeWedge
          ((Pi.basisFun F₂ (Fin 10)) i)
          ((Pi.basisFun F₂ (Fin 10)) j) := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨k, l, hkl, rfl⟩
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simp [ambientTwoHadamard, squarefreeWedge_pair, Pi.basisFun, hij]
    · simp [ambientTwoHadamard, squarefreeWedge_pair, Pi.basisFun,
        hij, hjl, hkl]
  · by_cases hil : i = l
    · subst l
      by_cases hjk : j = k
      · subst k
        rw [quadraticPair_swap]
        simp [ambientTwoHadamard, squarefreeWedge_pair, Pi.basisFun, hij]
      · simp [ambientTwoHadamard, squarefreeWedge_pair, Pi.basisFun,
          hij, hjk, hkl]
    · simp [ambientTwoHadamard, squarefreeWedge_pair, Pi.basisFun,
        hik, hil]

private theorem ambientTwoHadamard_smul_left
    (a : F₂) (p q : TwoForm) :
    ambientTwoHadamard (a • p) q = a • ambientTwoHadamard p q := by
  funext s
  simp only [ambientTwoHadamard, Pi.smul_apply, smul_eq_mul]
  ring

private def ambientTwoHadamardLeftLinear (q : TwoForm) :
    TwoForm →ₗ[F₂] TwoForm where
  toFun p := ambientTwoHadamard p q
  map_add' p r := ambientTwoHadamard_add_left p r q
  map_smul' a p := ambientTwoHadamard_smul_left a p q

/-- Ambient coordinate occupied by each rational-zero local basis vector. -/
def rationalZeroLocalAmbientIndex : Fin 4 → Fin 10 :=
  ![aCoord 0, aCoord 1, bCoord 0, bCoord 1]

theorem rationalZeroLocalBasis_eq_ambientBasis (i : Fin 4) :
    closedPlaceLocalBasis 0 i =
      (Pi.basisFun F₂ (Fin 10)) (rationalZeroLocalAmbientIndex i) := by
  fin_cases i <;>
    simp [closedPlaceLocalBasis, rationalZeroLocalAmbientIndex,
      aLinear, bLinear]

theorem rationalZeroLocalAmbientIndex_pair_ne (s : Fin 6) :
    rationalZeroLocalAmbientIndex (localKleinPair s).1 ≠
      rationalZeroLocalAmbientIndex (localKleinPair s).2 := by
  fin_cases s <;>
    decide

private theorem ambientBooleanContraction_smul_right
    (a : F₂) (ell : LinearForm) (q : TwoForm) :
    ambientBooleanContraction ell (a • q) =
      a • ambientBooleanContraction ell q := by
  funext s
  simp only [ambientBooleanContraction, Pi.smul_apply, smul_eq_mul]
  ring

/-- The exterior square of a coordinate block is closed under every Boolean
linear--quadratic contraction. -/
theorem ambientBooleanContraction_mem_quadraticExterior_coordinate
    (S : Set (Fin 10)) (ell : LinearForm) (q : TwoForm)
    (hq : q ∈ quadraticExterior (linearCoordinateSubspace S)) :
    ambientBooleanContraction ell q ∈
      quadraticExterior (linearCoordinateSubspace S) := by
  refine Submodule.span_induction
    (p := fun q _ => ambientBooleanContraction ell q ∈
      quadraticExterior (linearCoordinateSubspace S)) ?_ ?_ ?_ ?_ hq
  · rintro q ⟨u, hu, v, hv, rfl⟩
    rw [ambientBooleanContraction_squarefreeWedge]
    exact (quadraticExterior (linearCoordinateSubspace S)).add_mem
      (squarefreeWedge_mem_quadraticExterior _
        (ambientDiagonalProduct_mem_linearCoordinateSubspace S ell u hu) hv)
      (squarefreeWedge_mem_quadraticExterior _ hu
        (ambientDiagonalProduct_mem_linearCoordinateSubspace S ell v hv))
  · simp
  · intro p q _hp _hq hp hq
    rw [ambientBooleanContraction_add_right]
    exact (quadraticExterior (linearCoordinateSubspace S)).add_mem hp hq
  · intro a q _hq hq
    rw [ambientBooleanContraction_smul_right]
    exact (quadraticExterior (linearCoordinateSubspace S)).smul_mem a hq

/-- Transporting one extension factor and an arbitrary companion preserves
membership in the clean space. -/
private theorem squarefreeWedge_mem_rationalTargetClean_of_extensionMap
    (theta : Fin 2) (u v : LinearForm)
    (hu : u ∈ secondJetExtensionSpace.map (rationalPlaceLinear theta)) :
    squarefreeWedge u v ∈ rationalTargetCleanSecondJetSpace theta := by
  rcases hu with ⟨u₀, hu₀, rfl⟩
  refine ⟨squarefreeWedge u₀ (rationalPlaceLinear theta v), ?_, ?_⟩
  · apply Submodule.mem_sup_right
    exact Submodule.subset_span
      ⟨u₀, hu₀, rationalPlaceLinear theta v, rfl⟩
  · rw [rationalPlaceTwoFormLinear_squarefreeWedge',
      rationalPlaceLinear_involutive]

/-- A wedge with one factor in the rational first-jet extension belongs to
the corresponding target-clean second-jet space. -/
theorem rationalPlace_extensionWedge_mem_targetClean
    (place : Fin 3) (u v : LinearForm)
    (hu : u ∈ rationalPlaceSecondJetExtensionSpace place) :
    squarefreeWedge u v ∈
      rationalPlaceTargetCleanSecondJetSpace place := by
  fin_cases place
  · apply Submodule.mem_sup_right
    exact Submodule.subset_span ⟨u, hu, v, rfl⟩
  · exact squarefreeWedge_mem_rationalTargetClean_of_extensionMap 0 u v hu
  · exact squarefreeWedge_mem_rationalTargetClean_of_extensionMap 1 u v hu

/-- The displayed basis of the rational-zero local four-space is supported
on the second-jet core coordinates. -/
theorem rationalZeroLocalBasis_mem_secondJetCoreSpace (i : Fin 4) :
    closedPlaceLocalBasis 0 i ∈ secondJetCoreSpace := by
  change ∀ k, k ∉ secondJetCoreSet → closedPlaceLocalBasis 0 i k = 0
  intro k hk
  fin_cases i <;> fin_cases k <;>
    simp_all [closedPlaceLocalBasis, secondJetCoreSet,
      aLinear, bLinear, aCoord, bCoord, Pi.basisFun]

/-- The whole exterior square of the rational-zero local four-space is the
corresponding core exterior summand of the clean second jet. -/
theorem rationalZero_localTwoForm_mem_quadraticExterior
    (p : LocalKleinCoord) :
    localTwoForm 0 p ∈ quadraticExterior secondJetCoreSpace := by
  rw [localTwoForm]
  apply Submodule.sum_mem
  intro s _
  apply Submodule.smul_mem
  exact squarefreeWedge_mem_quadraticExterior secondJetCoreSpace
    (rationalZeroLocalBasis_mem_secondJetCoreSpace (localKleinPair s).1)
    (rationalZeroLocalBasis_mem_secondJetCoreSpace (localKleinPair s).2)

/-- Hadamard multiplication of a rational-zero local two-form by an
arbitrary ambient two-form remains in the local core exterior square. -/
theorem rationalZero_ambientTwoHadamard_mem_quadraticExterior
    (p : LocalKleinCoord) (q : TwoForm) :
    ambientTwoHadamard (localTwoForm 0 p) q ∈
      quadraticExterior secondJetCoreSpace := by
  change ambientTwoHadamardLeftLinear q
      (∑ s : Fin 6, p s •
        squarefreeWedge
          (closedPlaceLocalBasis 0 (localKleinPair s).1)
          (closedPlaceLocalBasis 0 (localKleinPair s).2)) ∈ _
  rw [map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [map_smul]
  have hbasis :
      ambientTwoHadamard
          (squarefreeWedge
            (closedPlaceLocalBasis 0 (localKleinPair s).1)
            (closedPlaceLocalBasis 0 (localKleinPair s).2)) q =
        q (quadraticPair
            (rationalZeroLocalAmbientIndex (localKleinPair s).1)
            (rationalZeroLocalAmbientIndex (localKleinPair s).2)
            (rationalZeroLocalAmbientIndex_pair_ne s)) •
          squarefreeWedge
            (closedPlaceLocalBasis 0 (localKleinPair s).1)
            (closedPlaceLocalBasis 0 (localKleinPair s).2) := by
    rw [rationalZeroLocalBasis_eq_ambientBasis,
      rationalZeroLocalBasis_eq_ambientBasis]
    exact ambientTwoHadamard_squarefreeWedge_basis _ _
      (rationalZeroLocalAmbientIndex_pair_ne s) q
  change p s • ambientTwoHadamard
      (squarefreeWedge
        (closedPlaceLocalBasis 0 (localKleinPair s).1)
        (closedPlaceLocalBasis 0 (localKleinPair s).2)) q ∈ _
  rw [hbasis]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact squarefreeWedge_mem_quadraticExterior secondJetCoreSpace
    (rationalZeroLocalBasis_mem_secondJetCoreSpace (localKleinPair s).1)
    (rationalZeroLocalBasis_mem_secondJetCoreSpace (localKleinPair s).2)

/-- Every exterior two-form on the rational-zero local four-space belongs
to the target-clean second-jet space. -/
theorem rationalZero_localTwoForm_mem_targetClean
    (p : LocalKleinCoord) :
    localTwoForm 0 p ∈ targetCleanSecondJetSpace := by
  exact Submodule.mem_sup_left (Submodule.mem_sup_right
    (rationalZero_localTwoForm_mem_quadraticExterior p))

/-- Contracting a rational-zero local two-form by any linear form remains in
the clean second-jet space. -/
theorem rationalZero_ambientBooleanContraction_mem_targetClean
    (ell : LinearForm) (p : LocalKleinCoord) :
    ambientBooleanContraction ell (localTwoForm 0 p) ∈
      targetCleanSecondJetSpace := by
  have hlocal : ambientBooleanContraction ell (localTwoForm 0 p) ∈
      quadraticExterior secondJetCoreSpace := by
    exact ambientBooleanContraction_mem_quadraticExterior_coordinate
      secondJetCoreSet ell (localTwoForm 0 p)
        (rationalZero_localTwoForm_mem_quadraticExterior p)
  exact Submodule.mem_sup_left (Submodule.mem_sup_right hlocal)

/-- The rational-zero local Hadamard term is likewise target-clean. -/
theorem rationalZero_ambientTwoHadamard_mem_targetClean
    (p : LocalKleinCoord) (q : TwoForm) :
    ambientTwoHadamard (localTwoForm 0 p) q ∈
      targetCleanSecondJetSpace := by
  exact Submodule.mem_sup_left (Submodule.mem_sup_right
    (rationalZero_ambientTwoHadamard_mem_quadraticExterior p q))

/-- Uniform rational-place version: the exterior square of each rational
local four-space is contained in its transported target-clean second-jet
space. -/
theorem rationalPlace_localTwoForm_mem_targetClean
    (place : Fin 3) (p : LocalKleinCoord) :
    localTwoForm place.castSucc p ∈
      rationalPlaceTargetCleanSecondJetSpace place := by
  fin_cases place
  · exact rationalZero_localTwoForm_mem_targetClean p
  · change localTwoForm 1 p ∈ rationalTargetCleanSecondJetSpace 0
    refine ⟨localTwoForm 0 p, rationalZero_localTwoForm_mem_targetClean p, ?_⟩
    simpa [rationalPlacePerm, rationalPlaceLocalTwoCoordChange] using
      rationalPlaceTwoFormLinear_localTwoForm 0 0 p
  · change localTwoForm 2 p ∈ rationalTargetCleanSecondJetSpace 1
    refine ⟨localTwoForm 0 p, rationalZero_localTwoForm_mem_targetClean p, ?_⟩
    simpa [rationalPlacePerm, rationalPlaceLocalTwoCoordChange] using
      rationalPlaceTwoFormLinear_localTwoForm 1 0 p

/-- Coordinate-free wrapper for the preceding inclusion: the wedge of any
two vectors in a rational closed-place four-space lies in the corresponding
target-clean second-jet space. -/
theorem rationalPlace_squarefreeWedge_mem_targetClean
    (place : Fin 3) (u v : LinearForm)
    (hu : u ∈ closedPlaceLinearSpace place.castSucc)
    (hv : v ∈ closedPlaceLinearSpace place.castSucc) :
    squarefreeWedge u v ∈
      rationalPlaceTargetCleanSecondJetSpace place := by
  rcases exists_localWedgeCoord_of_factors_mem place.castSucc u v hu hv with
    ⟨p, hp⟩
  rw [← hp]
  exact rationalPlace_localTwoForm_mem_targetClean place p

/-- The first-order envelope is contained in every rationally normalized
target-clean second-jet space. -/
theorem firstOrderEnvelopeTwoSpace_le_rationalPlaceTargetClean
    (place : Fin 3) :
    firstOrderEnvelopeTwoSpace ≤
      rationalPlaceTargetCleanSecondJetSpace place := by
  intro p hp
  fin_cases place
  · have hpInf : p ∈ targetTwoSpace ⊓ targetCleanSecondJetSpace := by
      rw [targetTwoSpace_inf_targetCleanSecondJetSpace]
      exact hp
    exact hpInf.2
  · have hpInf : p ∈ targetTwoSpace ⊓
        rationalTargetCleanSecondJetSpace 0 := by
      rw [targetTwoSpace_inf_rationalTargetCleanSecondJetSpace]
      exact hp
    exact hpInf.2
  · have hpInf : p ∈ targetTwoSpace ⊓
        rationalTargetCleanSecondJetSpace 1 := by
      rw [targetTwoSpace_inf_rationalTargetCleanSecondJetSpace]
      exact hp
    exact hpInf.2

/-- Uniform three-rational-place form of equation (11.7). -/
theorem targetTwoSpace_inf_rationalPlaceTargetClean_sup_decomposable
    (place : Fin 3) (q : TwoForm) (hqdec : IsDecomposableTwo q) :
    targetTwoSpace ⊓
        (rationalPlaceTargetCleanSecondJetSpace place ⊔
          Submodule.span F₂ ({q} : Set TwoForm)) =
      firstOrderEnvelopeTwoSpace := by
  fin_cases place
  · exact targetTwoSpace_inf_targetClean_sup_decomposable q hqdec
  · exact targetTwoSpace_inf_rationalTargetClean_sup_decomposable 0 q hqdec
  · exact targetTwoSpace_inf_rationalTargetClean_sup_decomposable 1 q hqdec

/-- The missing affine target coset contains no decomposable form in any of
the three rational clean normalizations. -/
theorem firstOrderMissing_add_rationalPlaceTargetClean_not_decomposable
    (place : Fin 3) (z : TwoForm)
    (hz : z ∈ rationalPlaceTargetCleanSecondJetSpace place) :
    ¬ IsDecomposableTwo (targetTwo firstOrderMissingCoeff + z) := by
  fin_cases place
  · exact firstOrderMissing_add_targetClean_not_decomposable z hz
  · exact firstOrderMissing_add_rationalTargetClean_not_decomposable 0 z hz
  · exact firstOrderMissing_add_rationalTargetClean_not_decomposable 1 z hz

end
end N5
end UnrestrictedBooleanMul
