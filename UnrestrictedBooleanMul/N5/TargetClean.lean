import UnrestrictedBooleanMul.N5.MissingCoset
import UnrestrictedBooleanMul.QuadraticSupport

/-!
# The target-clean second jet

This file formalizes the linear-algebra half of manuscript Lemma 11.4.  At
the rational place zero, the second-jet enlargement consists of the
first-order envelope, the exterior square of the four-dimensional local
block, and all wedges having one factor in the two-dimensional extension
block.  The displayed four-coordinate functional annihilates that entire
space but detects the missing target coefficient `tau`.

Consequently the multiplication target meets the second-jet enlargement in
exactly the first-order envelope.  No search or enumeration is involved.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Coordinate subspace of linear forms supported on `S`. -/
def linearCoordinateSubspace (S : Set (Fin 10)) :
    Submodule F₂ LinearForm where
  carrier := {u | ∀ i, i ∉ S → u i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv i hi
    simp [hu i hi, hv i hi]
  smul_mem' := by
    intro a u hu i hi
    simp [hu i hi]

@[simp] theorem mem_linearCoordinateSubspace
    (S : Set (Fin 10)) (u : LinearForm) :
    u ∈ linearCoordinateSubspace S ↔
      ∀ i, i ∉ S → u i = 0 := by
  rfl

/-- The local four-dimensional block
`K_0 = <a_0,b_0,a_1,b_1>`. -/
def secondJetCoreSet : Set (Fin 10) :=
  {aCoord 0, bCoord 0, aCoord 1, bCoord 1}

def secondJetCoreSpace : Submodule F₂ LinearForm :=
  linearCoordinateSubspace secondJetCoreSet

/-- The two new linear coordinates `E_0 = <a_1,b_1>`. -/
def secondJetExtensionSet : Set (Fin 10) :=
  {aCoord 1, bCoord 1}

def secondJetExtensionSpace : Submodule F₂ LinearForm :=
  linearCoordinateSubspace secondJetExtensionSet

/-- Span of quadratic forms having one factor in a specified linear
subspace. -/
def leftWedgeSpace (E : Submodule F₂ LinearForm) :
    Submodule F₂ TwoForm :=
  Submodule.span F₂
    {p | ∃ u ∈ E, ∃ v : LinearForm, p = squarefreeWedge u v}

/-- The manuscript space
`Z_0 = U + Lambda^2 K_0 + E_0 wedge L`. -/
def targetCleanSecondJetSpace : Submodule F₂ TwoForm :=
  firstOrderEnvelopeTwoSpace ⊔ quadraticExterior secondJetCoreSpace ⊔
    leftWedgeSpace secondJetExtensionSpace

/-- The four-coordinate functional from manuscript Lemma 11.4. -/
def secondJetCleanFunctional : TwoForm →ₗ[F₂] F₂ where
  toFun p :=
    p (quadraticPair (aCoord 0) (bCoord 2) (aCoord_ne_bCoord 0 2)) +
    p (quadraticPair (aCoord 0) (bCoord 3) (aCoord_ne_bCoord 0 3)) +
    p (quadraticPair (aCoord 2) (bCoord 3) (aCoord_ne_bCoord 2 3)) +
    p (quadraticPair (aCoord 2) (bCoord 4) (aCoord_ne_bCoord 2 4))
  map_add' p q := by
    simp only [Pi.add_apply]
    module
  map_smul' a p := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_add]
    module

/-- On the Hankel target, the clean functional is exactly the missing
first-order coefficient. -/
theorem secondJetCleanFunctional_targetTwo (c : TargetCoeff) :
    secondJetCleanFunctional (targetTwo c) =
      firstOrderMissingFunctional c := by
  simp [secondJetCleanFunctional, firstOrderMissingFunctional,
    hankelIndex]

@[simp] theorem secondJetCleanFunctional_missing :
    secondJetCleanFunctional (targetTwo firstOrderMissingCoeff) = 1 := by
  rw [secondJetCleanFunctional_targetTwo]
  exact firstOrderMissingFunctional_missing

theorem secondJetCleanFunctional_squarefreeWedge_core
    (u v : LinearForm) (hu : u ∈ secondJetCoreSpace)
    (hv : v ∈ secondJetCoreSpace) :
    secondJetCleanFunctional (squarefreeWedge u v) = 0 := by
  change ∀ i, i ∉ secondJetCoreSet → u i = 0 at hu
  change ∀ i, i ∉ secondJetCoreSet → v i = 0 at hv
  have hua2 : u (aCoord 2) = 0 := hu _ (by
    simp [secondJetCoreSet, aCoord, bCoord])
  have hub2 : u (bCoord 2) = 0 := hu _ (by
    simp [secondJetCoreSet, aCoord, bCoord])
  have hub3 : u (bCoord 3) = 0 := hu _ (by
    simp [secondJetCoreSet, aCoord, bCoord])
  have hub4 : u (bCoord 4) = 0 := hu _ (by
    simp [secondJetCoreSet, aCoord, bCoord])
  have hva2 : v (aCoord 2) = 0 := hv _ (by
    simp [secondJetCoreSet, aCoord, bCoord])
  have hvb2 : v (bCoord 2) = 0 := hv _ (by
    simp [secondJetCoreSet, aCoord, bCoord])
  have hvb3 : v (bCoord 3) = 0 := hv _ (by
    simp [secondJetCoreSet, aCoord, bCoord])
  have hvb4 : v (bCoord 4) = 0 := hv _ (by
    simp [secondJetCoreSet, aCoord, bCoord])
  simp [secondJetCleanFunctional, squarefreeWedge_pair,
    hua2, hub2, hub3, hub4, hva2, hvb2, hvb3, hvb4]

theorem secondJetCleanFunctional_squarefreeWedge_extension
    (u v : LinearForm) (hu : u ∈ secondJetExtensionSpace) :
    secondJetCleanFunctional (squarefreeWedge u v) = 0 := by
  change ∀ i, i ∉ secondJetExtensionSet → u i = 0 at hu
  have hua0 : u (aCoord 0) = 0 := hu _ (by
    simp [secondJetExtensionSet, aCoord, bCoord])
  have hua2 : u (aCoord 2) = 0 := hu _ (by
    simp [secondJetExtensionSet, aCoord, bCoord])
  have hub2 : u (bCoord 2) = 0 := hu _ (by
    simp [secondJetExtensionSet, aCoord, bCoord])
  have hub3 : u (bCoord 3) = 0 := hu _ (by
    simp [secondJetExtensionSet, aCoord, bCoord])
  have hub4 : u (bCoord 4) = 0 := hu _ (by
    simp [secondJetExtensionSet, aCoord, bCoord])
  simp [secondJetCleanFunctional, squarefreeWedge_pair,
    hua0, hua2, hub2, hub3, hub4]

theorem firstOrderEnvelopeTwoSpace_le_secondJetCleanKernel :
    firstOrderEnvelopeTwoSpace ≤
      LinearMap.ker secondJetCleanFunctional := by
  rintro p ⟨c, hc, rfl⟩
  change secondJetCleanFunctional (targetTwo c) = 0
  rw [secondJetCleanFunctional_targetTwo]
  exact (mem_firstOrderEnvelopeCoeffSpace c).1 hc

theorem quadraticExterior_core_le_secondJetCleanKernel :
    quadraticExterior secondJetCoreSpace ≤
      LinearMap.ker secondJetCleanFunctional := by
  apply Submodule.span_le.mpr
  rintro p ⟨u, hu, v, hv, rfl⟩
  exact (LinearMap.mem_ker).2
    (secondJetCleanFunctional_squarefreeWedge_core u v hu hv)

theorem extensionWedge_le_secondJetCleanKernel :
    leftWedgeSpace secondJetExtensionSpace ≤
      LinearMap.ker secondJetCleanFunctional := by
  apply Submodule.span_le.mpr
  rintro p ⟨u, hu, v, rfl⟩
  exact (LinearMap.mem_ker).2
    (secondJetCleanFunctional_squarefreeWedge_extension u v hu)

theorem targetCleanSecondJetSpace_le_kernel :
    targetCleanSecondJetSpace ≤
      LinearMap.ker secondJetCleanFunctional := by
  exact sup_le
    (sup_le firstOrderEnvelopeTwoSpace_le_secondJetCleanKernel
      quadraticExterior_core_le_secondJetCleanKernel)
    extensionWedge_le_secondJetCleanKernel

/-- Manuscript equation (11.6): the target-clean second-jet enlargement
contains no new multiplication-target direction. -/
theorem targetTwoSpace_inf_targetCleanSecondJetSpace :
    targetTwoSpace ⊓ targetCleanSecondJetSpace =
      firstOrderEnvelopeTwoSpace := by
  apply le_antisymm
  · rintro p ⟨hpT, hpZ⟩
    rcases hpT with ⟨c, rfl⟩
    have hker : targetTwo c ∈
        LinearMap.ker secondJetCleanFunctional :=
      targetCleanSecondJetSpace_le_kernel hpZ
    have hmissing : firstOrderMissingFunctional c = 0 := by
      rw [LinearMap.mem_ker, secondJetCleanFunctional_targetTwo] at hker
      exact hker
    exact ⟨c, (mem_firstOrderEnvelopeCoeffSpace c).2 hmissing, rfl⟩
  · intro p hp
    refine ⟨firstOrderEnvelopeTwoSpace_le_targetTwoSpace hp, ?_⟩
    exact ((le_sup_left : firstOrderEnvelopeTwoSpace ≤
      firstOrderEnvelopeTwoSpace ⊔ quadraticExterior secondJetCoreSpace).trans
        (le_sup_left :
          firstOrderEnvelopeTwoSpace ⊔ quadraticExterior secondJetCoreSpace ≤
            targetCleanSecondJetSpace)) hp

/-- Inclusion form used by later suffix modules. -/
theorem target_mem_targetCleanSecondJetSpace_iff_firstOrder
    (p : TwoForm) (hpT : p ∈ targetTwoSpace) :
    p ∈ targetCleanSecondJetSpace ↔
      p ∈ firstOrderEnvelopeTwoSpace := by
  constructor
  · intro hpZ
    have hp : p ∈ targetTwoSpace ⊓ targetCleanSecondJetSpace :=
      ⟨hpT, hpZ⟩
    rwa [targetTwoSpace_inf_targetCleanSecondJetSpace] at hp
  · intro hp
    exact ((le_sup_left : firstOrderEnvelopeTwoSpace ≤
      firstOrderEnvelopeTwoSpace ⊔ quadraticExterior secondJetCoreSpace).trans
        (le_sup_left :
          firstOrderEnvelopeTwoSpace ⊔ quadraticExterior secondJetCoreSpace ≤
            targetCleanSecondJetSpace)) hp

end

end N5
end UnrestrictedBooleanMul
