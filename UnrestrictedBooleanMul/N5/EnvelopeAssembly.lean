import UnrestrictedBooleanMul.N5.EnvelopeBasisChange

/-!
# Coordinate assembly for the first-order n=5 envelope

This module connects ambient low-product data to the sparse Plücker-kernel
classification already proved in `EnvelopeKernel`.  It only chooses
coordinates in the fixed eight-dimensional envelope and evaluates one
symbolic exterior block; it performs no finite circuit or assignment search.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Linear coordinate realization of the exact first-order envelope inside
the ambient quadratic space. -/
def exactFirstOrderTwoMap : (Fin 8 → F₂) →ₗ[F₂] TwoForm :=
  targetTwoLinear.comp
    (Fintype.linearCombination F₂ exactFirstOrderDirections)

@[simp] theorem exactFirstOrderTwoMap_apply (x : Fin 8 → F₂) :
    exactFirstOrderTwoMap x =
      targetTwo (exactFirstOrderCombination x) := by
  simp [exactFirstOrderTwoMap, exactFirstOrderCombination,
    Fintype.linearCombination_apply, targetTwo]

theorem exactFirstOrderTwoMap_injective :
    Function.Injective exactFirstOrderTwoMap :=
  targetTwoLinear_injective.comp
    exactFirstOrderDirections_linearIndependent.fintypeLinearCombination_injective

/-- Index of the unordered pair in the fixed lexicographic pair table.
Diagonal entries are arbitrary and are never used. -/
private def firstOrderPairIndex (i j : Fin 8) : Fin 28 :=
  ![![0, 0, 1, 2, 3, 4, 5, 6],
    ![0, 0, 7, 8, 9, 10, 11, 12],
    ![1, 7, 0, 13, 14, 15, 16, 17],
    ![2, 8, 13, 0, 18, 19, 20, 21],
    ![3, 9, 14, 18, 0, 22, 23, 24],
    ![4, 10, 15, 19, 22, 0, 25, 26],
    ![5, 11, 16, 20, 23, 25, 0, 27],
    ![6, 12, 17, 21, 24, 26, 27, 0]] i j

/-- Coefficient vectors of the three rational value directions in the exact
first-order basis. -/
def firstOrderLocalValueCoordinates : Fin 3 → (Fin 8 → F₂) :=
  ![Pi.basisFun F₂ (Fin 8) 0,
    Pi.basisFun F₂ (Fin 8) 1,
    Pi.basisFun F₂ (Fin 8) 2]

/-- Coefficient vectors of the corresponding rational first jets. -/
def firstOrderLocalJetCoordinates : Fin 3 → (Fin 8 → F₂) :=
  ![Pi.basisFun F₂ (Fin 8) 3,
    Pi.basisFun F₂ (Fin 8) 4,
    Pi.basisFun F₂ (Fin 8) 5]

/-- The three sparse kernel vectors are precisely the exterior coordinates
of the rational value--jet coefficient planes. -/
theorem firstOrderPlaneCoeff_localCoordinates (i : Fin 3) :
    firstOrderPlaneCoeff (firstOrderLocalValueCoordinates i)
        (firstOrderLocalJetCoordinates i) =
      firstOrderLocalKernelDirections i := by
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [firstOrderPlaneCoeff, firstOrderLocalValueCoordinates,
      firstOrderLocalJetCoordinates, firstOrderLocalKernelDirections,
      firstOrderPairLeft, firstOrderPairRight, Pi.basisFun]

theorem firstOrderLocalCoordinates_linearIndependent (i : Fin 3) :
    LinearIndependent F₂ ![firstOrderLocalValueCoordinates i,
      firstOrderLocalJetCoordinates i] := by
  rw [linearIndependent_fin2]
  fin_cases i
  · constructor
    · intro h
      have hk := congrFun h (3 : Fin 8)
      simp [firstOrderLocalJetCoordinates, Pi.basisFun] at hk
    · intro a
      rcases f2_eq_zero_or_one a with rfl | rfl
      · intro h
        have hk := congrFun h (0 : Fin 8)
        simp [firstOrderLocalValueCoordinates, Pi.basisFun] at hk
      · intro h
        have hk := congrFun h (3 : Fin 8)
        simp [firstOrderLocalValueCoordinates, firstOrderLocalJetCoordinates,
          Pi.basisFun] at hk
  · constructor
    · intro h
      have hk := congrFun h (4 : Fin 8)
      simp [firstOrderLocalJetCoordinates, Pi.basisFun] at hk
    · intro a
      rcases f2_eq_zero_or_one a with rfl | rfl
      · intro h
        have hk := congrFun h (1 : Fin 8)
        simp [firstOrderLocalValueCoordinates, Pi.basisFun] at hk
      · intro h
        have hk := congrFun h (4 : Fin 8)
        simp [firstOrderLocalValueCoordinates, firstOrderLocalJetCoordinates,
          Pi.basisFun] at hk
  · constructor
    · intro h
      have hk := congrFun h (5 : Fin 8)
      simp [firstOrderLocalJetCoordinates, Pi.basisFun] at hk
    · intro a
      rcases f2_eq_zero_or_one a with rfl | rfl
      · intro h
        have hk := congrFun h (2 : Fin 8)
        simp [firstOrderLocalValueCoordinates, Pi.basisFun] at hk
      · intro h
        have hk := congrFun h (5 : Fin 8)
        simp [firstOrderLocalValueCoordinates, firstOrderLocalJetCoordinates,
          Pi.basisFun] at hk

/-- Every distinct pair of exact first-order basis indices occurs, in one
of its two orientations, in the fixed lexicographic pair table. -/
private theorem exists_firstOrderPair_of_ne
    (i j : Fin 8) (hij : i ≠ j) :
    ∃ k : Fin 28,
      (firstOrderPairLeft k = i ∧ firstOrderPairRight k = j) ∨
      (firstOrderPairLeft k = j ∧ firstOrderPairRight k = i) := by
  refine ⟨firstOrderPairIndex i j, ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [firstOrderPairIndex, firstOrderPairLeft,
      firstOrderPairRight]

/-- Equality of the lexicographically ordered Pluecker coordinates is
exactly equality of the corresponding squarefree exterior two-forms. -/
theorem squarefreeWedge_eq_of_firstOrderPlaneCoeff_eq
    (x y z w : Fin 8 → F₂)
    (h : firstOrderPlaneCoeff x y = firstOrderPlaneCoeff z w) :
    squarefreeWedge x y = squarefreeWedge z w := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  rcases exists_firstOrderPair_of_ne i j hij with
    ⟨k, ⟨hki, hkj⟩ | ⟨hkj, hki⟩⟩
  · have hk := congrFun h k
    simpa [squarefreeWedge_pair, firstOrderPlaneCoeff, hki, hkj] using hk
  · have hk := congrFun h k
    simpa [squarefreeWedge_pair, firstOrderPlaneCoeff, hki, hkj,
      add_comm] using hk

/-- The lexicographic Pluecker table also reflects sums of two exterior
two-forms. -/
theorem squarefreeWedge_add_eq_of_firstOrderPlaneCoeff_add_eq
    (x y z w r s : Fin 8 → F₂)
    (h : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderPlaneCoeff r s) :
    squarefreeWedge x y + squarefreeWedge z w =
      squarefreeWedge r s := by
  funext t
  rcases QuadraticIndex.exists_pair t with ⟨i, j, hij, rfl⟩
  rcases exists_firstOrderPair_of_ne i j hij with
    ⟨k, ⟨hki, hkj⟩ | ⟨hkj, hki⟩⟩
  · have hk := congrFun h k
    simpa [squarefreeWedge_pair, firstOrderPlaneCoeff, hki, hkj] using hk
  · have hk := congrFun h k
    simpa [squarefreeWedge_pair, firstOrderPlaneCoeff, hki, hkj,
      add_comm] using hk

/-- A sum of two decomposable two-forms which is again supported on an
independent pair cannot have four independent endpoint vectors. -/
private theorem not_linearIndependent_four_of_squarefreeWedge_add_eq
    (x y r s z w : Fin 8 → F₂)
    (hzw : LinearIndependent F₂ ![z, w])
    (hwedge : squarefreeWedge x y + squarefreeWedge r s =
      squarefreeWedge z w) :
    ¬ LinearIndependent F₂ ![x, y, r, s] := by
  intro hfour
  have hspan :
      Submodule.span F₂ (Set.range ![x, y, r, s]) =
        Submodule.span F₂ (Set.range ![z, w]) := by
    calc
      Submodule.span F₂ (Set.range ![x, y, r, s]) =
          quadraticSupport
            (squarefreeWedge x y + squarefreeWedge r s) :=
        (quadraticSupport_two_wedges x y r s hfour).symm
      _ = quadraticSupport (squarefreeWedge z w) :=
        congrArg quadraticSupport hwedge
      _ = Submodule.span F₂ (Set.range ![z, w]) :=
        quadraticSupport_squarefreeWedge z w hzw
  have hrank := congrArg
    (fun P : Submodule F₂ (Fin 8 → F₂) => Module.finrank F₂ P) hspan
  have hfourRank : Module.finrank F₂
      (Submodule.span F₂ (Set.range ![x, y, r, s])) = 4 := by
    simpa using finrank_span_eq_card hfour
  have htwoRank : Module.finrank F₂
      (Submodule.span F₂ (Set.range ![z, w])) = 2 := by
    simpa using finrank_span_eq_card hzw
  rw [hfourRank, htwoRank] at hrank
  omega

private theorem quadraticSupport_zero_eight :
    quadraticSupport (0 : QuadraticForm 8) = ⊥ := by
  ext v
  simp [quadraticSupport, quadraticContraction, alternatingCoeff]
  change (0 : Fin 8 → F₂) = v ↔ v = 0
  exact eq_comm

private theorem squarefreeWedge_ne_zero_of_linearIndependent_eight
    (u v : Fin 8 → F₂) (huv : LinearIndependent F₂ ![u, v]) :
    squarefreeWedge u v ≠ 0 := by
  intro hzero
  have hsupport := quadraticSupport_squarefreeWedge u v huv
  rw [hzero, quadraticSupport_zero_eight] at hsupport
  have huMem : u ∈ Submodule.span F₂ (Set.range ![u, v]) :=
    Submodule.subset_span ⟨0, by simp⟩
  rw [← hsupport] at huMem
  have hu0 : u = 0 := by simpa using huMem
  exact (huv.ne_zero 0) hu0

/-- Two independent planes whose four displayed generators are dependent
have a nonzero common vector. -/
private theorem exists_nonzero_common_span_of_four_dependent
    (x y r s : Fin 8 → F₂)
    (hxy : LinearIndependent F₂ ![x, y])
    (hrs : LinearIndependent F₂ ![r, s])
    (hdep : ¬ LinearIndependent F₂ ![x, y, r, s]) :
    ∃ p : Fin 8 → F₂,
      p ≠ 0 ∧
      p ∈ Submodule.span F₂ ({x, y} : Set (Fin 8 → F₂)) ∧
      p ∈ Submodule.span F₂ ({r, s} : Set (Fin 8 → F₂)) := by
  let A := Submodule.span F₂ ({x, y} : Set (Fin 8 → F₂))
  let K := Submodule.span F₂ ({r, s} : Set (Fin 8 → F₂))
  have hinf : A ⊓ K ≠ ⊥ := by
    intro hinf
    have hdisjoint : Disjoint A K := by
      rw [disjoint_iff_inf_le, hinf]
    apply hdep
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    let leftPart : Fin 8 → F₂ := f 0 • x + f 1 • y
    let rightPart : Fin 8 → F₂ := f 2 • r + f 3 • s
    have htotal : leftPart + rightPart = 0 := by
      simpa [leftPart, rightPart, Fin.sum_univ_succ, add_assoc] using hf
    have heq : leftPart = rightPart := by
      funext k
      exact CharTwo.add_eq_zero.mp (congrFun htotal k)
    have hleftA : leftPart ∈ A := by
      apply Submodule.mem_span_pair.mpr
      exact ⟨f 0, f 1, rfl⟩
    have hrightK : rightPart ∈ K := by
      apply Submodule.mem_span_pair.mpr
      exact ⟨f 2, f 3, rfl⟩
    have hleftK : leftPart ∈ K := by
      rw [heq]
      exact hrightK
    have hleftZero : leftPart = 0 :=
      Submodule.disjoint_def.mp hdisjoint leftPart hleftA hleftK
    have hrightZero : rightPart = 0 := heq.symm.trans hleftZero
    have hleftSum :
        ∑ j : Fin 2, ![f 0, f 1] j • ![x, y] j = 0 := by
      simpa [leftPart, Fin.sum_univ_succ] using hleftZero
    have hrightSum :
        ∑ j : Fin 2, ![f 2, f 3] j • ![r, s] j = 0 := by
      simpa [rightPart, Fin.sum_univ_succ] using hrightZero
    have hleftCoeff := (Fintype.linearIndependent_iff.mp hxy)
      ![f 0, f 1] hleftSum
    have hrightCoeff := (Fintype.linearIndependent_iff.mp hrs)
      ![f 2, f 3] hrightSum
    fin_cases i
    · exact hleftCoeff 0
    · exact hleftCoeff 1
    · exact hrightCoeff 0
    · exact hrightCoeff 1
  obtain ⟨p, hp⟩ := Submodule.nonzero_mem_of_bot_lt
    (bot_lt_iff_ne_bot.mpr hinf)
  refine ⟨p.1, ?_, p.property.1, p.property.2⟩
  intro hp0
  apply hp
  exact Subtype.ext hp0

/-- One nonzero local-kernel difference forces the first factor plane to
meet the corresponding rational value--jet plane in a nonzero line.  This is
the algebraic incidence content of the manuscript's "one local rotation". -/
theorem oneLocalKernelDifference_common_line
    (x y z w : Fin 8 → F₂) (i : Fin 3)
    (hxy : LinearIndependent F₂ ![x, y])
    (hzw : LinearIndependent F₂ ![z, w])
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections i) :
    ∃ p : Fin 8 → F₂,
      p ≠ 0 ∧
      p ∈ Submodule.span F₂ ({x, y} : Set (Fin 8 → F₂)) ∧
      p ∈ Submodule.span F₂
        ({firstOrderLocalValueCoordinates i,
          firstOrderLocalJetCoordinates i} : Set (Fin 8 → F₂)) := by
  have hcoeff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderPlaneCoeff (firstOrderLocalValueCoordinates i)
        (firstOrderLocalJetCoordinates i) :=
    hdiff.trans (firstOrderPlaneCoeff_localCoordinates i).symm
  have hwedge := squarefreeWedge_add_eq_of_firstOrderPlaneCoeff_add_eq
    x y z w (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i) hcoeff
  have hwedge' : squarefreeWedge x y +
      squarefreeWedge (firstOrderLocalValueCoordinates i)
        (firstOrderLocalJetCoordinates i) = squarefreeWedge z w := by
    funext t
    have ht := congrFun hwedge t
    simp only [Pi.add_apply] at ht ⊢
    rw [← ht, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hdep := not_linearIndependent_four_of_squarefreeWedge_add_eq
    x y (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i) z w hzw hwedge'
  exact exists_nonzero_common_span_of_four_dependent
    x y (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i) hxy
        (firstOrderLocalCoordinates_linearIndependent i) hdep

private theorem mem_span_pair_cases_f2'
    {V : Type*} [AddCommGroup V] [Module F₂ V]
    (x y p : V) (hp : p ∈ Submodule.span F₂ ({x, y} : Set V)) :
    p = 0 ∨ p = x ∨ p = y ∨ p = x + y := by
  rcases Submodule.mem_span_pair.mp hp with ⟨a, b, hab⟩
  rcases f2_eq_zero_or_one a with rfl | rfl <;>
    rcases f2_eq_zero_or_one b with rfl | rfl
  · exact Or.inl (by simpa using hab.symm)
  · exact Or.inr (Or.inr (Or.inl (by simpa using hab.symm)))
  · exact Or.inr (Or.inl (by simpa using hab.symm))
  · exact Or.inr (Or.inr (Or.inr (by simpa using hab.symm)))

private theorem pair_dependent_classification_f2'
    {V : Type*} [AddCommGroup V] [Module F₂ V]
    (u v : V) (hdep : ¬ LinearIndependent F₂ ![u, v]) :
    u = 0 ∨ v = 0 ∨ u = v := by
  by_cases hu : u = 0
  · exact Or.inl hu
  by_cases hv : v = 0
  · exact Or.inr (Or.inl hv)
  by_cases huv : u = v
  · exact Or.inr (Or.inr huv)
  exfalso
  apply hdep
  rw [linearIndependent_fin2]
  change v ≠ 0 ∧ ∀ a : F₂, a • v ≠ u
  refine ⟨hv, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hu
  · simpa using Ne.symm huv

private theorem squarefreeWedge_comm_eight (u v : Fin 8 → F₂) :
    squarefreeWedge u v = squarefreeWedge v u := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp only [squarefreeWedge_pair]
  ring

private theorem squarefreeWedge_self_eight (u : Fin 8 → F₂) :
    squarefreeWedge u u = 0 := by
  funext s
  rcases QuadraticIndex.exists_pair s with ⟨i, j, hij, rfl⟩
  simp [squarefreeWedge_pair, mul_comm]

/-- The six ordered basis changes preserve the coefficient exterior
two-form. -/
private theorem squarefreeWedge_basisPair_eight
    (g : PlaneBasisChange) (u v : Fin 8 → F₂) :
    squarefreeWedge (g.basisPair u v).1 (g.basisPair u v).2 =
      squarefreeWedge u v := by
  cases g with
  | identity => rfl
  | swap => exact squarefreeWedge_comm_eight v u
  | rotateRight =>
      change squarefreeWedge u (u + v) = squarefreeWedge u v
      rw [squarefreeWedge_add_right, squarefreeWedge_self_eight, zero_add]
  | rotateLeft =>
      change squarefreeWedge (u + v) v = squarefreeWedge u v
      rw [squarefreeWedge_add_left, squarefreeWedge_self_eight, add_zero]
  | cycleRight =>
      change squarefreeWedge v (u + v) = squarefreeWedge u v
      rw [squarefreeWedge_add_right, squarefreeWedge_self_eight, add_zero,
        squarefreeWedge_comm_eight]
  | cycleLeft =>
      change squarefreeWedge (u + v) u = squarefreeWedge u v
      rw [squarefreeWedge_add_left, squarefreeWedge_self_eight, zero_add,
        squarefreeWedge_comm_eight]

/-- Generic `F₂` version of the six-basis classification. -/
private theorem exists_planeBasisChange_of_span_eq'
    {V : Type*} [AddCommGroup V] [Module F₂ V]
    (u v u' v' : V)
    (hind' : LinearIndependent F₂ ![u', v'])
    (hspan : Submodule.span F₂ ({u', v'} : Set V) =
      Submodule.span F₂ ({u, v} : Set V)) :
    ∃ g : PlaneBasisChange,
      u' = (g.basisPair u v).1 ∧ v' = (g.basisPair u v).2 := by
  have huMem : u' ∈ Submodule.span F₂ ({u, v} : Set V) := by
    rw [← hspan]
    exact Submodule.subset_span (by simp)
  have hvMem : v' ∈ Submodule.span F₂ ({u, v} : Set V) := by
    rw [← hspan]
    exact Submodule.subset_span (by simp)
  have hu0 : u' ≠ 0 := hind'.ne_zero 0
  have hv0 : v' ≠ 0 := hind'.ne_zero 1
  have huv : u' ≠ v' := by
    intro huv
    have h01 : (0 : Fin 2) = 1 := hind'.injective (by simpa using huv)
    exact Fin.zero_ne_one h01
  rcases mem_span_pair_cases_f2' u v u' huMem with
    hu'0 | hu'u | hu'v | hu'sum
  · exact (hu0 hu'0).elim
  · rcases mem_span_pair_cases_f2' u v v' hvMem with
      hv'0 | hv'u | hv'v | hv'sum
    · exact (hv0 hv'0).elim
    · exact (huv (hu'u.trans hv'u.symm)).elim
    · exact ⟨.identity, by simp [PlaneBasisChange.basisPair, hu'u, hv'v]⟩
    · exact ⟨.rotateRight,
        by simp [PlaneBasisChange.basisPair, hu'u, hv'sum]⟩
  · rcases mem_span_pair_cases_f2' u v v' hvMem with
      hv'0 | hv'u | hv'v | hv'sum
    · exact (hv0 hv'0).elim
    · exact ⟨.swap, by simp [PlaneBasisChange.basisPair, hu'v, hv'u]⟩
    · exact (huv (hu'v.trans hv'v.symm)).elim
    · exact ⟨.cycleRight,
        by simp [PlaneBasisChange.basisPair, hu'v, hv'sum]⟩
  · rcases mem_span_pair_cases_f2' u v v' hvMem with
      hv'0 | hv'u | hv'v | hv'sum
    · exact (hv0 hv'0).elim
    · exact ⟨.cycleLeft,
        by simp [PlaneBasisChange.basisPair, hu'sum, hv'u]⟩
    · exact ⟨.rotateLeft,
        by simp [PlaneBasisChange.basisPair, hu'sum, hv'v]⟩
    · exact (huv (hu'sum.trans hv'sum.symm)).elim

/-- A nonzero vector in a two-generator `F₂` plane can be made the first
vector by one of the six ordered basis changes. -/
private theorem exists_basisChange_first_eq_of_mem_span
    {V : Type*} [AddCommGroup V] [Module F₂ V]
    (x y p : V) (hp0 : p ≠ 0)
    (hp : p ∈ Submodule.span F₂ ({x, y} : Set V)) :
    ∃ g : PlaneBasisChange, (g.basisPair x y).1 = p := by
  rcases mem_span_pair_cases_f2' x y p hp with hp | hp | hp | hp
  · exact (hp0 hp).elim
  · exact ⟨.identity, by simpa [PlaneBasisChange.basisPair] using hp.symm⟩
  · exact ⟨.swap, by simpa [PlaneBasisChange.basisPair] using hp.symm⟩
  · exact ⟨.rotateLeft,
      by simpa [PlaneBasisChange.basisPair] using hp.symm⟩

/-- Normalized incidence form of a one-local-kernel difference: after basis
changes, the first factor plane and the rational value--jet plane have the
same first generator. -/
theorem oneLocalKernelDifference_aligned_common_generator
    (x y z w : Fin 8 → F₂) (i : Fin 3)
    (hxy : LinearIndependent F₂ ![x, y])
    (hzw : LinearIndependent F₂ ![z, w])
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections i) :
    ∃ (p q t : Fin 8 → F₂) (g h : PlaneBasisChange),
      p ≠ 0 ∧
      g.basisPair x y = (p, q) ∧
      h.basisPair (firstOrderLocalValueCoordinates i)
        (firstOrderLocalJetCoordinates i) = (p, t) := by
  rcases oneLocalKernelDifference_common_line x y z w i hxy hzw hdiff with
    ⟨p, hp0, hpXY, hpLocal⟩
  rcases exists_basisChange_first_eq_of_mem_span x y p hp0 hpXY with
    ⟨g, hg⟩
  rcases exists_basisChange_first_eq_of_mem_span
      (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i) p hp0 hpLocal with ⟨h, hh⟩
  let q := (g.basisPair x y).2
  let t := (h.basisPair (firstOrderLocalValueCoordinates i)
    (firstOrderLocalJetCoordinates i)).2
  refine ⟨p, q, t, g, h, hp0, ?_, ?_⟩
  · exact Prod.ext hg rfl
  · exact Prod.ext hh rfl

/-- The manuscript stores a quadratic plane as `[c,q]`; swapping its two
independent generators preserves linear independence. -/
private theorem orderedQuadraticPair_linearIndependent
    (q c : TwoForm)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    LinearIndependent F₂ ![q, c] := by
  rcases quadraticPlaneDirections_independent_nonzero_ne q c hind with
    ⟨hq, hc, hqc⟩
  rw [linearIndependent_fin2]
  change c ≠ 0 ∧ ∀ a : F₂, a • c ≠ q
  refine ⟨hc, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hq
  · simpa using Ne.symm hqc

/-- Independent quadratic factors in the exact envelope have independent
coordinates because the coordinate realization is injective. -/
theorem exactFirstOrderCoordinates_linearIndependent
    (q c : TwoForm) (x y : Fin 8 → F₂)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c)) :
    LinearIndependent F₂ ![x, y] := by
  rcases quadraticPlaneDirections_independent_nonzero_ne q c hind with
    ⟨hq, hc, hqc⟩
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hq
    calc
      q = exactFirstOrderTwoMap x := hx
      _ = exactFirstOrderTwoMap 0 := congrArg exactFirstOrderTwoMap hx0
      _ = 0 := exactFirstOrderTwoMap.map_zero
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hc
    calc
      c = exactFirstOrderTwoMap y := hy
      _ = exactFirstOrderTwoMap 0 := congrArg exactFirstOrderTwoMap hy0
      _ = 0 := exactFirstOrderTwoMap.map_zero
  have hxy : x ≠ y := by
    intro hxy
    apply hqc
    rw [hx, hy, hxy]
  rw [linearIndependent_fin2]
  change y ≠ 0 ∧ ∀ a : F₂, a • y ≠ x
  refine ⟨hy0, ?_⟩
  intro a
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simpa using Ne.symm hx0
  · simpa using Ne.symm hxy

/-- In characteristic two, a zero sum of the two Pluecker vectors forces
equality of the coefficient planes. -/
theorem firstOrderCoordinate_span_eq_of_planeCoeff_add_eq_zero
    (x y z w : Fin 8 → F₂)
    (hxy : LinearIndependent F₂ ![x, y])
    (hzw : LinearIndependent F₂ ![z, w])
    (hzero : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff z w = 0) :
    Submodule.span F₂ (Set.range ![x, y]) =
      Submodule.span F₂ (Set.range ![z, w]) := by
  have hcoeff : firstOrderPlaneCoeff x y =
      firstOrderPlaneCoeff z w := by
    funext k
    exact CharTwo.add_eq_zero.mp (congrFun hzero k)
  have hwedge := squarefreeWedge_eq_of_firstOrderPlaneCoeff_eq
    x y z w hcoeff
  have hsupport := congrArg quadraticSupport hwedge
  rw [quadraticSupport_squarefreeWedge x y hxy,
    quadraticSupport_squarefreeWedge z w hzw] at hsupport
  exact hsupport

private theorem range_finTwo_eq_pair {V : Type*} (u v : V) :
    Set.range ![u, v] = ({u, v} : Set V) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- Full one-rotation normal form.  The two factor planes and the rational
value--jet plane can be based as `(p,q)`, `(p,q+t)`, and `(p,t)` with the
same nonzero first generator. -/
theorem oneLocalKernelDifference_normalForm
    (x y z w : Fin 8 → F₂) (i : Fin 3)
    (hxy : LinearIndependent F₂ ![x, y])
    (hzw : LinearIndependent F₂ ![z, w])
    (hdiff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderLocalKernelDirections i) :
    ∃ (p q t : Fin 8 → F₂) (g h k : PlaneBasisChange),
      p ≠ 0 ∧
      g.basisPair x y = (p, q) ∧
      h.basisPair (firstOrderLocalValueCoordinates i)
          (firstOrderLocalJetCoordinates i) = (p, t) ∧
      k.basisPair z w = (p, q + t) := by
  rcases oneLocalKernelDifference_aligned_common_generator
      x y z w i hxy hzw hdiff with ⟨p, q, t, g, h, hp0, hg, hh⟩
  have hxyWedge : squarefreeWedge p q = squarefreeWedge x y := by
    have hchange := squarefreeWedge_basisPair_eight g x y
    rw [hg] at hchange
    exact hchange
  have hlocalWedge : squarefreeWedge p t =
      squarefreeWedge (firstOrderLocalValueCoordinates i)
        (firstOrderLocalJetCoordinates i) := by
    have hchange := squarefreeWedge_basisPair_eight h
      (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i)
    rw [hh] at hchange
    exact hchange
  have hcoeff : firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
      firstOrderPlaneCoeff (firstOrderLocalValueCoordinates i)
        (firstOrderLocalJetCoordinates i) :=
    hdiff.trans (firstOrderPlaneCoeff_localCoordinates i).symm
  have horiginal := squarefreeWedge_add_eq_of_firstOrderPlaneCoeff_add_eq
    x y z w (firstOrderLocalValueCoordinates i)
      (firstOrderLocalJetCoordinates i) hcoeff
  have hrotated : squarefreeWedge x y +
      squarefreeWedge (firstOrderLocalValueCoordinates i)
        (firstOrderLocalJetCoordinates i) = squarefreeWedge z w := by
    funext a
    have ha := congrFun horiginal a
    simp only [Pi.add_apply] at ha ⊢
    rw [← ha, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hpqtWedge : squarefreeWedge p (q + t) =
      squarefreeWedge z w := by
    rw [squarefreeWedge_add_right, hxyWedge, hlocalWedge]
    exact hrotated
  have hzwNe := squarefreeWedge_ne_zero_of_linearIndependent_eight z w hzw
  have hpqt : LinearIndependent F₂ ![p, q + t] := by
    by_contra hdep
    rcases pair_dependent_classification_f2' p (q + t) hdep with
      hp | hqt | hpqt
    · exact hp0 hp
    · apply hzwNe
      rw [← hpqtWedge, hqt, squarefreeWedge_zero_right]
    · apply hzwNe
      rw [← hpqtWedge, ← hpqt, squarefreeWedge_self_eight]
  have hspanRange :
      Submodule.span F₂ (Set.range ![p, q + t]) =
        Submodule.span F₂ (Set.range ![z, w]) := by
    calc
      Submodule.span F₂ (Set.range ![p, q + t]) =
          quadraticSupport (squarefreeWedge p (q + t)) :=
        (quadraticSupport_squarefreeWedge p (q + t) hpqt).symm
      _ = quadraticSupport (squarefreeWedge z w) :=
        congrArg quadraticSupport hpqtWedge
      _ = Submodule.span F₂ (Set.range ![z, w]) :=
        quadraticSupport_squarefreeWedge z w hzw
  rw [range_finTwo_eq_pair, range_finTwo_eq_pair] at hspanRange
  rcases exists_planeBasisChange_of_span_eq'
      z w p (q + t) hpqt hspanRange with ⟨k, hk1, hk2⟩
  refine ⟨p, q, t, g, h, k, hp0, hg, hh, ?_⟩
  exact Prod.ext hk1.symm hk2.symm

/-- Equality of coefficient spans lifts through the exact first-order
coordinate map to equality of the represented quadratic planes. -/
theorem quadraticPlane_span_eq_of_firstOrderCoordinate_span_eq
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂)
    (hx : q = exactFirstOrderTwoMap x)
    (hy : c = exactFirstOrderTwoMap y)
    (hz : q' = exactFirstOrderTwoMap z)
    (hw : c' = exactFirstOrderTwoMap w)
    (hspan : Submodule.span F₂ (Set.range ![x, y]) =
      Submodule.span F₂ (Set.range ![z, w])) :
    Submodule.span F₂ ({q, c} : Set TwoForm) =
      Submodule.span F₂ ({q', c'} : Set TwoForm) := by
  rw [range_finTwo_eq_pair, range_finTwo_eq_pair] at hspan
  have hmap := congrArg
    (fun P : Submodule F₂ (Fin 8 → F₂) =>
      P.map exactFirstOrderTwoMap) hspan
  simpa only [Submodule.map_span, Set.image_insert_eq,
    Set.image_singleton, ← hx, ← hy, ← hz, ← hw] using hmap

/-- The zero local-kernel branch of the Pluecker comparison is exactly the
equal-plane case, hence differs by one of the six ordered basis changes. -/
theorem exists_planeBasisChange_of_firstOrderPlaneCoeff_add_eq_zero
    (q c q' c' : TwoForm) (x y z w : Fin 8 → F₂)
    (hx : q = targetTwo (exactFirstOrderCombination x))
    (hy : c = targetTwo (exactFirstOrderCombination y))
    (hz : q' = targetTwo (exactFirstOrderCombination z))
    (hw : c' = targetTwo (exactFirstOrderCombination w))
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hzero : firstOrderPlaneCoeff x y +
      firstOrderPlaneCoeff z w = 0) :
    ∃ g : PlaneBasisChange,
      q' = (g.basisPair q c).1 ∧ c' = (g.basisPair q c).2 := by
  have hxMap : q = exactFirstOrderTwoMap x := by simpa using hx
  have hyMap : c = exactFirstOrderTwoMap y := by simpa using hy
  have hzMap : q' = exactFirstOrderTwoMap z := by simpa using hz
  have hwMap : c' = exactFirstOrderTwoMap w := by simpa using hw
  have hxy := exactFirstOrderCoordinates_linearIndependent
    q c x y hxMap hyMap hind
  have hzw := exactFirstOrderCoordinates_linearIndependent
    q' c' z w hzMap hwMap hind'
  have hcoeffSpan :=
    firstOrderCoordinate_span_eq_of_planeCoeff_add_eq_zero
      x y z w hxy hzw hzero
  have hplaneSpan :=
    quadraticPlane_span_eq_of_firstOrderCoordinate_span_eq
      q c q' c' x y z w hxMap hyMap hzMap hwMap hcoeffSpan
  exact exists_planeBasisChange_of_span_eq q c q' c' hind' hplaneSpan.symm

/-- Every two-form in the first-order envelope has coordinates in the exact
eight-direction basis. -/
theorem exists_exactFirstOrderTwoCombination
    (q : TwoForm) (hq : q ∈ firstOrderEnvelopeTwoSpace) :
    ∃ x : Fin 8 → F₂, q = targetTwo (exactFirstOrderCombination x) := by
  rcases hq with ⟨d, hd, hdq⟩
  rcases exists_exactFirstOrderCombination d hd with ⟨x, hxd⟩
  refine ⟨x, ?_⟩
  rw [hxd]
  exact hdq.symm

/-- The `2A,2B` coordinate block of the ambient exterior product of two
target forms is exactly `targetCrossWedge`. -/
theorem ambientWedgeTwo_targetTwo_cross
    (d e : TargetCoeff) (i k j l : Fin 5) :
    ambientWedgeTwo (targetTwo d) (targetTwo e)
        (aCoord i) (aCoord k) (bCoord j) (bCoord l) =
      targetCrossWedge d e i k j l := by
  have haa (t : TargetCoeff) (r s : Fin 5) :
      ambientTwoCoeff (targetTwo t) (aCoord r) (aCoord s) = 0 := by
    by_cases hrs : r = s
    · subst s
      simp
    · simp [ambientTwoCoeff, hrs]
  have hbb (t : TargetCoeff) (r s : Fin 5) :
      ambientTwoCoeff (targetTwo t) (bCoord r) (bCoord s) = 0 := by
    by_cases hrs : r = s
    · subst s
      simp
    · simp [ambientTwoCoeff, hrs]
  simp [ambientWedgeTwo, targetCrossWedge, crossWedge, hankelMatrix,
    haa, hbb]

/-- Ambient quartic equality between target forms implies equality in the
cross-wedge coordinate model used by the envelope kernel theorem. -/
theorem targetCrossWedge_eq_of_ambientWedgeTwo_eq
    (d e d' e' : TargetCoeff)
    (hfour : ambientWedgeTwo (targetTwo d) (targetTwo e) =
      ambientWedgeTwo (targetTwo d') (targetTwo e')) :
    targetCrossWedge d e = targetCrossWedge d' e' := by
  funext i k j l
  rw [← ambientWedgeTwo_targetTwo_cross,
    ← ambientWedgeTwo_targetTwo_cross]
  exact congrFun (congrFun (congrFun (congrFun hfour (aCoord i))
    (aCoord k)) (bCoord j)) (bCoord l)

/-- Coordinate realization of four quadratic factors in the first-order
envelope, together with the three sparse possibilities for their Plücker
difference. -/
theorem firstOrderPlaneCoeff_classification_of_ambientWedge_eq
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hfour : ambientWedgeTwo q c = ambientWedgeTwo q' c') :
    ∃ x y z w : Fin 8 → F₂,
      q = targetTwo (exactFirstOrderCombination x) ∧
      c = targetTwo (exactFirstOrderCombination y) ∧
      q' = targetTwo (exactFirstOrderCombination z) ∧
      c' = targetTwo (exactFirstOrderCombination w) ∧
      (firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w = 0 ∨
        (∃ i : Fin 3, firstOrderPlaneCoeff x y +
          firstOrderPlaneCoeff z w = firstOrderLocalKernelDirections i) ∨
        ∃ i j : Fin 3, i ≠ j ∧
          firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
            firstOrderLocalKernelDirections i +
              firstOrderLocalKernelDirections j) := by
  rcases exists_exactFirstOrderTwoCombination q hq with ⟨x, hx⟩
  rcases exists_exactFirstOrderTwoCombination c hc with ⟨y, hy⟩
  rcases exists_exactFirstOrderTwoCombination q' hq' with ⟨z, hz⟩
  rcases exists_exactFirstOrderTwoCombination c' hc' with ⟨w, hw⟩
  refine ⟨x, y, z, w, hx, hy, hz, hw, ?_⟩
  apply firstOrderPlaneCoeff_difference_classification x y z w
  apply targetCrossWedge_eq_of_ambientWedgeTwo_eq
  simpa only [← hx, ← hy, ← hz, ← hw] using hfour

/-- Refined ambient quartic classification for two independent quadratic
planes.  The zero Pluecker difference has already been converted to an
actual basis change; only the one- and two-local-rotation branches remain. -/
theorem independentFirstOrderPlane_classification_of_ambientWedge_eq
    (q c q' c' : TwoForm)
    (hq : q ∈ firstOrderEnvelopeTwoSpace)
    (hc : c ∈ firstOrderEnvelopeTwoSpace)
    (hq' : q' ∈ firstOrderEnvelopeTwoSpace)
    (hc' : c' ∈ firstOrderEnvelopeTwoSpace)
    (hind : LinearIndependent F₂ (quadraticPlaneDirections q c))
    (hind' : LinearIndependent F₂ (quadraticPlaneDirections q' c'))
    (hfour : ambientWedgeTwo q c = ambientWedgeTwo q' c') :
    (∃ g : PlaneBasisChange,
      q' = (g.basisPair q c).1 ∧ c' = (g.basisPair q c).2) ∨
    ∃ x y z w : Fin 8 → F₂,
      q = targetTwo (exactFirstOrderCombination x) ∧
      c = targetTwo (exactFirstOrderCombination y) ∧
      q' = targetTwo (exactFirstOrderCombination z) ∧
      c' = targetTwo (exactFirstOrderCombination w) ∧
      ((∃ i : Fin 3, firstOrderPlaneCoeff x y +
          firstOrderPlaneCoeff z w = firstOrderLocalKernelDirections i) ∨
        ∃ i j : Fin 3, i ≠ j ∧
          firstOrderPlaneCoeff x y + firstOrderPlaneCoeff z w =
            firstOrderLocalKernelDirections i +
              firstOrderLocalKernelDirections j) := by
  rcases firstOrderPlaneCoeff_classification_of_ambientWedge_eq
      q c q' c' hq hc hq' hc' hfour with
    ⟨x, y, z, w, hx, hy, hz, hw, hzero | hone | htwo⟩
  · exact Or.inl
      (exists_planeBasisChange_of_firstOrderPlaneCoeff_add_eq_zero
        q c q' c' x y z w hx hy hz hw hind hind' hzero)
  · exact Or.inr ⟨x, y, z, w, hx, hy, hz, hw, Or.inl hone⟩
  · exact Or.inr ⟨x, y, z, w, hx, hy, hz, hw, Or.inr htwo⟩

end

end N5
end UnrestrictedBooleanMul
