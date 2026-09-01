import UnrestrictedBooleanMul.N5.DisplacementRank
import Mathlib.FieldTheory.Finiteness

/-!
# Sparse relations in defect spaces

This module gives the relation kernel the sparse algebraic interface used by
the Fano-plane part of the five-term argument.  A relation is represented by
the indicator of its finite support.  Lines have three terms and Fano
quadrilaterals have four; their relation-map images are the corresponding
sums of chosen lifts.

Nothing here enumerates subspaces or quotient points.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Coefficient vector which is one exactly on `S`. -/
noncomputable def relationIndicator {X : Type*} [Fintype X]
    (S : Finset X) : X → F₂ := by
  classical
  exact fun x => if x ∈ S then 1 else 0

/-- Finite support of a coefficient vector. -/
noncomputable def relationSupport {X : Type*} [Fintype X]
    (a : X → F₂) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => a x ≠ 0)

@[simp] theorem mem_relationSupport {X : Type*} [Fintype X]
    (a : X → F₂) (x : X) :
    x ∈ relationSupport a ↔ a x ≠ 0 := by
  classical
  simp [relationSupport]

@[simp] theorem relationSupport_indicator {X : Type*} [Fintype X]
    (S : Finset X) : relationSupport (relationIndicator S) = S := by
  classical
  ext x
  by_cases hx : x ∈ S <;> simp [relationIndicator, hx]

/-- Over `F₂`, a coefficient vector is the indicator of its support. -/
theorem relationIndicator_support_eq {X : Type*} [Fintype X]
    (a : X → F₂) : relationIndicator (relationSupport a) = a := by
  classical
  funext x
  rcases f2_eq_zero_or_one (a x) with hx | hx
  · simp [relationIndicator, hx]
  · simp [relationIndicator, hx]

theorem coefficientSum_relationIndicator
    {X V : Type*} [Fintype X] [AddCommGroup V] [Module F₂ V]
    (v : X → V) (S : Finset X) :
    coefficientSum v (relationIndicator S) = ∑ x ∈ S, v x := by
  classical
  simp [coefficientSum, relationIndicator]

/-- A sparse support whose quotient points sum to zero. -/
structure SparseRelationSupport {X : Type*} [Fintype X]
    (q : X → QuadraticQuotient) where
  support : Finset X
  sum_eq_zero : ∑ x ∈ support, q x = 0

/-- The coefficient vector attached to a sparse relation support. -/
def SparseRelationSupport.coefficients
    {X : Type*} [Fintype X] {q : X → QuadraticQuotient}
    (r : SparseRelationSupport q) : X → F₂ :=
  relationIndicator r.support

theorem SparseRelationSupport.coefficients_mem_relationKernel
    {X : Type*} [Fintype X] {q : X → QuadraticQuotient}
    (r : SparseRelationSupport q) :
    r.coefficients ∈ relationKernel q := by
  change coefficientSum q (relationIndicator r.support) = 0
  rw [coefficientSum_relationIndicator]
  exact r.sum_eq_zero

/-- Every relation vector has a canonical sparse-support presentation. -/
noncomputable def sparseRelationSupportOfKernel
    {X : Type*} [Fintype X] {q : X → QuadraticQuotient}
    (a : relationKernel q) : SparseRelationSupport q where
  support := relationSupport a.1
  sum_eq_zero := by
    have ha : coefficientSum q a.1 = 0 := (LinearMap.mem_ker).1 a.2
    rw [← relationIndicator_support_eq a.1,
      coefficientSum_relationIndicator] at ha
    exact ha

@[simp] theorem sparseRelationSupportOfKernel_coefficients
    {X : Type*} [Fintype X] {q : X → QuadraticQuotient}
    (a : relationKernel q) :
    (sparseRelationSupportOfKernel a).coefficients = a.1 := by
  exact relationIndicator_support_eq a.1

/-- For an injective family of nonzero vectors, a nonempty relation support
has at least three points. -/
theorem sparseRelationSupport_card_eq_zero_or_three_le
    {X : Type*} [Fintype X] {q : X → QuadraticQuotient}
    (hinj : Function.Injective q) (hne : ∀ x, q x ≠ 0)
    (r : SparseRelationSupport q) :
    r.support.card = 0 ∨ 3 ≤ r.support.card := by
  classical
  have hneOne : r.support.card ≠ 1 := by
    intro hcard
    rcases Finset.card_eq_one.mp hcard with ⟨x, hx⟩
    have hsum := r.sum_eq_zero
    rw [hx] at hsum
    apply hne x
    simpa only [Finset.sum_singleton] using hsum
  have hneTwo : r.support.card ≠ 2 := by
    intro hcard
    rcases Finset.card_eq_two.mp hcard with ⟨x, y, hxy, hs⟩
    have hsum : q x + q y = 0 := by
      have hsum0 := r.sum_eq_zero
      rw [hs] at hsum0
      simpa [hxy] using hsum0
    have hqxy : q x = q y := by
      have hone : (1 + 1 : F₂) = 0 := by
        change (2 : F₂) = 0
        exact N3Certificate.two_eq_zero_f2
      have hself : q y + q y = 0 := by
        calc
          q y + q y = (1 + 1 : F₂) • q y := by simp [add_smul]
          _ = 0 := by rw [hone, zero_smul]
      calc
        q x = q x + (q y + q y) := by rw [hself, add_zero]
        _ = (q x + q y) + q y := add_assoc _ _ _ |>.symm
        _ = q y := by rw [hsum, zero_add]
    exact hxy (hinj hqxy)
  omega

/-- Specialization of the preceding support bound to populated nonzero
points of a defect subspace. -/
theorem populatedSparseRelation_card_eq_zero_or_three_le
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) :
    r.support.card = 0 ∨ 3 ≤ r.support.card := by
  apply sparseRelationSupport_card_eq_zero_or_three_le
    (populatedQuotientPoint_injective Q)
  intro x
  exact x.2.1

/-! ## Dimension-three relation bound -/

/-- A finite injective family of nonzero vectors, together with zero, embeds
in its linear span. -/
theorem card_add_one_le_pow_finrank_span
    {X V : Type*} [Fintype X] [Fintype V]
    [AddCommGroup V] [Module F₂ V]
    (v : X → V) (hinj : Function.Injective v) (hne : ∀ x, v x ≠ 0) :
    Fintype.card X + 1 ≤
      2 ^ Module.finrank F₂ (Submodule.span F₂ (Set.range v)) := by
  let S : Submodule F₂ V := Submodule.span F₂ (Set.range v)
  let inc : Option X → S := fun o =>
    match o with
    | none => 0
    | some x => ⟨v x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hinc : Function.Injective inc := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            exfalso
            apply hne y
            exact congrArg Subtype.val hxy |>.symm
    | some x =>
        cases y with
        | none =>
            exfalso
            apply hne x
            exact congrArg Subtype.val hxy
        | some y =>
            congr 1
            apply hinj
            exact congrArg Subtype.val hxy
  letI : Fintype S := Fintype.ofFinite S
  have hcard := Fintype.card_le_of_injective inc hinc
  rw [Fintype.card_option,
    Module.card_eq_pow_finrank (K := F₂) (V := S)] at hcard
  simpa [S] using hcard

/-- For a defect space of dimension at most three, the additive relation
kernel of its populated nonzero points has dimension at most four. -/
theorem populatedRelationKernel_finrank_le_four
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    Module.finrank F₂
      ↑(relationKernel (populatedQuotientPoint (Q := Q))) ≤ 4 := by
  let q := populatedQuotientPoint (Q := Q)
  let S : Submodule F₂ QuadraticQuotient :=
    Submodule.span F₂ (Set.range q)
  have hSle : S ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact x.1.2
  have hSrank : Module.finrank F₂ S ≤ 3 :=
    (Submodule.finrank_mono hSle).trans hQ
  have hcard : Fintype.card (PopulatedPoint Q) + 1 ≤
      2 ^ Module.finrank F₂ S := by
    exact card_add_one_le_pow_finrank_span q
      (populatedQuotientPoint_injective Q) (fun x => x.2.1)
  have hkernel := relationKernel_finrank_add_span q
  change Module.finrank F₂ ↑(relationKernel q) +
      Module.finrank F₂ S = Fintype.card (PopulatedPoint Q) at hkernel
  change Module.finrank F₂ ↑(relationKernel q) ≤ 4
  interval_cases hS : Module.finrank F₂ S <;>
    norm_num [hS] at hcard hkernel ⊢ <;> omega

/-- Profile-free half of the displacement estimate: before using any local
place pivots, a three-dimensional defect has at most four relation gifts. -/
theorem relationGiftRank_le_four
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    relationGiftRank Q ≤ 4 :=
  (relationGiftRank_le_relationKernel Q).trans
    (populatedRelationKernel_finrank_le_four Q hQ)

/-- Any relation with at least five populated points in a defect of dimension
at most three contains a line or quadrilateral subrelation.  This is the
algebraic circuit-reduction step behind the Fano presentation; it chooses
four support points and uses dimension, not an enumeration of planes. -/
theorem exists_small_sparseRelation_subset
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q)))
    (hrcard : 5 ≤ r.support.card) :
    ∃ C : Finset (PopulatedPoint Q),
      C ⊆ r.support ∧
      (C.card = 3 ∨ C.card = 4) ∧
      ∑ x ∈ C, populatedQuotientPoint x = 0 := by
  classical
  rcases r.support.exists_subset_card_eq (by omega : 4 ≤ r.support.card) with
    ⟨S, hSr, hScard⟩
  let v : PopulatedPoint Q → Q := fun x => x.1
  have hv : Function.Injective v := Subtype.val_injective
  let T : Finset Q := S.image v
  have hTcard : T.card = 4 := by
    change (S.image v).card = 4
    rw [Finset.card_image_of_injective _ hv, hScard]
  have hTdep : Module.finrank F₂ Q < T.card := by omega
  rcases Module.exists_nontrivial_relation_of_finrank_lt_card hTdep with
    ⟨f, hfsum, e, heT, hfe⟩
  have hfsumS : ∑ x ∈ S, f (v x) • v x = 0 := by
    simpa [T, Finset.sum_image, v] using hfsum
  let C : Finset (PopulatedPoint Q) :=
    S.filter (fun x => f (v x) ≠ 0)
  have hCsubS : C ⊆ S := Finset.filter_subset _ _
  have hCsubr : C ⊆ r.support := hCsubS.trans hSr
  have hCsumQ : ∑ x ∈ C, v x = 0 := by
    calc
      ∑ x ∈ C, v x = ∑ x ∈ S, f (v x) • v x := by
        change ∑ x ∈ S.filter (fun x => f (v x) ≠ 0), v x = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hfx : f (v x) = 0
        · simp [hfx]
        · have hfx1 : f (v x) = 1 := by
            rcases f2_eq_zero_or_one (f (v x)) with hzero | hone
            · exact (hfx hzero).elim
            · exact hone
          simp [hfx1]
      _ = 0 := hfsumS
  have hCsum : ∑ x ∈ C, populatedQuotientPoint x = 0 := by
    change ∑ x ∈ C, Q.subtype (v x) = 0
    simpa only [map_sum, map_zero] using congrArg Q.subtype hCsumQ
  have hCnonempty : C.Nonempty := by
    change e ∈ S.image v at heT
    rw [Finset.mem_image] at heT
    rcases heT with ⟨x, hxS, rfl⟩
    exact ⟨x, by simp [C, hxS, hfe]⟩
  let rC : SparseRelationSupport
      (populatedQuotientPoint (Q := Q)) := ⟨C, hCsum⟩
  have hCthree : 3 ≤ C.card := by
    rcases populatedSparseRelation_card_eq_zero_or_three_le Q rC with
      hzero | hthree
    · exact (hCnonempty.ne_empty (Finset.card_eq_zero.mp hzero)).elim
    · exact hthree
  have hCfour : C.card ≤ 4 := by
    rw [← hScard]
    exact Finset.card_le_card hCsubS
  exact ⟨C, hCsubr, by omega, hCsum⟩

/-- Adding the indicator of a subset of a support removes exactly that
subset. -/
theorem relationSupport_add_indicator_of_subset
    {X : Type*} [Fintype X] [DecidableEq X]
    (a : X → F₂) (C : Finset X)
    (hC : C ⊆ relationSupport a) :
    relationSupport (a + relationIndicator C) = relationSupport a \ C := by
  classical
  ext x
  by_cases hxC : x ∈ C
  · have hax : a x ≠ 0 := (mem_relationSupport a x).1 (hC hxC)
    have hax1 : a x = 1 := by
      rcases f2_eq_zero_or_one (a x) with hzero | hone
      · exact (hax hzero).elim
      · exact hone
    have hone : (1 + 1 : F₂) = 0 := by
      change (2 : F₂) = 0
      exact N3Certificate.two_eq_zero_f2
    simp [mem_relationSupport, relationIndicator, hxC, hax1, hone]
  · simp [mem_relationSupport, relationIndicator, hxC]

/-- Coefficient vectors of Fano line and quadrilateral relations. -/
def smallSparseRelationVectors
    (Q : Submodule F₂ QuadraticQuotient) :
    Set (PopulatedPoint Q → F₂) :=
  {a | ∃ r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q)),
    (r.support.card = 3 ∨ r.support.card = 4) ∧
      a = r.coefficients}

/-- Span of all populated Fano line and quadrilateral relations. -/
def fanoRelationSpan (Q : Submodule F₂ QuadraticQuotient) :
    Submodule F₂ (PopulatedPoint Q → F₂) :=
  Submodule.span F₂ (smallSparseRelationVectors Q)

theorem fanoRelationSpan_le_relationKernel
    (Q : Submodule F₂ QuadraticQuotient) :
    fanoRelationSpan Q ≤
      relationKernel (populatedQuotientPoint (Q := Q)) := by
  apply Submodule.span_le.mpr
  rintro a ⟨r, _hrcard, rfl⟩
  exact r.coefficients_mem_relationKernel

/-- Manuscript Fano presentation: when `finrank Q ≤ 3`, every additive
relation among populated nonzero points is a sum of relations supported on
Fano lines and Fano quadrilaterals. -/
theorem relationKernel_eq_fanoRelationSpan
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    relationKernel (populatedQuotientPoint (Q := Q)) =
      fanoRelationSpan Q := by
  classical
  apply le_antisymm
  · intro a ha
    let aK : relationKernel (populatedQuotientPoint (Q := Q)) := ⟨a, ha⟩
    have hind : ∀ n : Nat,
        ∀ b : relationKernel (populatedQuotientPoint (Q := Q)),
        (relationSupport b.1).card = n → b.1 ∈ fanoRelationSpan Q := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro b hbn
          let r := sparseRelationSupportOfKernel b
          have hrsupport : r.support = relationSupport b.1 := rfl
          rcases populatedSparseRelation_card_eq_zero_or_three_le Q r with
            hrzero | hrthree
          · have hbzero : b.1 = 0 := by
              rw [← relationIndicator_support_eq b.1,
                ← hrsupport, Finset.card_eq_zero.mp hrzero]
              funext x
              simp [relationIndicator]
            rw [hbzero]
            exact Submodule.zero_mem _
          · by_cases hrthreeEq : r.support.card = 3
            · apply Submodule.subset_span
              exact ⟨r, Or.inl hrthreeEq,
                (sparseRelationSupportOfKernel_coefficients b).symm⟩
            by_cases hrfourEq : r.support.card = 4
            · apply Submodule.subset_span
              exact ⟨r, Or.inr hrfourEq,
                (sparseRelationSupportOfKernel_coefficients b).symm⟩
            have hrfive : 5 ≤ r.support.card := by omega
            rcases exists_small_sparseRelation_subset Q hQ r hrfive with
              ⟨C, hCr, hCcard, hCsum⟩
            let rC : SparseRelationSupport
                (populatedQuotientPoint (Q := Q)) := ⟨C, hCsum⟩
            let cK : relationKernel
                (populatedQuotientPoint (Q := Q)) :=
              ⟨rC.coefficients, rC.coefficients_mem_relationKernel⟩
            let b' : relationKernel
                (populatedQuotientPoint (Q := Q)) := b + cK
            have hsupport' : relationSupport b'.1 = r.support \ C := by
              change relationSupport (b.1 + relationIndicator C) = _
              calc
                relationSupport (b.1 + relationIndicator C) =
                    relationSupport b.1 \ C :=
                  relationSupport_add_indicator_of_subset b.1 C (by
                    rw [← hrsupport]
                    exact hCr)
                _ = r.support \ C := by rw [hrsupport]
            have hClt : (relationSupport b'.1).card < n := by
              rw [hsupport', Finset.card_sdiff,
                Finset.inter_eq_left.mpr hCr, ← hbn, ← hrsupport]
              have hCpos : 0 < C.card := by rcases hCcard with h | h <;> omega
              omega
            have hb'mem : b'.1 ∈ fanoRelationSpan Q :=
              ih _ hClt b' rfl
            have hcKmem : cK.1 ∈ fanoRelationSpan Q := by
              apply Submodule.subset_span
              exact ⟨rC, hCcard, rfl⟩
            have hbEq : b.1 = b'.1 + cK.1 := by
              change b.1 = (b.1 + cK.1) + cK.1
              funext x
              calc
                b.1 x = b.1 x + 0 := (add_zero _).symm
                _ = b.1 x + (cK.1 x + cK.1 x) := by
                  rw [CharTwo.add_self_eq_zero]
                _ = (b.1 x + cK.1 x) + cK.1 x :=
                  (add_assoc _ _ _).symm
            rw [hbEq]
            exact Submodule.add_mem _ hb'mem hcKmem
    exact hind (relationSupport aK.1).card aK rfl
  · exact fanoRelationSpan_le_relationKernel Q

/-! ## Relation-map reduction to sparse gifts -/

/-- The chosen-lift sum map on all coefficient vectors.  Its restriction to
the relation kernel is `defectRelationMap`. -/
def populatedLiftQuotientMap
    (Q : Submodule F₂ QuadraticQuotient) :
    (PopulatedPoint Q → F₂) →ₗ[F₂]
      (TwoForm ⧸ localDisplacementSpace Q) :=
  (Submodule.mkQ (localDisplacementSpace Q)).comp
    (coefficientSum (populatedLift (Q := Q)))

theorem populatedLiftQuotientMap_sparse_apply
    (Q : Submodule F₂ QuadraticQuotient)
    (r : SparseRelationSupport
      (populatedQuotientPoint (Q := Q))) :
    populatedLiftQuotientMap Q r.coefficients =
      (Submodule.mkQ (localDisplacementSpace Q))
        (∑ x ∈ r.support, populatedLift x) := by
  change (Submodule.mkQ (localDisplacementSpace Q))
    (coefficientSum populatedLift (relationIndicator r.support)) = _
  rw [coefficientSum_relationIndicator]

theorem defectRelationMap_eq_populatedLiftQuotientMap_domRestrict
    (Q : Submodule F₂ QuadraticQuotient) :
    defectRelationMap Q =
      (populatedLiftQuotientMap Q).domRestrict
        (relationKernel (populatedQuotientPoint (Q := Q))) := rfl

/-- Sparse line and quadrilateral gift vectors, after quotienting by all
intrinsic local displacements. -/
def smallRelationGiftVectors
    (Q : Submodule F₂ QuadraticQuotient) :
    Set (TwoForm ⧸ localDisplacementSpace Q) :=
  populatedLiftQuotientMap Q '' smallSparseRelationVectors Q

/-- For a defect of dimension at most three, the entire relation-gift image
is spanned by its Fano line and quadrilateral gifts. -/
theorem defectRelationMap_range_eq_span_smallRelationGifts
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    LinearMap.range (defectRelationMap Q) =
      Submodule.span F₂ (smallRelationGiftVectors Q) := by
  rw [defectRelationMap_eq_populatedLiftQuotientMap_domRestrict,
    LinearMap.range_domRestrict,
    relationKernel_eq_fanoRelationSpan Q hQ,
    fanoRelationSpan, Submodule.map_span]
  rfl

/-- A Fano line relation is a sparse relation on three points. -/
structure FanoLineRelation {X : Type*} [Fintype X]
    (q : X → QuadraticQuotient) extends SparseRelationSupport q where
  card_support : toSparseRelationSupport.support.card = 3

/-- A Fano quadrilateral relation is a sparse relation on four points. -/
structure FanoQuadrilateralRelation {X : Type*} [Fintype X]
    (q : X → QuadraticQuotient) extends SparseRelationSupport q where
  card_support : toSparseRelationSupport.support.card = 4

theorem relationMap_sparseRelation_apply
    {X : Type*} [Fintype X] (D : Submodule F₂ TwoForm)
    (lift : X → TwoForm) (q : X → QuadraticQuotient)
    (r : SparseRelationSupport q) :
    relationMap D lift q
        ⟨r.coefficients, r.coefficients_mem_relationKernel⟩ =
      (Submodule.mkQ D) (∑ x ∈ r.support, lift x) := by
  change (Submodule.mkQ D)
    (coefficientSum lift (relationIndicator r.support)) = _
  rw [coefficientSum_relationIndicator]

/-- Three distinct points with `q x + q y + q z = 0` give a Fano line
relation. -/
noncomputable def fanoLineRelationOf
    {X : Type*} [Fintype X] (q : X → QuadraticQuotient)
    (x y z : X) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsum : q x + q y + q z = 0) : FanoLineRelation q := by
  classical
  refine
    { support := {x, y, z}
      sum_eq_zero := ?_
      card_support := ?_ }
  · simpa [hxy, hxz, hyz, add_assoc] using hsum
  · simp [hxy, hxz, hyz]

/-- Four pairwise distinct points with zero sum give a Fano quadrilateral
relation. -/
noncomputable def fanoQuadrilateralRelationOf
    {X : Type*} [Fintype X] (q : X → QuadraticQuotient)
    (w x y z : X)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsum : q w + q x + q y + q z = 0) :
    FanoQuadrilateralRelation q := by
  classical
  refine
    { support := {w, x, y, z}
      sum_eq_zero := ?_
      card_support := ?_ }
  · simpa [hwx, hwy, hwz, hxy, hxz, hyz, add_assoc] using hsum
  · simp [hwx, hwy, hwz, hxy, hxz, hyz]

/-! ## Closed-place incidence -/

/-- An effective atlas point, viewed as a populated nonzero point of `Q`. -/
def closedPlacePopulatedPoint
    (Q : Submodule F₂ QuadraticQuotient)
    (x : ClosedPlaceEffectiveParam)
    (hx : closedPlaceEffectivePoint x ∈ Q) : PopulatedPoint Q :=
  ⟨⟨closedPlaceEffectivePoint x, hx⟩,
    closedPlaceQuotientPoint_ne_zero x.1
      (effectiveParamsAt_ne_zero x.1 x.2.2),
    closedPlaceEffectivePoint_populated x⟩

@[simp] theorem populatedQuotientPoint_closedPlacePopulatedPoint
    (Q : Submodule F₂ QuadraticQuotient)
    (x : ClosedPlaceEffectiveParam)
    (hx : closedPlaceEffectivePoint x ∈ Q) :
    populatedQuotientPoint (closedPlacePopulatedPoint Q x hx) =
      closedPlaceEffectivePoint x := rfl

/-- Strong mixed-place exclusion in the incidence form used for sparse
relations: the sum of two distinct effective place types is not populated. -/
theorem not_populated_sum_of_distinct_effective_places
    (x y : ClosedPlaceEffectiveParam) (hxy : x.1 ≠ y.1) :
    ¬ IsPopulatedFiber
      (closedPlaceEffectivePoint x + closedPlaceEffectivePoint y) := by
  rw [IsPopulatedFiber, strongMixedPlace x y hxy]
  simp

/-- Consequently no populated point of a defect subspace can be the mixed
sum of two represented effective points of distinct place types. -/
theorem no_populatedPoint_eq_sum_of_distinct_effective_places
    (Q : Submodule F₂ QuadraticQuotient)
    (x y : ClosedPlaceEffectiveParam) (hxy : x.1 ≠ y.1)
    (z : PopulatedPoint Q) :
    populatedQuotientPoint z ≠
      closedPlaceEffectivePoint x + closedPlaceEffectivePoint y := by
  intro hz
  apply not_populated_sum_of_distinct_effective_places x y hxy
  rw [← hz]
  exact z.2.2

end

end N5
end UnrestrictedBooleanMul
