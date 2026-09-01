import UnrestrictedBooleanMul.N5.FanoLineIncidencePivots

/-!
# Pointed Fano relations

This module develops the remaining incidence input without enumerating a
Fano plane.  Translation by a fixed nonzero populated point pairs the other
points.  A populated translate is exactly the third point of a Fano line;
an unpopulated translate is a genuinely missing vector.  Since a defect of
rank at most three has at most eight vectors, a cardinal injection forces
enough line pairs.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

noncomputable local instance quadraticSubspaceFintype
    (Q : Submodule F₂ QuadraticQuotient) : Fintype Q :=
  Fintype.ofFinite Q

noncomputable local instance populatedPointDecidableEq
    (Q : Submodule F₂ QuadraticQuotient) : DecidableEq (PopulatedPoint Q) :=
  Classical.decEq _

private theorem add_eq_zero_iff_eq_f2
    {V : Type*} [AddCommGroup V] [Module F₂ V] (a b : V) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have hb : b + b = 0 := by
      calc
        b + b = (1 + 1 : F₂) • b := by simp [add_smul]
        _ = 0 := by
          rw [show (1 + 1 : F₂) = 0 by
            exact N3Certificate.two_eq_zero_f2, zero_smul]
    calc
      a = a + 0 := (add_zero _).symm
      _ = a + (b + b) := by rw [hb]
      _ = (a + b) + b := (add_assoc _ _ _).symm
      _ = b := by rw [h, zero_add]
  · intro h
    rw [h]
    calc
      b + b = (1 + 1 : F₂) • b := by simp [add_smul]
      _ = 0 := by
        rw [show (1 + 1 : F₂) = 0 by
          exact N3Certificate.two_eq_zero_f2, zero_smul]

private theorem add_self_eq_zero_f2
    {V : Type*} [AddCommGroup V] [Module F₂ V] (a : V) :
    a + a = 0 :=
  (add_eq_zero_iff_eq_f2 a a).2 rfl

/-- Coefficient relations supported on populated Fano lines through `x`. -/
def fanoLineRelationCoeffSpaceThrough
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q) :
    Submodule F₂ (PopulatedPoint Q → F₂) :=
  Submodule.span F₂ {a | ∃ r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)),
    x ∈ r.support ∧ a = r.coefficients}

/-- Every pointed line relation is an additive relation. -/
theorem fanoLineRelationCoeffSpaceThrough_le_relationKernel
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q) :
    fanoLineRelationCoeffSpaceThrough Q x ≤
      relationKernel (populatedQuotientPoint (Q := Q)) := by
  apply Submodule.span_le.mpr
  rintro a ⟨r, _hx, rfl⟩
  exact r.coefficients_mem_relationKernel

/-- A rank-three defect subspace contains at most eight vectors. -/
theorem defectSubspace_card_le_eight
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) :
    Fintype.card Q ≤ 8 := by
  rw [Module.card_eq_pow_finrank (K := F₂) (V := Q)]
  interval_cases h : Module.finrank F₂ Q <;> norm_num [h]

/-- If the populated points outside `E`, their translates by `x`, all
populated points, and zero would give at least nine vectors, then some point
outside `E` has a populated translate.  The proof is a direct injection into
`Q`; it does not inspect coordinates of the defect space. -/
theorem exists_populated_translate_outside
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q) (E : Finset (PopulatedPoint Q))
    (hxE : x ∈ E)
    (hcard : 9 ≤ Fintype.card (PopulatedPoint Q) + 1 +
      (Fintype.card (PopulatedPoint Q) - E.card)) :
    ∃ y z : PopulatedPoint Q,
      y ∉ E ∧ populatedQuotientPoint z =
        populatedQuotientPoint x + populatedQuotientPoint y := by
  classical
  by_contra hnone
  push Not at hnone
  let R := {y : PopulatedPoint Q // y ∉ E}
  let inc : Option (PopulatedPoint Q ⊕ R) → Q
    | none => 0
    | some (Sum.inl y) => y.1
    | some (Sum.inr y) => x.1 + y.1.1
  have hinc : Function.Injective inc := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            cases b with
            | inl y =>
                exfalso
                apply y.2.1
                exact congrArg Subtype.val hab |>.symm
            | inr y =>
                exfalso
                change (0 : Q) = x.1 + y.1.1 at hab
                have hxy : x.1 = y.1.1 :=
                  (add_eq_zero_iff_eq_f2 x.1 y.1.1).1
                    hab.symm
                have hxyPoint : x = y.1 := by
                  apply Subtype.ext
                  exact hxy
                exact y.2 (hxyPoint ▸ hxE)
    | some a =>
        cases a with
        | inl a =>
            cases b with
            | none =>
                exfalso
                apply a.2.1
                exact congrArg Subtype.val hab
            | some b =>
                cases b with
                | inl b =>
                    congr 2
                    apply Subtype.ext
                    exact hab
                | inr b =>
                    exfalso
                    change a.1 = x.1 + b.1.1 at hab
                    exact hnone b.1 a b.2
                      (congrArg Subtype.val hab)
        | inr a =>
            cases b with
            | none =>
                exfalso
                change x.1 + a.1.1 = (0 : Q) at hab
                have hxy : x.1 = a.1.1 :=
                  (add_eq_zero_iff_eq_f2 x.1 a.1.1).1
                    hab
                have hxyPoint : x = a.1 := by
                  apply Subtype.ext
                  exact hxy
                exact a.2 (hxyPoint ▸ hxE)
            | some b =>
                cases b with
                | inl b =>
                    exfalso
                    change x.1 + a.1.1 = b.1 at hab
                    exact hnone a.1 b a.2
                      (congrArg Subtype.val hab).symm
                | inr b =>
                    congr 3
                    apply Subtype.ext
                    apply Subtype.ext
                    change x.1 + a.1.1 = x.1 + b.1.1 at hab
                    exact add_left_cancel hab
  have hle := Fintype.card_le_of_injective inc hinc
  have hRcard : Fintype.card R =
      Fintype.card (PopulatedPoint Q) - E.card := by
    change Fintype.card {y : PopulatedPoint Q // y ∉ E} = _
    rw [Fintype.card_subtype_compl]
    congr 1
    exact Fintype.card_coe E
  have hsource : 9 ≤ Fintype.card (Option (PopulatedPoint Q ⊕ R)) := by
    rw [Fintype.card_option, Fintype.card_sum, hRcard]
    omega
  have hQcard := defectSubspace_card_le_eight Q hQ
  omega

/-- A finite set is closed under the partner involution based at `x`. -/
def IsPartnerClosedAt
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q)
    (E : Finset (PopulatedPoint Q)) : Prop :=
  ∀ y : PopulatedPoint Q, y ∈ E →
    ∀ z : PopulatedPoint Q,
      populatedQuotientPoint z =
        populatedQuotientPoint x + populatedQuotientPoint y →
      z ∈ E

theorem isPartnerClosedAt_singleton
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q) :
    IsPartnerClosedAt Q x {x} := by
  intro y hy z hz
  have hyx : y = x := by simpa using hy
  subst y
  exfalso
  apply z.2.1
  change populatedQuotientPoint z = 0
  exact hz.trans (add_self_eq_zero_f2 _)

/-- The support of a Fano line through `x` is partner-closed at `x`. -/
theorem fanoLine_support_isPartnerClosedAt
    (Q : Submodule F₂ QuadraticQuotient)
    (x : PopulatedPoint Q)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (hx : x ∈ r.support) :
    IsPartnerClosedAt Q x r.support := by
  intro y hy z hz
  by_cases hyx : y = x
  · subst y
    exfalso
    apply z.2.1
    change populatedQuotientPoint z = 0
    exact hz.trans (add_self_eq_zero_f2 _)
  · rcases fanoLine_exists_third Q r x y hx hy (Ne.symm hyx) with
      ⟨w, hw, _hwx, _hwy, hwPoint⟩
    have hzw : z = w := populatedQuotientPoint_injective Q
      (hz.trans hwPoint.symm)
    simpa [hzw] using hw

theorem IsPartnerClosedAt.union
    {Q : Submodule F₂ QuadraticQuotient} {x : PopulatedPoint Q}
    {E F : Finset (PopulatedPoint Q)}
    (hE : IsPartnerClosedAt Q x E)
    (hF : IsPartnerClosedAt Q x F) :
    IsPartnerClosedAt Q x (E ∪ F) := by
  intro y hy z hz
  rcases Finset.mem_union.mp hy with hyE | hyF
  · exact Finset.mem_union_left _ (hE y hyE z hz)
  · exact Finset.mem_union_right _ (hF y hyF z hz)

/-- The cardinal injection produces a new Fano line meeting a partner-closed
excluded set only at the base point. -/
theorem exists_fanoLineRelation_inter_eq_singleton
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q) (E : Finset (PopulatedPoint Q))
    (hxE : x ∈ E) (hclosed : IsPartnerClosedAt Q x E)
    (hcard : 9 ≤ Fintype.card (PopulatedPoint Q) + 1 +
      (Fintype.card (PopulatedPoint Q) - E.card)) :
    ∃ (r : FanoLineRelation
        (populatedQuotientPoint (Q := Q))) (y : PopulatedPoint Q),
      x ∈ r.support ∧ y ∈ r.support ∧ y ∉ E ∧
        r.support ∩ E = {x} := by
  classical
  rcases exists_populated_translate_outside Q hQ x E hxE hcard with
    ⟨y, z, hyE, hz⟩
  have hyx : y ≠ x := fun hyx ↦ hyE (hyx ▸ hxE)
  have hzx : z ≠ x := by
    intro hzx
    subst z
    apply y.2.1
    have hzero : (0 : QuadraticQuotient) =
        populatedQuotientPoint y := by
      apply add_left_cancel (a := populatedQuotientPoint x)
      simpa using hz
    exact hzero.symm
  have hzy : z ≠ y := by
    intro hzy
    subst z
    apply x.2.1
    have hzero : (0 : QuadraticQuotient) =
        populatedQuotientPoint x := by
      apply add_left_cancel (a := populatedQuotientPoint y)
      simpa [add_comm] using hz
    exact hzero.symm
  have hyPartner : populatedQuotientPoint y =
      populatedQuotientPoint x + populatedQuotientPoint z := by
    apply (add_eq_zero_iff_eq_f2
      (populatedQuotientPoint y)
      (populatedQuotientPoint x + populatedQuotientPoint z)).1
    calc
      populatedQuotientPoint y +
          (populatedQuotientPoint x + populatedQuotientPoint z) =
          (populatedQuotientPoint x + populatedQuotientPoint x) +
            (populatedQuotientPoint y + populatedQuotientPoint y) := by
              rw [hz]
              ac_rfl
      _ = 0 := by rw [add_self_eq_zero_f2, add_self_eq_zero_f2, add_zero]
  have hzE : z ∉ E := by
    intro hzMem
    exact hyE (hclosed z hzMem y hyPartner)
  have hsum : populatedQuotientPoint x + populatedQuotientPoint y +
      populatedQuotientPoint z = 0 := by
    rw [hz]
    exact add_self_eq_zero_f2
      (populatedQuotientPoint x + populatedQuotientPoint y)
  let r := fanoLineRelationOf
    (populatedQuotientPoint (Q := Q)) x y z
      hyx.symm hzx.symm hzy.symm hsum
  have hrSupport : r.support = {x, y, z} := by
    change ({x, y, z} : Finset (PopulatedPoint Q)) = {x, y, z}
    rfl
  refine ⟨r, y, ?_, ?_, hyE, ?_⟩
  · rw [hrSupport]
    simp
  · rw [hrSupport]
    simp
  · rw [hrSupport]
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hw, hwE⟩
      rcases hw with rfl | rfl | rfl
      · rfl
      · exact (hyE hwE).elim
      · exact (hzE hwE).elim
    · rintro rfl
      exact ⟨Or.inl rfl, hxE⟩

/-- Five populated points force a Fano line through any selected point. -/
theorem exists_one_fanoLine_through
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q)
    (hcard : 5 ≤ Fintype.card (PopulatedPoint Q)) :
    ∃ (r : FanoLineRelation
        (populatedQuotientPoint (Q := Q))) (y : PopulatedPoint Q),
      x ∈ r.support ∧ y ∈ r.support ∧ y ≠ x := by
  have hlarge : 9 ≤ Fintype.card (PopulatedPoint Q) + 1 +
      (Fintype.card (PopulatedPoint Q) - ({x} : Finset _).card) := by
    simp only [Finset.card_singleton]
    omega
  rcases exists_fanoLineRelation_inter_eq_singleton Q hQ x {x}
      (by simp) (isPartnerClosedAt_singleton Q x) hlarge with
    ⟨r, y, hx, hy, hyOutside, _hinter⟩
  exact ⟨r, y, hx, hy, by simpa using hyOutside⟩

/-- Six populated points force two pointed Fano lines whose only common
point is the selected base point. -/
theorem exists_two_fanoLines_through
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q)
    (hcard : 6 ≤ Fintype.card (PopulatedPoint Q)) :
    ∃ (r₁ r₂ : FanoLineRelation
        (populatedQuotientPoint (Q := Q)))
        (y₁ y₂ : PopulatedPoint Q),
      x ∈ r₁.support ∧ x ∈ r₂.support ∧
      y₁ ∈ r₁.support ∧ y₁ ≠ x ∧
      y₂ ∈ r₂.support ∧ y₂ ∉ r₁.support ∧
      r₂.support ∩ r₁.support = {x} := by
  rcases exists_one_fanoLine_through Q hQ x (by omega) with
    ⟨r₁, y₁, hx₁, hy₁, hy₁x⟩
  have hlarge : 9 ≤ Fintype.card (PopulatedPoint Q) + 1 +
      (Fintype.card (PopulatedPoint Q) - r₁.support.card) := by
    rw [r₁.card_support]
    omega
  rcases exists_fanoLineRelation_inter_eq_singleton Q hQ x r₁.support
      hx₁ (fanoLine_support_isPartnerClosedAt Q x r₁ hx₁) hlarge with
    ⟨r₂, y₂, hx₂, hy₂, hy₂Outside, hinter⟩
  exact ⟨r₁, r₂, y₁, y₂, hx₁, hx₂,
    hy₁, hy₁x, hy₂, hy₂Outside, hinter⟩

/-- Seven populated points force three pointed Fano lines, pairwise meeting
only at the selected base point. -/
theorem exists_three_fanoLines_through
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q)
    (hcard : 7 ≤ Fintype.card (PopulatedPoint Q)) :
    ∃ (r₁ r₂ r₃ : FanoLineRelation
        (populatedQuotientPoint (Q := Q)))
        (y₁ y₂ y₃ : PopulatedPoint Q),
      x ∈ r₁.support ∧ x ∈ r₂.support ∧ x ∈ r₃.support ∧
      y₁ ∈ r₁.support ∧ y₁ ≠ x ∧
      y₂ ∈ r₂.support ∧ y₂ ∉ r₁.support ∧
      y₃ ∈ r₃.support ∧
        y₃ ∉ r₁.support ∪ r₂.support ∧
      r₂.support ∩ r₁.support = {x} ∧
      r₃.support ∩ (r₁.support ∪ r₂.support) = {x} := by
  rcases exists_two_fanoLines_through Q hQ x (by omega) with
    ⟨r₁, r₂, y₁, y₂, hx₁, hx₂, hy₁, hy₁x,
      hy₂, hy₂Outside, hinter₂₁⟩
  let E := r₁.support ∪ r₂.support
  have hxE : x ∈ E := Finset.mem_union_left _ hx₁
  have hclosedE : IsPartnerClosedAt Q x E :=
    (fanoLine_support_isPartnerClosedAt Q x r₁ hx₁).union
      (fanoLine_support_isPartnerClosedAt Q x r₂ hx₂)
  have hinterCard : (r₁.support ∩ r₂.support).card = 1 := by
    rw [Finset.inter_comm, hinter₂₁]
    simp
  have hEcard : E.card = 5 := by
    change (r₁.support ∪ r₂.support).card = 5
    have h := Finset.card_union_add_card_inter r₁.support r₂.support
    rw [r₁.card_support, r₂.card_support, hinterCard] at h
    omega
  have hlarge : 9 ≤ Fintype.card (PopulatedPoint Q) + 1 +
      (Fintype.card (PopulatedPoint Q) - E.card) := by
    rw [hEcard]
    omega
  rcases exists_fanoLineRelation_inter_eq_singleton Q hQ x E hxE
      hclosedE hlarge with
    ⟨r₃, y₃, hx₃, hy₃, hy₃Outside, hinter₃⟩
  exact ⟨r₁, r₂, r₃, y₁, y₂, y₃,
    hx₁, hx₂, hx₃, hy₁, hy₁x, hy₂, hy₂Outside,
    hy₃, hy₃Outside, hinter₂₁, hinter₃⟩

/-- Line indicators with private support points are linearly independent.
This is the only independence argument needed for the pointed-star rank. -/
theorem fanoLine_coefficients_linearIndependent_of_private_points
    {Q : Submodule F₂ QuadraticQuotient}
    {I : Type*} [Fintype I]
    (r : I → FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (y : I → PopulatedPoint Q)
    (hy : ∀ i, y i ∈ (r i).support)
    (hprivate : ∀ i j, i ≠ j → y i ∉ (r j).support) :
    LinearIndependent F₂ (fun i ↦ (r i).coefficients) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hi := congrFun hsum (y i)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hi
  rw [Finset.sum_eq_single i] at hi
  · simpa [SparseRelationSupport.coefficients,
      relationIndicator, hy i] using hi
  · intro j _hj hji
    simp [SparseRelationSupport.coefficients,
      relationIndicator, hprivate i j hji.symm]
  · simp

/-- A private-point family of pointed Fano lines supplies that many
independent vectors inside the pointed relation subspace. -/
theorem card_le_finrank_fanoLineRelationCoeffSpaceThrough
    {Q : Submodule F₂ QuadraticQuotient}
    (x : PopulatedPoint Q) {I : Type*} [Fintype I]
    (r : I → FanoLineRelation
      (populatedQuotientPoint (Q := Q)))
    (y : I → PopulatedPoint Q)
    (hx : ∀ i, x ∈ (r i).support)
    (hy : ∀ i, y i ∈ (r i).support)
    (hprivate : ∀ i j, i ≠ j → y i ∉ (r j).support) :
    Fintype.card I ≤
      Module.finrank F₂ (fanoLineRelationCoeffSpaceThrough Q x) := by
  let v : I → (PopulatedPoint Q → F₂) :=
    fun i ↦ (r i).coefficients
  have hvLI : LinearIndependent F₂ v :=
    fanoLine_coefficients_linearIndependent_of_private_points r y hy hprivate
  have hvSpan : Submodule.span F₂ (Set.range v) ≤
      fanoLineRelationCoeffSpaceThrough Q x := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨r i, hx i, rfl⟩
  rw [← finrank_span_eq_card hvLI]
  exact Submodule.finrank_mono hvSpan

theorem one_le_finrank_fanoLineRelationCoeffSpaceThrough_of_card_ge_five
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) (x : PopulatedPoint Q)
    (hcard : 5 ≤ Fintype.card (PopulatedPoint Q)) :
    1 ≤ Module.finrank F₂ (fanoLineRelationCoeffSpaceThrough Q x) := by
  rcases exists_one_fanoLine_through Q hQ x hcard with
    ⟨r, y, hx, hy, hyx⟩
  let rs : Fin 1 → FanoLineRelation
      (populatedQuotientPoint (Q := Q)) := fun _ ↦ r
  let ys : Fin 1 → PopulatedPoint Q := fun _ ↦ y
  have hbound := card_le_finrank_fanoLineRelationCoeffSpaceThrough
    x rs ys (fun _ ↦ hx) (fun _ ↦ hy) (by
      intro i j hij
      fin_cases i
      fin_cases j
      exact (hij rfl).elim)
  simpa using hbound

theorem two_le_finrank_fanoLineRelationCoeffSpaceThrough_of_card_ge_six
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) (x : PopulatedPoint Q)
    (hcard : 6 ≤ Fintype.card (PopulatedPoint Q)) :
    2 ≤ Module.finrank F₂ (fanoLineRelationCoeffSpaceThrough Q x) := by
  rcases exists_two_fanoLines_through Q hQ x hcard with
    ⟨r₁, r₂, y₁, y₂, hx₁, hx₂, hy₁, hy₁x,
      hy₂, hy₂not₁, hinter⟩
  have hy₁not₂ : y₁ ∉ r₂.support := by
    intro hy₁₂
    have hyInter : y₁ ∈ r₂.support ∩ r₁.support :=
      Finset.mem_inter.mpr ⟨hy₁₂, hy₁⟩
    rw [hinter] at hyInter
    exact hy₁x (by simpa using hyInter)
  let rs : Fin 2 → FanoLineRelation
      (populatedQuotientPoint (Q := Q)) := ![r₁, r₂]
  let ys : Fin 2 → PopulatedPoint Q := ![y₁, y₂]
  have hbound := card_le_finrank_fanoLineRelationCoeffSpaceThrough
    x rs ys (by
      intro i
      fin_cases i <;> assumption) (by
      intro i
      fin_cases i <;> assumption) (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hy₁not₂
      · exact hy₂not₁
      · exact (hij rfl).elim)
  simpa using hbound

private theorem not_mem_left_of_inter_eq_singleton
    {X : Type*} [DecidableEq X] {s t : Finset X} {x y : X}
    (hinter : s ∩ t = {x}) (hyt : y ∈ t) (hyx : y ≠ x) :
    y ∉ s := by
  intro hys
  have hyInter : y ∈ s ∩ t := Finset.mem_inter.mpr ⟨hys, hyt⟩
  rw [hinter] at hyInter
  exact hyx (by simpa using hyInter)

theorem three_le_finrank_fanoLineRelationCoeffSpaceThrough_of_card_ge_seven
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) (x : PopulatedPoint Q)
    (hcard : 7 ≤ Fintype.card (PopulatedPoint Q)) :
    3 ≤ Module.finrank F₂ (fanoLineRelationCoeffSpaceThrough Q x) := by
  rcases exists_three_fanoLines_through Q hQ x hcard with
    ⟨r₁, r₂, r₃, y₁, y₂, y₃, hx₁, hx₂, hx₃,
      hy₁, hy₁x, hy₂, hy₂not₁, hy₃, hy₃notUnion,
      hinter₂₁, hinter₃Union⟩
  have hy₁not₂ : y₁ ∉ r₂.support :=
    not_mem_left_of_inter_eq_singleton hinter₂₁ hy₁ hy₁x
  have hy₁not₃ : y₁ ∉ r₃.support := by
    apply not_mem_left_of_inter_eq_singleton hinter₃Union
      (Finset.mem_union_left _ hy₁) hy₁x
  have hy₂x : y₂ ≠ x := by
    intro hy₂x
    exact hy₂not₁ (hy₂x ▸ hx₁)
  have hy₂not₃ : y₂ ∉ r₃.support := by
    apply not_mem_left_of_inter_eq_singleton hinter₃Union
      (Finset.mem_union_right _ hy₂) hy₂x
  have hy₃not₁ : y₃ ∉ r₁.support := by
    intro hy₃₁
    exact hy₃notUnion (Finset.mem_union_left _ hy₃₁)
  have hy₃not₂ : y₃ ∉ r₂.support := by
    intro hy₃₂
    exact hy₃notUnion (Finset.mem_union_right _ hy₃₂)
  let rs : Fin 3 → FanoLineRelation
      (populatedQuotientPoint (Q := Q)) := ![r₁, r₂, r₃]
  let ys : Fin 3 → PopulatedPoint Q := ![y₁, y₂, y₃]
  have hbound := card_le_finrank_fanoLineRelationCoeffSpaceThrough
    x rs ys (by
      intro i
      fin_cases i <;> assumption) (by
      intro i
      fin_cases i <;> assumption) (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hy₁not₂
      · exact hy₁not₃
      · exact hy₂not₁
      · exact (hij rfl).elim
      · exact hy₂not₃
      · exact hy₃not₁
      · exact hy₃not₂
      · exact (hij rfl).elim)
  simpa using hbound

/-- Once the relation kernel has dimension at least two, the populated family
uses a full three-dimensional span.  This is just rank-nullity together with
the injection of the populated nonzero points and zero into that span. -/
theorem relationKernel_finrank_add_three_le_populatedPoint_card
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hkerTwo : 2 ≤ Module.finrank F₂
      (relationKernel (populatedQuotientPoint (Q := Q)))) :
    Module.finrank F₂
        (relationKernel (populatedQuotientPoint (Q := Q))) + 3 ≤
      Fintype.card (PopulatedPoint Q) := by
  let q := populatedQuotientPoint (Q := Q)
  let S : Submodule F₂ QuadraticQuotient :=
    Submodule.span F₂ (Set.range q)
  have hSle : S ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    exact y.1.2
  have hSrank : Module.finrank F₂ S ≤ 3 :=
    (Submodule.finrank_mono hSle).trans hQ
  have hcard : Fintype.card (PopulatedPoint Q) + 1 ≤
      2 ^ Module.finrank F₂ S :=
    card_add_one_le_pow_finrank_span q
      (populatedQuotientPoint_injective Q) (fun y ↦ y.2.1)
  have hkernel := relationKernel_finrank_add_span q
  change 2 ≤ Module.finrank F₂ (relationKernel q) at hkerTwo
  change Module.finrank F₂ (relationKernel q) +
      Module.finrank F₂ S = Fintype.card (PopulatedPoint Q) at hkernel
  change Module.finrank F₂ (relationKernel q) + 3 ≤
      Fintype.card (PopulatedPoint Q)
  interval_cases hS : Module.finrank F₂ S <;>
    norm_num [hS] at hcard hkernel ⊢ <;> omega

/-- Pointed Fano-line relations have codimension at most one in the full
relation kernel of a rank-three defect. -/
theorem fanoLineRelationCoeffSpaceThrough_codim_le_one
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) (x : PopulatedPoint Q) :
    Module.finrank F₂
        (relationKernel (populatedQuotientPoint (Q := Q))) ≤
      Module.finrank F₂ (fanoLineRelationCoeffSpaceThrough Q x) + 1 := by
  have hKle : Module.finrank F₂
      (relationKernel (populatedQuotientPoint (Q := Q))) ≤ 4 :=
    populatedRelationKernel_finrank_le_four Q hQ
  by_cases hsmall : Module.finrank F₂
      (relationKernel (populatedQuotientPoint (Q := Q))) ≤ 1
  · omega
  have htwo : 2 ≤ Module.finrank F₂
      (relationKernel (populatedQuotientPoint (Q := Q))) := by omega
  have hcard := relationKernel_finrank_add_three_le_populatedPoint_card
    Q hQ htwo
  interval_cases hK : Module.finrank F₂
      (relationKernel (populatedQuotientPoint (Q := Q)))
  · have hline :=
      one_le_finrank_fanoLineRelationCoeffSpaceThrough_of_card_ge_five
        Q hQ x (by omega)
    omega
  · have hline :=
      two_le_finrank_fanoLineRelationCoeffSpaceThrough_of_card_ge_six
        Q hQ x (by omega)
    omega
  · have hline :=
      three_le_finrank_fanoLineRelationCoeffSpaceThrough_of_card_ge_seven
        Q hQ x (by omega)
    omega

/-- The pointed line space, regarded as a subspace of the relation kernel. -/
def fanoLineRelationSubspaceThrough
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q) :
    Submodule F₂
      (relationKernel (populatedQuotientPoint (Q := Q))) :=
  (fanoLineRelationCoeffSpaceThrough Q x).comap
    (relationKernel (populatedQuotientPoint (Q := Q))).subtype

theorem fanoLineRelationSubspaceThrough_finrank
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q) :
    Module.finrank F₂ (fanoLineRelationSubspaceThrough Q x) =
      Module.finrank F₂ (fanoLineRelationCoeffSpaceThrough Q x) := by
  exact (Submodule.comapSubtypeEquivOfLe
    (fanoLineRelationCoeffSpaceThrough_le_relationKernel Q x)).finrank_eq

/-- Restricting a linear map to a codimension-at-most-one subspace loses at
most one dimension of image. -/
theorem finrank_range_le_domRestrict_range_add_one
    {V W : Type*} [AddCommGroup V] [Module F₂ V]
    [AddCommGroup W] [Module F₂ W] [Module.Finite F₂ V]
    (f : V →ₗ[F₂] W) (U : Submodule F₂ V)
    (hcodim : Module.finrank F₂ V ≤ Module.finrank F₂ U + 1) :
    Module.finrank F₂ (LinearMap.range f) ≤
      Module.finrank F₂ (LinearMap.range (f.domRestrict U)) + 1 := by
  let g := f.domRestrict U
  let kerInc : LinearMap.ker g →ₗ[F₂] LinearMap.ker f := {
    toFun a := ⟨a.1.1, by
      apply LinearMap.mem_ker.mpr
      exact LinearMap.mem_ker.mp a.2⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  have hkerInc : Function.Injective kerInc := by
    intro a b hab
    have hv : (a.1.1 : V) = b.1.1 :=
      congrArg (fun z : LinearMap.ker f ↦ (z.1 : V)) hab
    exact Subtype.ext (Subtype.ext hv)
  have hkerRank : Module.finrank F₂ (LinearMap.ker g) ≤
      Module.finrank F₂ (LinearMap.ker f) :=
    kerInc.finrank_le_finrank_of_injective hkerInc
  have hfRank := f.finrank_range_add_finrank_ker
  have hgRank := g.finrank_range_add_finrank_ker
  change Module.finrank F₂ (LinearMap.range f) ≤
    Module.finrank F₂ (LinearMap.range g) + 1
  omega

/-- On a sparse line indicator, anchor summation is exactly the quotient
class of its coefficient gift. -/
theorem populatedAnchorQuotientMap_line_coefficients
    (Q : Submodule F₂ QuadraticQuotient)
    (r : FanoLineRelation
      (populatedQuotientPoint (Q := Q))) :
    populatedAnchorQuotientMap Q r.coefficients =
      (Submodule.mkQ (localDisplacementCoeffSpace Q))
        (sparseRelationGiftCoeff Q r.1) := by
  have hmaps := congrArg
    (fun f : relationKernel (populatedQuotientPoint (Q := Q)) →ₗ[F₂]
        (TargetCoeff ⧸ localDisplacementCoeffSpace Q) ↦
      f ⟨r.coefficients, r.coefficients_mem_relationKernel⟩)
    (defectRelationCoeffMap_eq_anchorQuotient_domRestrict Q)
  rw [show defectRelationCoeffMap Q
      ⟨r.coefficients, r.coefficients_mem_relationKernel⟩ =
        (Submodule.mkQ (localDisplacementCoeffSpace Q))
          (sparseRelationGiftCoeff Q r.1) by
      change (Submodule.mkQ (localDisplacementCoeffSpace Q))
          (relationGiftCoefficientMap Q
            ⟨r.coefficients, r.coefficients_mem_relationKernel⟩) = _
      rw [relationGiftCoefficientMap_sparse]] at hmaps
  exact hmaps.symm

/-- The image of the pointed coefficient-relation space lies in the
corresponding quotient line-gift space. -/
theorem populatedAnchorQuotientMap_lineSpace_le
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q) :
    (fanoLineRelationCoeffSpaceThrough Q x).map
        (populatedAnchorQuotientMap Q) ≤
      fanoLineGiftQuotientSpaceThrough Q x := by
  rw [fanoLineRelationCoeffSpaceThrough, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ⟨r, hx, rfl⟩, rfl⟩
  rw [populatedAnchorQuotientMap_line_coefficients Q r]
  refine ⟨⟨sparseRelationGiftCoeff Q r.1, ?_⟩, rfl⟩
  apply Submodule.subset_span
  exact ⟨r, hx, rfl⟩

/-- Restricting the coefficient gift map to pointed line relations lands in
the quotient span of pointed line gifts. -/
theorem defectRelationCoeffMap_pointedLine_range_le
    (Q : Submodule F₂ QuadraticQuotient) (x : PopulatedPoint Q) :
    LinearMap.range
        ((defectRelationCoeffMap Q).domRestrict
          (fanoLineRelationSubspaceThrough Q x)) ≤
      fanoLineGiftQuotientSpaceThrough Q x := by
  rintro _ ⟨a, rfl⟩
  apply populatedAnchorQuotientMap_lineSpace_le Q x
  refine ⟨a.1.1, a.2, ?_⟩
  have hmaps := congrArg
    (fun f : relationKernel (populatedQuotientPoint (Q := Q)) →ₗ[F₂]
        (TargetCoeff ⧸ localDisplacementCoeffSpace Q) ↦ f a.1)
    (defectRelationCoeffMap_eq_anchorQuotient_domRestrict Q)
  simpa using hmaps.symm

/-- Unconditional pointed Fano-incidence rank theorem.  In a rank-three
defect, the entire gift range is at most one dimension larger than the span
of line gifts through any populated point. -/
theorem relationGiftRank_le_lineQuotientRank_add_one_of_finrank_le_three
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3) (x : PopulatedPoint Q) :
    relationGiftRank Q ≤
      Module.finrank F₂ (fanoLineGiftQuotientSpaceThrough Q x) + 1 := by
  rw [relationGiftRank_eq_coefficients]
  have hcodim : Module.finrank F₂
      (relationKernel (populatedQuotientPoint (Q := Q))) ≤
      Module.finrank F₂ (fanoLineRelationSubspaceThrough Q x) + 1 := by
    rw [fanoLineRelationSubspaceThrough_finrank]
    exact fanoLineRelationCoeffSpaceThrough_codim_le_one Q hQ x
  have hrank := finrank_range_le_domRestrict_range_add_one
    (defectRelationCoeffMap Q) (fanoLineRelationSubspaceThrough Q x) hcodim
  have hline := Submodule.finrank_mono
    (defectRelationCoeffMap_pointedLine_range_le Q x)
  omega

/-- Sharp one-rational-place gift bound from the unconditional pointed
incidence theorem and the rational local secant pivots. -/
theorem relationGiftRank_le_three_of_rationalZero_place
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q) (q : LocalKleinParam)
    (hq : RationalLocalEffective q)
    (hxPoint : populatedQuotientPoint x = closedPlaceQuotientPoint 0 q)
    (hzero : IsRepresentedPlace Q 0) :
    relationGiftRank Q ≤ 3 := by
  have hgift :=
    relationGiftRank_le_lineQuotientRank_add_one_of_finrank_le_three
      Q hQ x
  have hline :=
    fanoLineGiftCoeffSpaceThrough_rationalZero_quotientRank_le_two
      Q x q hq hxPoint hzero
  change Module.finrank F₂
      (fanoLineGiftQuotientSpaceThrough Q x) ≤ 2 at hline
  omega

/-- Representing the zero rational place forces relation-gift rank at most
three in every rank-three defect. -/
theorem relationGiftRank_le_three_of_represented_rationalZero
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hzero : IsRepresentedPlace Q 0) :
    relationGiftRank Q ≤ 3 := by
  let p := representedClosedPlaceParam Q 0 hzero
  let q : LocalKleinParam := p.2.1
  have hq : RationalLocalEffective q := by
    have hm := p.2.2
    change q ∈ effectiveParamsAt 0 at hm
    rw [effectiveParamsAt, if_neg (by decide)] at hm
    simpa [rationalEffectiveParams] using hm
  refine relationGiftRank_le_three_of_rationalZero_place Q hQ
    (representedPopulatedPoint Q 0 hzero) q hq ?_ hzero
  rfl

/-- Sharp degree-two one-place gift bound from the unconditional pointed
incidence theorem and the degree-two local secant pivots. -/
theorem relationGiftRank_le_two_of_degreeTwo_place
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (x : PopulatedPoint Q) (q : LocalKleinParam)
    (hq : DegreeTwoLocalEffective q)
    (hxPoint : populatedQuotientPoint x = closedPlaceQuotientPoint 3 q)
    (hdegree : IsRepresentedPlace Q 3) :
    relationGiftRank Q ≤ 2 := by
  have hgift :=
    relationGiftRank_le_lineQuotientRank_add_one_of_finrank_le_three
      Q hQ x
  have hline :=
    fanoLineGiftCoeffSpaceThrough_degreeTwo_quotientRank_le_one
      Q x q hq hxPoint hdegree
  change Module.finrank F₂
      (fanoLineGiftQuotientSpaceThrough Q x) ≤ 1 at hline
  omega

/-- Representing the degree-two place forces relation-gift rank at most two
in every rank-three defect. -/
theorem relationGiftRank_le_two_of_represented_degreeTwo
    (Q : Submodule F₂ QuadraticQuotient)
    (hQ : Module.finrank F₂ Q ≤ 3)
    (hdegree : IsRepresentedPlace Q 3) :
    relationGiftRank Q ≤ 2 := by
  let p := representedClosedPlaceParam Q 3 hdegree
  let q : LocalKleinParam := p.2.1
  have hq : DegreeTwoLocalEffective q := by
    have hm := p.2.2
    change q ∈ effectiveParamsAt 3 at hm
    rw [effectiveParamsAt, if_pos rfl] at hm
    simpa [degreeTwoEffectiveParams] using hm
  refine relationGiftRank_le_two_of_degreeTwo_place Q hQ
    (representedPopulatedPoint Q 3 hdegree) q hq ?_ hdegree
  rfl

end

end N5
end UnrestrictedBooleanMul
