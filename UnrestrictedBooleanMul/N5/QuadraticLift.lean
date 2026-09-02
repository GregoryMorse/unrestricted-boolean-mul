import UnrestrictedBooleanMul.N5.PrefixState

/-!
# A canonical squarefree-quadratic ANF section

This file supplies the small linear-algebra bridge from the 45-coordinate
quadratic space back to ten-variable Boolean ANFs.  The section uses one ANF
monomial per two-element support and is a right inverse to
`quadraticProjection`; hence it is injective.  No coordinate enumeration is
involved.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Interpret a squarefree quadratic coefficient form as its pure quadratic
Boolean ANF. -/
def quadraticANFOfForm (q : TwoForm) : ANF 10 :=
  ∑ s : QuadraticIndex 10, q s • monomial s.1

def quadraticANFOfFormLinear : TwoForm →ₗ[F₂] ANF 10 where
  toFun := quadraticANFOfForm
  map_add' q r := by
    simp [quadraticANFOfForm, add_smul, Finset.sum_add_distrib]
  map_smul' a q := by
    simp [quadraticANFOfForm, Finset.smul_sum, smul_smul]

@[simp] theorem quadraticProjection_quadraticANFOfForm (q : TwoForm) :
    quadraticProjection 10 (quadraticANFOfForm q) = q := by
  classical
  ext s
  simp [quadraticANFOfForm, quadraticProjection, coeff_monomial]
  rw [Fintype.sum_eq_single s]
  · simp
  · intro t hts
    have hvars : t.1 ≠ s.1 := by
      intro h
      exact hts (Subtype.ext h)
    simp [hvars]

@[simp] theorem quadraticANFOfFormLinear_rightInverse (q : TwoForm) :
    quadraticProjection 10 (quadraticANFOfFormLinear q) = q :=
  quadraticProjection_quadraticANFOfForm q

theorem quadraticANFOfFormLinear_injective :
    Function.Injective quadraticANFOfFormLinear := by
  intro q r h
  have := congrArg (quadraticProjection 10) h
  simpa using this

/-- The pure squarefree-quadratic complement to the affine ANFs. -/
def pureQuadraticANFSpace : Submodule F₂ (ANF 10) :=
  LinearMap.range quadraticANFOfFormLinear

@[simp] theorem quadraticANFOfForm_basis (s : QuadraticIndex 10) :
    quadraticANFOfForm ((Pi.basisFun F₂ (QuadraticIndex 10)) s) =
      monomial s.1 := by
  classical
  rw [quadraticANFOfForm]
  simp [Pi.basisFun]

theorem quadraticMonomial_mem_pure (s : QuadraticIndex 10) :
    monomial s.1 ∈ pureQuadraticANFSpace := by
  exact ⟨(Pi.basisFun F₂ (QuadraticIndex 10)) s,
    quadraticANFOfForm_basis s⟩

theorem aVar_mul_bVar_mem_pure (i j : Fin 5) :
    aVar 5 i * bVar 5 j ∈ pureQuadraticANFSpace := by
  let s := quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j)
  have hs : s.1 = {aCoord i, bCoord j} := rfl
  have hmon := quadraticMonomial_mem_pure s
  rw [hs] at hmon
  simpa [aVar_five_eq_X_aCoord, bVar_five_eq_X_bCoord, X] using hmon

theorem Mul_five_mem_pure (s : Fin 9) :
    Mul 5 s ∈ pureQuadraticANFSpace := by
  rw [Mul, mulCoefficient]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  split
  · exact aVar_mul_bVar_mem_pure i j
  · exact Submodule.zero_mem _

theorem targetANF_mem_pure (c : TargetCoeff) :
    targetANF c ∈ pureQuadraticANFSpace := by
  rw [targetANF]
  exact Submodule.sum_mem _ (fun s _ =>
    Submodule.smul_mem _ _ (Mul_five_mem_pure s))

theorem quadraticProjection_injective_on_pure
    {p q : ANF 10} (hp : p ∈ pureQuadraticANFSpace)
    (hq : q ∈ pureQuadraticANFSpace)
    (hprojection : quadraticProjection 10 p = quadraticProjection 10 q) :
    p = q := by
  rcases hp with ⟨x, rfl⟩
  rcases hq with ⟨y, rfl⟩
  change quadraticANFOfForm x = quadraticANFOfForm y
  apply congrArg quadraticANFOfForm
  simpa using hprojection

theorem quadraticANFOfForm_targetTwo (c : TargetCoeff) :
    quadraticANFOfForm (targetTwo c) = targetANF c := by
  apply quadraticProjection_injective_on_pure
  · exact ⟨targetTwo c, rfl⟩
  · exact targetANF_mem_pure c
  · rw [quadraticProjection_quadraticANFOfForm,
      quadraticProjection_targetANF]

theorem quadraticProjection_pureQuadraticANFSpace :
    Submodule.map (quadraticProjection 10) pureQuadraticANFSpace = ⊤ := by
  apply top_unique
  intro q _
  exact ⟨quadraticANFOfForm q, ⟨q, rfl⟩,
    quadraticProjection_quadraticANFOfForm q⟩

theorem affine_disjoint_pureQuadraticANFSpace :
    Disjoint (affine 10) pureQuadraticANFSpace := by
  rw [disjoint_iff_inf_le]
  rintro p ⟨hpAff, ⟨q, rfl⟩⟩
  have hzero := quadraticProjection_kills_affine 10 hpAff
  rw [LinearMap.mem_ker] at hzero
  change quadraticProjection 10 (quadraticANFOfForm q) = 0 at hzero
  rw [quadraticProjection_quadraticANFOfForm] at hzero
  subst q
  rw [map_zero]
  exact Submodule.zero_mem ⊥

/-- Lift a quadratic coordinate subspace into the pure quadratic ANFs. -/
def quadraticLiftSpace (W : Submodule F₂ TwoForm) :
    Submodule F₂ (ANF 10) :=
  Submodule.map quadraticANFOfFormLinear W

theorem quadraticLiftSpace_le_pure (W : Submodule F₂ TwoForm) :
    quadraticLiftSpace W ≤ pureQuadraticANFSpace := by
  rintro _ ⟨q, _hq, rfl⟩
  exact ⟨q, rfl⟩

/-- Pure quadratic ANFs have degree at most two. -/
theorem pureQuadraticANFSpace_le_quadraticANFSpace :
    pureQuadraticANFSpace ≤ N4.quadraticANFSpace 10 := by
  rintro _ ⟨q, rfl⟩ s hs
  classical
  change (quadraticANFOfForm q).coeff s = 0
  rw [quadraticANFOfForm, MonoidAlgebra.coeff_sum]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro t _ht
  have hne : t.1 ≠ s.vars := by
    intro h
    have hcard := congrArg Finset.card h
    have htcard : t.1.card = 2 := t.2
    omega
  have hcoeff : (monomial t.1 : ANF 10).coeff s = 0 := by
    rw [show s = ⟨s.vars⟩ by cases s; rfl]
    simp [coeff_monomial, hne]
  change q t * (monomial t.1 : ANF 10).coeff s = 0
  rw [hcoeff]
  simp

/-- Every degree-at-most-two ANF splits as an affine ANF plus its pure
quadratic part. -/
theorem quadraticANFSpace_eq_affine_sup_pure :
    N4.quadraticANFSpace 10 = affine 10 ⊔ pureQuadraticANFSpace := by
  apply le_antisymm
  · intro p hp
    have hreconstruct :
        p.coeff.sum (fun s c => c • monomial s.vars) = p := by
      calc
        p.coeff.sum (fun s c => c • monomial s.vars) =
            p.coeff.sum MonoidAlgebra.single := by
          apply Finsupp.sum_congr
          intro s _hs
          cases s
          simp [monomial]
        _ = p := MonoidAlgebra.sum_coeff_single p
    rw [← hreconstruct, Finsupp.sum]
    apply Submodule.sum_mem
    intro s hs
    have hcard : s.vars.card ≤ 2 := by
      by_contra hnot
      have hzero := hp s (by omega)
      exact (Finsupp.mem_support_iff.mp hs) hzero
    interval_cases hsCard : s.vars.card
    · have hs0 : s.vars = ∅ := Finset.card_eq_zero.mp hsCard
      rw [hs0]
      have hone : (monomial ∅ : ANF 10) = 1 := by
        rw [monomial, MonoidAlgebra.one_def]
        congr 1
      rw [hone]
      exact Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (one_mem_affine 10))
    · rcases Finset.card_eq_one.mp hsCard with ⟨i, hi⟩
      rw [hi]
      exact Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (X_mem_affine i))
    · let t : QuadraticIndex 10 := ⟨s.vars, hsCard⟩
      have ht : monomial s.vars ∈ pureQuadraticANFSpace := by
        simpa [t] using quadraticMonomial_mem_pure t
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ ht)
  · exact sup_le N4.affine_le_quadraticANFSpace
      pureQuadraticANFSpace_le_quadraticANFSpace

theorem quadraticProjection_quadraticLiftSpace
    (W : Submodule F₂ TwoForm) :
    Submodule.map (quadraticProjection 10) (quadraticLiftSpace W) = W := by
  apply le_antisymm
  · rintro q ⟨p, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw
  · intro q hq
    exact ⟨quadraticANFOfForm q, ⟨q, hq, rfl⟩,
      quadraticProjection_quadraticANFOfForm q⟩

theorem quadraticLiftSpace_finrank (W : Submodule F₂ TwoForm) :
    Module.finrank F₂ (quadraticLiftSpace W) = Module.finrank F₂ W := by
  let f := quadraticANFOfFormLinear.domRestrict W
  have hrange : LinearMap.range f = quadraticLiftSpace W := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  have hinj : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply quadraticANFOfFormLinear_injective
    exact h
  rw [← hrange]
  exact LinearMap.finrank_range_of_inj hinj

theorem affine_disjoint_quadraticLiftSpace (W : Submodule F₂ TwoForm) :
    Disjoint (affine 10) (quadraticLiftSpace W) :=
  Disjoint.mono_right (quadraticLiftSpace_le_pure W)
    affine_disjoint_pureQuadraticANFSpace

end
end N5
end UnrestrictedBooleanMul
