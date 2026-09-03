import UnrestrictedBooleanMul.N5.SuffixBudget
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Splitting quadratic defect from genuinely high directions

The target ambient is contained in the degree-at-most-two ANFs.  Consequently
the defect of any wire state splits exactly into its defect inside the
quadratic part and the dimension contributed above degree two.  This is the
algebraic form of the manuscript budget `e + s ≤ 3`; it does not enumerate
circuits or high-degree ANFs.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The degree-at-most-two part of an arbitrary wire state. -/
def stateQuadraticPart (V : Submodule F₂ (ANF 10)) :
    Submodule F₂ (ANF 10) :=
  V ⊓ N4.quadraticANFSpace 10

/-- Defect already visible inside the quadratic part of a state. -/
def stateQuadraticDefectRank (V : Submodule F₂ (ANF 10)) : Nat :=
  N4.flagDefectRank (stateQuadraticPart V) (mulTarget 5)

/-- Number of independent directions of a state modulo all quadratic ANFs. -/
def stateHighRank (V : Submodule F₂ (ANF 10)) : Nat :=
  Module.finrank F₂ V - Module.finrank F₂ (stateQuadraticPart V)

/-- Image of a state in the quotient by all degree-at-most-two ANFs. -/
def stateHighImage (V : Submodule F₂ (ANF 10)) :
    Submodule F₂ ((ANF 10) ⧸ N4.quadraticANFSpace 10) :=
  Submodule.map (Submodule.mkQ (N4.quadraticANFSpace 10)) V

theorem stateQuadraticPart_inf_targetAmbient
    (V : Submodule F₂ (ANF 10)) :
    stateQuadraticPart V ⊓ N4.targetAmbient 10 (mulTarget 5) =
      V ⊓ N4.targetAmbient 10 (mulTarget 5) := by
  rw [stateQuadraticPart, inf_assoc,
    inf_eq_right.mpr targetAmbient_five_le_quadraticANFSpace]

/-- The total quotient defect is exactly the sum of the quadratic defect and
the genuinely high rank. -/
theorem flagDefectRank_eq_quadratic_add_high
    (V : Submodule F₂ (ANF 10)) :
    N4.flagDefectRank V (mulTarget 5) =
      stateQuadraticDefectRank V + stateHighRank V := by
  have hquadLe : Module.finrank F₂ (stateQuadraticPart V) ≤
      Module.finrank F₂ V :=
    Submodule.finrank_mono inf_le_left
  have hambLe : Module.finrank F₂
      ↥(V ⊓ N4.targetAmbient 10 (mulTarget 5)) ≤
        Module.finrank F₂ (stateQuadraticPart V) := by
    apply Submodule.finrank_mono
    rintro p ⟨hpV, hpA⟩
    exact ⟨hpV, targetAmbient_five_le_quadraticANFSpace hpA⟩
  unfold stateQuadraticDefectRank stateHighRank N4.flagDefectRank
  rw [stateQuadraticPart_inf_targetAmbient]
  omega

/-- The high quotient image has precisely the high rank defined above. -/
theorem stateHighImage_finrank (V : Submodule F₂ (ANF 10)) :
    Module.finrank F₂ (stateHighImage V) = stateHighRank V := by
  let Q := N4.quadraticANFSpace 10
  let f : V →ₗ[F₂] (ANF 10 ⧸ Q) := (Submodule.mkQ Q).domRestrict V
  have hrange : LinearMap.range f = stateHighImage V := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker f = Q.comap V.subtype := by
    ext x
    simp [f, Submodule.Quotient.mk_eq_zero]
  let e : ↥(Q.comap V.subtype) ≃ₗ[F₂] ↥(stateQuadraticPart V) := {
    toFun x := ⟨x.1.1, x.1.2, x.2⟩
    invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  have hkerRank : Module.finrank F₂ (LinearMap.ker f) =
      Module.finrank F₂ (stateQuadraticPart V) := by
    rw [hker]
    exact e.finrank_eq
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange, hkerRank] at hrank
  have hquadLe : Module.finrank F₂ (stateQuadraticPart V) ≤
      Module.finrank F₂ V := Submodule.finrank_mono inf_le_left
  unfold stateHighRank
  exact Nat.eq_sub_of_add_eq hrank

/-- High rank is monotone under inclusion of wire states. -/
theorem stateHighRank_mono {V W : Submodule F₂ (ANF 10)}
    (hVW : V ≤ W) : stateHighRank V ≤ stateHighRank W := by
  rw [← stateHighImage_finrank, ← stateHighImage_finrank]
  exact Submodule.finrank_mono (Submodule.map_mono hVW)

theorem stateHighImage_eq_bot_iff
    (V : Submodule F₂ (ANF 10)) :
    stateHighImage V = ⊥ ↔ V ≤ N4.quadraticANFSpace 10 := by
  constructor
  · intro h p hp
    have hmem : Submodule.mkQ (N4.quadraticANFSpace 10) p ∈
        stateHighImage V := ⟨p, hp, rfl⟩
    rw [h] at hmem
    have hzero : Submodule.mkQ (N4.quadraticANFSpace 10) p = 0 := by
      simpa using hmem
    exact (Submodule.Quotient.mk_eq_zero _).mp hzero
  · intro h
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      have hzero : Submodule.mkQ (N4.quadraticANFSpace 10) p = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (h hp)
      simp [hzero]
    · exact bot_le

/-- A genuinely nonquadratic wire forces a nonzero high quotient. -/
theorem one_le_stateHighRank_of_mem_not_quadratic
    {V : Submodule F₂ (ANF 10)} {g : ANF 10}
    (hgV : g ∈ V) (hghigh : g ∉ N4.quadraticANFSpace 10) :
    1 ≤ stateHighRank V := by
  by_contra hnot
  have hzero : stateHighRank V = 0 := by omega
  have himageRank : Module.finrank F₂ (stateHighImage V) = 0 := by
    rw [stateHighImage_finrank, hzero]
  have himageBot : stateHighImage V = ⊥ :=
    Submodule.finrank_eq_zero.mp himageRank
  exact hghigh ((stateHighImage_eq_bot_iff V).mp himageBot hgV)

/-- A quadratic base contributes its full old defect to every containing
state's quadratic defect. -/
theorem quadraticBase_defect_le_quadraticDefect
    {W V : Submodule F₂ (ANF 10)}
    (hWV : W ≤ V) (hWquad : W ≤ N4.quadraticANFSpace 10) :
    N4.flagDefectRank W (mulTarget 5) ≤ stateQuadraticDefectRank V := by
  unfold stateQuadraticDefectRank
  apply flagDefectRank_mono
  intro p hp
  exact ⟨hWV hp, hWquad hp⟩

/-- Exact algebraic high-direction budget above a quadratic base. -/
theorem quadraticBase_defect_add_high_le
    {W V : Submodule F₂ (ANF 10)}
    (hWV : W ≤ V) (hWquad : W ≤ N4.quadraticANFSpace 10) :
    N4.flagDefectRank W (mulTarget 5) + stateHighRank V ≤
      N4.flagDefectRank V (mulTarget 5) := by
  have hlow := quadraticBase_defect_le_quadraticDefect hWV hWquad
  rw [flagDefectRank_eq_quadratic_add_high V]
  omega

/-- Every defect-legal suffix above a quadratic base satisfies the manuscript
budget `e + s ≤ 3`. -/
theorem DefectLegalSuffix.quadraticDefect_add_high_le_three
    {W V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix W V)
    (hWquad : W ≤ N4.quadraticANFSpace 10) :
    N4.flagDefectRank W (mulTarget 5) + stateHighRank V ≤ 3 := by
  exact (quadraticBase_defect_add_high_le hreach.start_le hWquad).trans
    hreach.final_defect_le_three

/-- In particular, a defect-two quadratic base leaves at most one genuinely
high direction in every legal suffix state. -/
theorem DefectLegalSuffix.highRank_le_one_of_quadratic_defect_two
    {W V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix W V)
    (hWquad : W ≤ N4.quadraticANFSpace 10)
    (hWdef : N4.flagDefectRank W (mulTarget 5) = 2) :
    stateHighRank V ≤ 1 := by
  have hbudget := hreach.quadraticDefect_add_high_le_three hWquad
  omega

/-- A state of high rank at most one has an actual wire representative `g`
for its unique possible high direction.  Every wire differs from either zero
or `g` by a quadratic ANF. -/
theorem exists_single_highRepresentative
    (V : Submodule F₂ (ANF 10)) (hhigh : stateHighRank V ≤ 1) :
    ∃ g : ANF 10, g ∈ V ∧
      ∀ p : ANF 10, p ∈ V →
        ∃ a : F₂, p + a • g ∈ N4.quadraticANFSpace 10 := by
  have himage : Module.finrank F₂ (stateHighImage V) ≤ 1 := by
    rw [stateHighImage_finrank]
    exact hhigh
  rcases finrank_le_one_iff.mp himage with ⟨v, hv⟩
  rcases v.2 with ⟨g, hgV, hg⟩
  refine ⟨g, hgV, ?_⟩
  intro p hpV
  let w : stateHighImage V :=
    ⟨Submodule.mkQ (N4.quadraticANFSpace 10) p, ⟨p, hpV, rfl⟩⟩
  rcases hv w with ⟨a, ha⟩
  have hquot : a • Submodule.mkQ (N4.quadraticANFSpace 10) g =
      Submodule.mkQ (N4.quadraticANFSpace 10) p := by
    have := congrArg (fun z : stateHighImage V => z.1) ha
    simpa [w, hg] using this
  refine ⟨a, ?_⟩
  apply (Submodule.Quotient.mk_eq_zero
    (N4.quadraticANFSpace 10)).mp
  change (Submodule.mkQ (N4.quadraticANFSpace 10)) (p + a • g) = 0
  rw [map_add, map_smul, hquot]
  calc
    Submodule.mkQ (N4.quadraticANFSpace 10) p +
        Submodule.mkQ (N4.quadraticANFSpace 10) p =
        ((1 : F₂) + 1) •
          Submodule.mkQ (N4.quadraticANFSpace 10) p := by
            rw [add_smul, one_smul]
    _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]

/-- Defect-two suffix form: one high representative suffices jointly for all
wires at any legal endpoint. -/
theorem DefectLegalSuffix.exists_single_highRepresentative_of_defect_two
    {W V : Submodule F₂ (ANF 10)}
    (hreach : DefectLegalSuffix W V)
    (hWquad : W ≤ N4.quadraticANFSpace 10)
    (hWdef : N4.flagDefectRank W (mulTarget 5) = 2) :
    ∃ g : ANF 10, g ∈ V ∧
      ∀ p : ANF 10, p ∈ V →
        ∃ a : F₂, p + a • g ∈ N4.quadraticANFSpace 10 :=
  exists_single_highRepresentative V
    (hreach.highRank_le_one_of_quadratic_defect_two hWquad hWdef)

end
end N5
end UnrestrictedBooleanMul
