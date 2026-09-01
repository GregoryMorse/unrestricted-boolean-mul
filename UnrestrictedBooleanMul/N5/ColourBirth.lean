import UnrestrictedBooleanMul.N5.EnvelopeKernel

/-!
# Independent cubic colours create a new high-degree direction

This module certifies manuscript Lemma 12.1, specifically the injectivity in
equation (12.2).  For the four normalized cubic colours, the six pairwise
products have an injective projection to six named quartic ANF coordinates.

The proof is an algebraic sparse-pivot calculation.  It does not enumerate
coefficient assignments.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The four normalized cubic colour directions from Section 12. -/
def colourDirection : Fin 4 → ANF 10 :=
  ![monomial ({0, 1, 5} : Finset (Fin 10)),
    monomial ({0, 5, 6} : Finset (Fin 10)),
    monomial ({0, 1, 6} : Finset (Fin 10)) +
      monomial ({0, 2, 5} : Finset (Fin 10)),
    monomial ({0, 5, 7} : Finset (Fin 10)) +
      monomial ({1, 5, 6} : Finset (Fin 10))]

/-- Left endpoint of the ordered pair list
`(c₁c₂,c₁c₃,c₁c₄,c₂c₃,c₂c₄,c₃c₄)`. -/
def colourPairLeft : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- Right endpoint of the ordered pair list. -/
def colourPairRight : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- Six quartic coordinates used to witness independent colour birth. -/
def colourQuarticRow : Fin 6 → Finset (Fin 10) :=
  ![({0, 1, 2, 5} : Finset (Fin 10)),
    ({0, 1, 5, 6} : Finset (Fin 10)),
    ({0, 2, 5, 6} : Finset (Fin 10)),
    ({0, 1, 5, 7} : Finset (Fin 10)),
    ({0, 2, 5, 7} : Finset (Fin 10)),
    ({0, 5, 6, 7} : Finset (Fin 10))]

/-- The sparse `6 × 6` coefficient matrix displayed in equation (12.2). -/
def colourBirthMatrix : Fin 6 → Fin 6 → F₂ :=
  ![![0, 1, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0]]

/-- Direct ANF verification of every entry of the manuscript matrix. -/
theorem colourBirth_product_coefficient (r k : Fin 6) :
    (colourDirection (colourPairLeft k) *
        colourDirection (colourPairRight k)).coeff
      ⟨colourQuarticRow r⟩ = colourBirthMatrix r k := by
  fin_cases r <;> fin_cases k <;>
    simp (disch := decide) [colourDirection, colourPairLeft, colourPairRight,
      colourQuarticRow, colourBirthMatrix, monomial_mul, coeff_monomial,
      add_mul, mul_add] <;> decide

/-- A linear combination of the six pairwise cubic-colour products. -/
def colourPairProductLinear : (Fin 6 → F₂) →ₗ[F₂] ANF 10 where
  toFun α := ∑ k : Fin 6, α k •
    (colourDirection (colourPairLeft k) *
      colourDirection (colourPairRight k))
  map_add' α β := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a α := by
    change (∑ k : Fin 6, (a * α k) •
      (colourDirection (colourPairLeft k) *
        colourDirection (colourPairRight k))) =
      a • ∑ k : Fin 6, α k •
        (colourDirection (colourPairLeft k) *
          colourDirection (colourPairRight k))
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    simp only [smul_smul]

/-- Projection to the six selected quartic ANF coordinates. -/
def colourQuarticProjection : ANF 10 →ₗ[F₂] (Fin 6 → F₂) where
  toFun p r := p.coeff ⟨colourQuarticRow r⟩
  map_add' p q := by
    ext r
    simp
  map_smul' a p := by
    ext r
    simp

/-- The selected high-degree projection of the colour-pair multiplication
map in equation (12.2). -/
def colourBirthMap : (Fin 6 → F₂) →ₗ[F₂] (Fin 6 → F₂) :=
  colourQuarticProjection.comp colourPairProductLinear

theorem colourBirthMap_apply (alpha : Fin 6 → F₂) (r : Fin 6) :
    colourBirthMap alpha r =
      ∑ k : Fin 6, alpha k * colourBirthMatrix r k := by
  change colourQuarticProjection
    (∑ k : Fin 6, alpha k •
      (colourDirection (colourPairLeft k) *
        colourDirection (colourPairRight k))) r = _
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _hk
  exact congrArg (fun x => alpha k * x)
    (colourBirth_product_coefficient r k)

/-- The six selected quartic rows separate all six colour-pair products. -/
theorem colourBirthMap_ker_eq_bot : LinearMap.ker colourBirthMap = ⊥ := by
  apply le_antisymm
  · intro alpha halpha
    have hmap := (LinearMap.mem_ker).mp halpha
    have h1 : alpha 1 = 0 := by
      have h := congrFun hmap 0
      simpa [colourBirthMap_apply, colourBirthMatrix,
        Fin.sum_univ_succ] using h
    have h3 : alpha 3 = 0 := by
      have h := congrFun hmap 2
      simpa [colourBirthMap_apply, colourBirthMatrix,
        Fin.sum_univ_succ] using h
    have h2 : alpha 2 = 0 := by
      have h := congrFun hmap 3
      simpa [colourBirthMap_apply, colourBirthMatrix,
        Fin.sum_univ_succ] using h
    have h5 : alpha 5 = 0 := by
      have h := congrFun hmap 4
      simpa [colourBirthMap_apply, colourBirthMatrix,
        Fin.sum_univ_succ] using h
    have h4 : alpha 4 = 0 := by
      have h := congrFun hmap 5
      simpa [colourBirthMap_apply, colourBirthMatrix,
        Fin.sum_univ_succ] using h
    have h0 : alpha 0 = 0 := by
      have h := congrFun hmap 1
      simpa [colourBirthMap_apply, colourBirthMatrix,
        Fin.sum_univ_succ, h1, h2, h3, h4, h5] using h
    have halpha0 : alpha = 0 := by
      funext k
      fin_cases k <;> assumption
    simpa [halpha0]
  · exact bot_le

/-- Kernel-checked form of manuscript Lemma 12.1 / equation (12.2): six
independent pairwise cubic-colour products are born in high degree. -/
theorem independentColours_birth : Function.Injective colourBirthMap :=
  LinearMap.ker_eq_bot.mp colourBirthMap_ker_eq_bot

end
end N5
end UnrestrictedBooleanMul
