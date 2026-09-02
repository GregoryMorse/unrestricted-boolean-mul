import UnrestrictedBooleanMul.N5.EnvelopeRankTwoLines

/-!
# The rational secant triangle

The remaining rank-two Hankel line is cubic-rigid.  The proof uses a sparse
set of twenty exterior coordinates and linear elimination over `F₂`; it does
not enumerate Boolean assignments or circuit states.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

def rationalTriangleLeftTwo : TwoForm :=
  rationalZeroValueTwo + rationalOneValueTwo

def rationalTriangleRightTwo : TwoForm :=
  rationalZeroValueTwo + rationalInfinityValueTwo

set_option linter.unusedSimpArgs false

/-- The rational secant triangle has trivial cubic syzygy kernel. -/
theorem rationalTriangle_cubic_syzygy (x y : LinearForm)
    (h : factorPlaneCubic x y rationalTriangleLeftTwo
      rationalTriangleRightTwo = 0) :
    x = 0 ∧ y = 0 := by
  have hc (i j k : Fin 10) := congrFun (congrFun (congrFun h i) j) k
  have h015 := hc (aCoord 0) (aCoord 1) (bCoord 0)
  have h016 := hc (aCoord 0) (aCoord 1) (bCoord 1)
  have h025 := hc (aCoord 0) (aCoord 2) (bCoord 0)
  have h026 := hc (aCoord 0) (aCoord 2) (bCoord 1)
  have h035 := hc (aCoord 0) (aCoord 3) (bCoord 0)
  have h036 := hc (aCoord 0) (aCoord 3) (bCoord 1)
  have h045 := hc (aCoord 0) (aCoord 4) (bCoord 0)
  have h046 := hc (aCoord 0) (aCoord 4) (bCoord 1)
  have h049 := hc (aCoord 0) (aCoord 4) (bCoord 4)
  have h056 := hc (aCoord 0) (bCoord 0) (bCoord 1)
  have h057 := hc (aCoord 0) (bCoord 0) (bCoord 2)
  have h058 := hc (aCoord 0) (bCoord 0) (bCoord 3)
  have h059 := hc (aCoord 0) (bCoord 0) (bCoord 4)
  have h067 := hc (aCoord 0) (bCoord 1) (bCoord 2)
  have h068 := hc (aCoord 0) (bCoord 1) (bCoord 3)
  have h069 := hc (aCoord 0) (bCoord 1) (bCoord 4)
  have h149 := hc (aCoord 1) (aCoord 4) (bCoord 4)
  have h156 := hc (aCoord 1) (bCoord 0) (bCoord 1)
  have h459 := hc (aCoord 4) (bCoord 0) (bCoord 4)
  have h469 := hc (aCoord 4) (bCoord 1) (bCoord 4)
  simp [factorPlaneCubic, ambientVectorWedgeTwo, N4.vectorWedgeTwoN,
    rationalTriangleLeftTwo, rationalTriangleRightTwo,
    rationalZeroValueTwo, rationalOneValueTwo,
    rationalInfinityValueTwo, targetPairTwo, aOneEval, bOneEval,
    aLinear, bLinear, Pi.basisFun, ambientTwoCoeff_add,
    ambientTwoCoeff_squarefreeWedge,
    aCoord_ne_bCoord, Fin.sum_univ_succ] at h015 h016 h025 h026 h035 h036 h045 h046 h049 h056 h057 h058 h059 h067 h068 h069 h149 h156 h459 h469
  have htwo : (2 : F₂) = 0 := N3Certificate.two_eq_zero_f2
  simp only [show (1 + 1 : F₂) = 0 by decide, mul_zero, add_zero] at h015 h016 h025 h026 h035 h036 h045 h046 h049 h056 h057 h058 h059 h067 h068 h069 h149 h156 h459 h469
  have hx0 : x (aCoord 0) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h046 + h049
  have hx1 : x (aCoord 1) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h016 + h046 + h149
  have hx2 : x (aCoord 2) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h015 + h016 + h025 + h046 + h149
  have hx3 : x (aCoord 3) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h015 + h016 + h035 + h046 + h149
  have hx4 : x (aCoord 4) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h015 + h016 + h045 + h046 + h149
  have hx5 : x (bCoord 0) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h069 + h156 + h459
  have hx6 : x (bCoord 1) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h069 + h469
  have hx7 : x (bCoord 2) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h056 + h057 + h069 + h469
  have hx8 : x (bCoord 3) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h056 + h058 + h069 + h469
  have hx9 : x (bCoord 4) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h056 + h059 + h069 + h469
  have hy0 : y (aCoord 0) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h015 + h016 + h046 + h149
  have hy1 : y (aCoord 1) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h015 + h046 + h149
  have hy2 : y (aCoord 2) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h015 + h016 + h026 + h046 + h149
  have hy3 : y (aCoord 3) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h015 + h016 + h036 + h046 + h149
  have hy4 : y (aCoord 4) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h015 + h016 + h149
  have hy5 : y (bCoord 0) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h056 + h069 + h469
  have hy6 : y (bCoord 1) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h056 + h069 + h156 + h469
  have hy7 : y (bCoord 2) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h056 + h067 + h069 + h156 + h469
  have hy8 : y (bCoord 3) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h056 + h068 + h069 + h156 + h469
  have hy9 : y (bCoord 4) = 0 := by
    linear_combination
      (norm := (ring_nf; try simp only [htwo, mul_zero, add_zero, sub_zero]))
      h056 + h156 + h469
  constructor
  · funext i
    fin_cases i <;> simp_all [aCoord, bCoord]
  · funext i
    fin_cases i <;> simp_all [aCoord, bCoord]

/-- Cubic rigidity is intrinsic to the quadratic plane and hence survives
every ordered basis change. -/
theorem cubicRigidPlane_basisChange (q c : TwoForm)
    (hrigid : CubicRigidPlane q c) (g : PlaneBasisChange) :
    CubicRigidPlane (g.basisPair q c).1 (g.basisPair q c).2 := by
  intro x y hcubic
  let lm := g.inverse.basisPair x y
  have hcanonical : factorPlaneCubic lm.1 lm.2 q c = 0 := by
    calc
      factorPlaneCubic lm.1 lm.2 q c =
          (lowProductHighPart lm.1 lm.2 q c).2 := rfl
      _ = (changedLowProductHighPart g lm.1 lm.2 q c).2 :=
        congrArg Prod.snd (planeBasisChange_high g lm.1 lm.2 q c).symm
      _ = (lowProductHighPart x y (g.basisPair q c).1
          (g.basisPair q c).2).2 := by
        simpa [lm] using congrArg Prod.snd
          (changedLowProductHighPart_inverse g x y q c)
      _ = factorPlaneCubic x y (g.basisPair q c).1
          (g.basisPair q c).2 := rfl
      _ = 0 := hcubic
  rcases hrigid lm.1 lm.2 hcanonical with ⟨hl, hm⟩
  have hpair := g.basisPair_apply_inverse x y
  change g.basisPair lm.1 lm.2 = (x, y) at hpair
  rw [hl, hm] at hpair
  have hxy : x = 0 ∧ y = 0 := by
    cases g <;> simpa [PlaneBasisChange.basisPair] using hpair.symm
  exact hxy

end
end N5
end UnrestrictedBooleanMul
