import UnrestrictedBooleanMul.Models
import UnrestrictedBooleanMul.Mul

/-!
# Positive bilinear witnesses for six-term and five-by-six multiplication

The 17-term data is transcribed from the supplied n6 JSON witness. The 16-term
rectangle is its `a₀ = 0` restriction, deleting the vanishing first product
and shifting the output coefficient index. Both tensors are checked directly
by ordinary `decide`, followed by the generic semantic circuit conversion.
No negative enumeration or external verdict is a premise.
-/

namespace UnrestrictedBooleanMul.N6

def sixMask : Fin 17 → Nat :=
  ![1, 2, 3, 6, 7, 12, 16, 18, 24, 27, 32, 37, 41, 45, 48, 56, 63]

def sixOutputSupport : Fin 11 → Finset (Fin 17) :=
  ![{0}, {0, 1, 2}, {2, 3, 4},
    {1, 3, 5, 6, 8, 11, 13, 14, 15},
    {1, 2, 5, 7, 9, 11, 13, 14, 15},
    {0, 1, 6, 7, 10, 11, 12, 13},
    {0, 1, 3, 5, 8, 9, 10, 11, 15, 16},
    {1, 2, 3, 4, 5, 6, 8, 12, 13},
    {8, 14, 15}, {6, 10, 14}, {10}]

def bitCoefficient (mask index : Nat) : F₂ := if mask.testBit index then 1 else 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- 396 scalar tensor identities, checked by the Lean kernel. -/
def seventeen : BilinearFormula (polynomialTensor 6 6) 17 where
  left k i := bitCoefficient (sixMask k) i.val
  right k j := bitCoefficient (sixMask k) j.val
  output s k := if k ∈ sixOutputSupport s then 1 else 0
  correct := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- 300 independent identities for the rectangular restriction. -/
def sixteen : BilinearFormula (polynomialTensor 5 6) 16 where
  left k i := bitCoefficient (sixMask k.succ) (i.val + 1)
  right k j := bitCoefficient (sixMask k.succ) j.val
  output s k := if k.succ ∈ sixOutputSupport s.succ then 1 else 0
  correct := by decide

theorem bilinearRank_six_le_seventeen : bilinearRank (polynomialTensor 6 6) ≤ 17 :=
  bilinearRank_le seventeen

theorem bilinearRank_five_six_le_sixteen : bilinearRank (polynomialTensor 5 6) ≤ 16 :=
  bilinearRank_le sixteen

theorem quadraticComplexity_six_le_seventeen :
    quadraticComplexity (polynomialTensor 6 6).realize ≤ 17 :=
  (quadraticComplexity_le_bilinearRank _).trans bilinearRank_six_le_seventeen

theorem quadraticComplexity_five_six_le_sixteen :
    quadraticComplexity (polynomialTensor 5 6).realize ≤ 16 :=
  (quadraticComplexity_le_bilinearRank _).trans bilinearRank_five_six_le_sixteen

theorem polynomialTensor_six_realize : (polynomialTensor 6 6).realize = Mul 6 := by
  funext s
  simp [BilinearTensor.realize, polynomialTensor, Mul, mulCoefficient,
    tensorLeftVar, tensorRightVar, aVar, bVar, Fin.castAdd, Fin.natAdd,
    Fin.castLE, Nat.add_comm]

theorem mul_six_upper : HasCircuit (Mul 6) 17 := by
  rw [← polynomialTensor_six_realize]
  exact seventeen.toQuadratic.hasCircuit

theorem mul_five_six_upper : HasCircuit (polynomialTensor 5 6).realize 16 :=
  sixteen.toQuadratic.hasCircuit

end UnrestrictedBooleanMul.N6
