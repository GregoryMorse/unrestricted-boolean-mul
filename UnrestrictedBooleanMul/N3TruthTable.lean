import UnrestrictedBooleanMul.N3
import Batteries.Data.BitVec.Lemmas

/-!
# Independent truth-table cross-check for the `n = 3` lower bound

This module validates the concrete 64-bit encodings used while developing the
algebraic proof.  Nothing in `N3.lean` or the final theorem depends on it.
-/

namespace UnrestrictedBooleanMul

def bitF2 (b : Bool) : F₂ := if b then 1 else 0
def f2Bit (x : F₂) : Bool := decide (x = 1)

@[simp] theorem f2Bit_zero : f2Bit 0 = false := by decide
@[simp] theorem f2Bit_one : f2Bit 1 = true := by decide

@[simp] theorem bitF2_f2Bit (x : F₂) : bitF2 (f2Bit x) = x := by
  fin_cases x <;> rfl

@[simp] theorem bitF2_xor (a b : Bool) : bitF2 (xor a b) = bitF2 a + bitF2 b := by
  cases a <;> cases b <;> decide

@[simp] theorem bitF2_and (a b : Bool) : bitF2 (a && b) = bitF2 a * bitF2 b := by
  cases a <;> cases b <;> decide

theorem bitF2_injective : Function.Injective bitF2 := by
  intro a b h
  cases a <;> cases b <;> simp [bitF2] at h ⊢

def coeffBits {n : Nat} (c : Fin n → F₂) : BitVec n :=
  BitVec.ofFnLE (fun i ↦ f2Bit (c i))

@[simp] theorem coeffBits_getLsb {n : Nat} (c : Fin n → F₂) (i : Fin n) :
    (coeffBits c).getLsb i = f2Bit (c i) := by
  simp [coeffBits]

def sel (b : Bool) (x : BitVec 64) : BitVec 64 := if b then x else 0

@[simp] theorem bitF2_sel_getLsb (c : F₂) (x : BitVec 64) (q : Fin 64) :
    bitF2 ((sel (f2Bit c) x).getLsb q) = c * bitF2 (x.getLsb q) := by
  cases h : f2Bit c
  · have hc : c = 0 := by rw [← bitF2_f2Bit c, h]; rfl
    simp [sel, hc, bitF2]
  · have hc : c = 1 := by rw [← bitF2_f2Bit c, h]; rfl
    simp [sel, hc]

@[simp] theorem bitF2_sel_getElem (c : F₂) (x : BitVec 64) (q : Fin 64) :
    bitF2 (sel (f2Bit c) x)[q] = c * bitF2 x[q] :=
  bitF2_sel_getLsb c x q

@[simp] theorem bitF2_sel_getElemNat (c : F₂) (x : BitVec 64) (i : Nat) (h : i < 64) :
    bitF2 (sel (f2Bit c) x)[i] = c * bitF2 x[i] :=
  bitF2_sel_getLsb c x ⟨i, h⟩

def v0 : BitVec 64 := 0xAAAAAAAAAAAAAAAA#64
def v1 : BitVec 64 := 0xCCCCCCCCCCCCCCCC#64
def v2 : BitVec 64 := 0xF0F0F0F0F0F0F0F0#64
def v3 : BitVec 64 := 0xFF00FF00FF00FF00#64
def v4 : BitVec 64 := 0xFFFF0000FFFF0000#64
def v5 : BitVec 64 := 0xFFFFFFFF00000000#64

@[simp] theorem bitF2_allOnes_getElem (q : Fin 64) :
    bitF2 (0xFFFFFFFFFFFFFFFF#64)[q] = 1 := by
  fin_cases q <;> decide

@[simp] theorem bitF2_allOnes_getElemNat (i : Nat) (h : i < 64) :
    bitF2 (0xFFFFFFFFFFFFFFFF#64)[i] = 1 :=
  bitF2_allOnes_getElem ⟨i, h⟩

def e0 := v0 &&& v3
def e1 := (v0 &&& v4) ^^^ (v1 &&& v3)
def e2 := (v0 &&& v5) ^^^ (v1 &&& v4) ^^^ (v2 &&& v3)
def e3 := (v1 &&& v5) ^^^ (v2 &&& v4)
def e4 := v2 &&& v5

def tableVar : Fin 6 → BitVec 64 := ![v0, v1, v2, v3, v4, v5]
def targetTable : Fin 5 → BitVec 64 := ![e0, e1, e2, e3, e4]

def assignment (q : Fin 64) : Fin 6 → F₂ :=
  fun i ↦ bitF2 ((tableVar i).getLsb q)

theorem eval_Mul_three (i : Fin 5) (q : Fin 64) :
    eval (Mul 3 i) (assignment q) = bitF2 ((targetTable i).getLsb q) := by
  fin_cases i <;>
    simp [Mul, mulCoefficient, aVar, bVar, assignment, tableVar, targetTable,
      e0, e1, e2, e3, e4, Fin.sum_univ_succ]

def truthR (x : BitVec 10) : BitVec 64 :=
  sel (x.getLsbD 0) (BitVec.allOnes 64) ^^^
  sel (x.getLsbD 1) v0 ^^^ sel (x.getLsbD 2) v1 ^^^
  sel (x.getLsbD 3) v2 ^^^ sel (x.getLsbD 4) v3 ^^^
  sel (x.getLsbD 5) v4 ^^^ sel (x.getLsbD 6) v5 ^^^
  sel (x.getLsbD 7) e0 ^^^ sel (x.getLsbD 8) e4 ^^^
  sel (x.getLsbD 9) (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4)

def truthW (x : BitVec 12) : BitVec 64 :=
  sel (x.getLsbD 0) (BitVec.allOnes 64) ^^^
  sel (x.getLsbD 1) v0 ^^^ sel (x.getLsbD 2) v1 ^^^
  sel (x.getLsbD 3) v2 ^^^ sel (x.getLsbD 4) v3 ^^^
  sel (x.getLsbD 5) v4 ^^^ sel (x.getLsbD 6) v5 ^^^
  sel (x.getLsbD 7) e0 ^^^ sel (x.getLsbD 8) e1 ^^^
  sel (x.getLsbD 9) e2 ^^^ sel (x.getLsbD 10) e3 ^^^
  sel (x.getLsbD 11) e4

theorem rationalRep_truth (c : Fin 10 → F₂) (q : Fin 64) :
    eval (rationalRep c) (assignment q) =
      bitF2 ((truthR (coeffBits c)).getLsb q) := by
  simp [rationalRep, rationalBasis, targetSum, truthR, eval_Mul_three,
    assignment, tableVar, targetTable, e0, e1, e2, e3, e4,
    Fin.sum_univ_succ, coeffBits]
  ring

theorem ambientRep_truth (c : Fin 12 → F₂) (q : Fin 64) :
    eval (ambientRep c) (assignment q) =
      bitF2 ((truthW (coeffBits c)).getLsb q) := by
  simp [ambientRep, ambientBasis, truthW, eval_Mul_three,
    assignment, tableVar, targetTable, e0, e1, e2, e3, e4,
    Fin.sum_univ_succ, coeffBits]

end UnrestrictedBooleanMul
