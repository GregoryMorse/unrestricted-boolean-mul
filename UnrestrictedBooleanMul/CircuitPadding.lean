import UnrestrictedBooleanMul.N4.Flag

/-!
# Padding unrestricted circuits with redundant gates

An XOR--AND circuit with at most `r` multiplication gates can be viewed as
one with exactly `r` gates by adjoining zero products.  This small structural
lemma lets a no-`r` theorem imply a lower bound against every smaller size.
-/

namespace UnrestrictedBooleanMul

noncomputable section

def Circuit.padGate {m s r : Nat} (C : Circuit m s) (_h : s ≤ r) :
    Fin r → ANF m := fun i =>
  if hi : i.val < s then C.gate ⟨i.val, hi⟩ else 0

def Circuit.padLeft {m s r : Nat} (C : Circuit m s) (_h : s ≤ r) :
    Fin r → ANF m := fun i =>
  if hi : i.val < s then C.left ⟨i.val, hi⟩ else 0

def Circuit.padRight {m s r : Nat} (C : Circuit m s) (_h : s ≤ r) :
    Fin r → ANF m := fun i =>
  if hi : i.val < s then C.right ⟨i.val, hi⟩ else 0

theorem Circuit.wireSpace_le_padGate {m s r j : Nat}
    (C : Circuit m s) (h : s ≤ r) :
    wireSpace C.gate j ≤ wireSpace (C.padGate h) j := by
  apply sup_le le_sup_left
  apply le_sup_of_le_right
  apply Submodule.span_mono
  rintro p ⟨i, hij, rfl⟩
  let k : Fin r := ⟨i.val, i.isLt.trans_le h⟩
  refine ⟨k, hij, ?_⟩
  simp [Circuit.padGate, k, i.isLt]

/-- Pad a circuit on the right by zero-product gates. -/
def Circuit.pad {m s r : Nat} (C : Circuit m s) (h : s ≤ r) :
    Circuit m r where
  gate := C.padGate h
  left := C.padLeft h
  right := C.padRight h
  left_mem i := by
    by_cases hi : i.val < s
    · have hold : C.left ⟨i.val, hi⟩ ∈ wireSpace C.gate i.val :=
        C.left_mem ⟨i.val, hi⟩
      have hnew := C.wireSpace_le_padGate h hold
      simpa [Circuit.padLeft, hi] using hnew
    · simp [Circuit.padLeft, hi]
  right_mem i := by
    by_cases hi : i.val < s
    · have hold : C.right ⟨i.val, hi⟩ ∈ wireSpace C.gate i.val :=
        C.right_mem ⟨i.val, hi⟩
      have hnew := C.wireSpace_le_padGate h hold
      simpa [Circuit.padRight, hi] using hnew
    · simp [Circuit.padRight, hi]
  gate_eq i := by
    by_cases hi : i.val < s
    · simp [Circuit.padGate, Circuit.padLeft, Circuit.padRight, hi,
        C.gate_eq ⟨i.val, hi⟩]
    · simp [Circuit.padGate, Circuit.padLeft, Circuit.padRight, hi]

theorem Circuit.le_finalWire_pad {m s r : Nat}
    (C : Circuit m s) (h : s ≤ r) :
    C.finalWire ≤ (C.pad h).finalWire := by
  change wireSpace C.gate s ≤ wireSpace (C.padGate h) r
  exact (C.wireSpace_le_padGate h).trans (N4.wireSpace_mono h)

theorem Circuit.Computes.pad {m s r o : Nat} {C : Circuit m s}
    {target : Fin o → ANF m} (hC : C.Computes target) (h : s ≤ r) :
    (C.pad h).Computes target := by
  intro i
  exact C.le_finalWire_pad h (hC i)

theorem HasCircuit.pad {m s r o : Nat} {target : Fin o → ANF m}
    (hC : HasCircuit target s) (h : s ≤ r) : HasCircuit target r := by
  rcases hC with ⟨⟨C, hComputes⟩⟩
  exact ⟨⟨C.pad h, hComputes.pad h⟩⟩

end
end UnrestrictedBooleanMul
