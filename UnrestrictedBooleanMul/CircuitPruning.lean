import UnrestrictedBooleanMul.CircuitPadding

/-!
# Removing redundant gates

A gate already in its preceding wire space can be deleted: every later factor
still lies in the span of the remaining earlier gates.  This gives a genuinely
nonredundant minimum-size circuit and makes the target/defect ledger exact.
-/

namespace UnrestrictedBooleanMul

noncomputable section

/-- The gate list obtained by deleting position `k`. -/
def Circuit.eraseGateFn {m n : Nat} (C : Circuit m (n + 1))
    (k : Fin (n + 1)) : Fin n → ANF m :=
  fun i => C.gate (k.succAbove i)

private theorem Circuit.oldPrefix_le_erasedPrefix {m n : Nat}
    (C : Circuit m (n + 1)) (k : Fin (n + 1))
    (hk : C.gate k ∈ wireSpace C.gate k.val) (i : Fin n) :
    wireSpace C.gate (k.succAbove i).val ≤
      wireSpace (C.eraseGateFn k) i.val := by
  have mapEarlier {l : Fin (n + 1)} (hlk : l ≠ k)
      (hli : l < k.succAbove i) :
      C.gate l ∈ wireSpace (C.eraseGateFn k) i.val := by
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hlk
    apply Submodule.mem_sup_right
    apply Submodule.subset_span
    refine ⟨a, ?_, ?_⟩
    · apply (Fin.succAbove_lt_succAbove_iff).mp
      have hmaps : k.succAbove a < k.succAbove i := by
        rw [ha]
        exact hli
      exact hmaps
    · simp only [Circuit.eraseGateFn]
      rw [ha]
  apply sup_le le_sup_left
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hli, rfl⟩
  by_cases hlk : l = k
  · subst l
    apply (show wireSpace C.gate k.val ≤
        wireSpace (C.eraseGateFn k) i.val by
      apply sup_le le_sup_left
      apply Submodule.span_le.mpr
      rintro _ ⟨l, hlk, rfl⟩
      exact mapEarlier (Fin.ne_of_lt hlk) (hlk.trans hli))
    exact hk
  · exact mapEarlier hlk hli

/-- Delete a redundant gate and keep all later gate polynomials unchanged. -/
def Circuit.eraseGate {m n : Nat} (C : Circuit m (n + 1))
    (k : Fin (n + 1)) (hk : C.gate k ∈ wireSpace C.gate k.val) :
    Circuit m n where
  gate := C.eraseGateFn k
  left i := C.left (k.succAbove i)
  right i := C.right (k.succAbove i)
  left_mem i := C.oldPrefix_le_erasedPrefix k hk i (C.left_mem (k.succAbove i))
  right_mem i := C.oldPrefix_le_erasedPrefix k hk i (C.right_mem (k.succAbove i))
  gate_eq i := C.gate_eq (k.succAbove i)

/-- Deleting a redundant gate preserves every wire in the original final
space, not merely the designated outputs. -/
theorem Circuit.finalWire_le_eraseGate {m n : Nat}
    (C : Circuit m (n + 1)) (k : Fin (n + 1))
    (hk : C.gate k ∈ wireSpace C.gate k.val) :
    C.finalWire ≤ (C.eraseGate k hk).finalWire := by
  have mapOther {l : Fin (n + 1)} (hlk : l ≠ k) :
      C.gate l ∈ (C.eraseGate k hk).finalWire := by
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hlk
    apply Submodule.mem_sup_right
    apply Submodule.subset_span
    refine ⟨a, a.isLt, ?_⟩
    simp only [Circuit.eraseGate, Circuit.eraseGateFn]
    rw [ha]
  have hprefix : wireSpace C.gate k.val ≤
      (C.eraseGate k hk).finalWire := by
    apply sup_le
    · exact affine_le_wireSpace (C.eraseGate k hk).gate
    · apply Submodule.span_le.mpr
      rintro _ ⟨l, hlk, rfl⟩
      exact mapOther (Fin.ne_of_lt hlk)
  rw [C.finalWire_eq]
  apply sup_le
  · exact affine_le_wireSpace (C.eraseGate k hk).gate
  · apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    by_cases hlk : l = k
    · subst l
      exact hprefix hk
    · exact mapOther hlk

/-- Deleting a redundant gate preserves computation of every target. -/
theorem Circuit.Computes.eraseGate {m n o : Nat}
    {C : Circuit m (n + 1)} {target : Fin o → ANF m}
    (hC : C.Computes target) (k : Fin (n + 1))
    (hk : C.gate k ∈ wireSpace C.gate k.val) :
    (C.eraseGate k hk).Computes target := by
  intro i
  exact C.finalWire_le_eraseGate k hk (hC i)

/-- Every gate of a gate-minimal circuit is nonredundant. -/
theorem Circuit.Computes.all_nonredundant_of_minimal {m r o : Nat}
    {C : Circuit m r} {target : Fin o → ANF m}
    (hC : C.Computes target)
    (hmin : ∀ s, HasCircuit target s → r ≤ s) :
    ∀ i : Fin r, N4.NonredundantAt C i := by
  cases r with
  | zero => exact fun i => Fin.elim0 i
  | succ n =>
      intro i hred
      have hsmall : HasCircuit target n :=
        ⟨⟨C.eraseGate i hred, hC.eraseGate i hred⟩⟩
      have := hmin n hsmall
      omega

/-- A computable target has a minimum-size semantic circuit all of whose gates
are nonredundant. -/
theorem exists_minimalCircuit_all_nonredundant {m o R : Nat}
    {target : Fin o → ANF m} (hupper : HasCircuit target R) :
    ∃ r, ∃ C : Circuit m r, C.Computes target ∧
      (∀ i : Fin r, N4.NonredundantAt C i) ∧
      (∀ s, HasCircuit target s → r ≤ s) := by
  classical
  let hex : ∃ r, HasCircuit target r := ⟨R, hupper⟩
  let r := Nat.find hex
  have hr : HasCircuit target r := Nat.find_spec hex
  rcases hr with ⟨⟨C, hC⟩⟩
  have hmin : ∀ s, HasCircuit target s → r ≤ s := by
    intro s hs
    exact Nat.find_min' hex hs
  exact ⟨r, C, hC, hC.all_nonredundant_of_minimal hmin, hmin⟩

end
end UnrestrictedBooleanMul
