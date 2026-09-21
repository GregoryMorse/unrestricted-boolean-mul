import UnrestrictedBooleanMul.Models

/-! Output recombination and zero-coordinate padding preserve the intended
bilinear formula semantics. These operations do not change either input block. -/
namespace UnrestrictedBooleanMul
noncomputable section

def BilinearTensor.mapOutputs {a b o o' : Nat} (T : BilinearTensor a b o)
    (C : Fin o' → Fin o → F₂) : BilinearTensor a b o' :=
  fun s i j => ∑ t, C s t * T t i j

def BilinearFormula.mapOutputs {a b o o' r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (C : Fin o' → Fin o → F₂) :
    BilinearFormula (T.mapOutputs C) r where
  left := F.left
  right := F.right
  output s k := ∑ t, C s t * F.output t k
  correct s i j := by
    simp only [BilinearTensor.mapOutputs, F.correct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro t _
    ac_rfl

theorem bilinearRank_mapOutputs_le {a b o o' : Nat} (T : BilinearTensor a b o)
    (C : Fin o' → Fin o → F₂) : bilinearRank (T.mapOutputs C) ≤ bilinearRank T := by
  classical
  obtain ⟨F⟩ := Nat.find_spec T.hasFormula
  exact bilinearRank_le (F.mapOutputs C)

def BilinearTensor.selectOutputs {a b o o' : Nat} (T : BilinearTensor a b o)
    (f : Fin o' → Fin o) : BilinearTensor a b o' := fun s => T (f s)

def BilinearFormula.selectOutputs {a b o o' r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (f : Fin o' → Fin o) :
    BilinearFormula (T.selectOutputs f) r where
  left := F.left
  right := F.right
  output s := F.output (f s)
  correct s := F.correct (f s)

theorem bilinearRank_selectOutputs_le {a b o o' : Nat} (T : BilinearTensor a b o)
    (f : Fin o' → Fin o) : bilinearRank (T.selectOutputs f) ≤ bilinearRank T := by
  classical
  obtain ⟨F⟩ := Nat.find_spec T.hasFormula
  exact bilinearRank_le (F.selectOutputs f)

/-- Insert an identically zero first output, retaining every old output. -/
def BilinearTensor.prependZero {a b o : Nat} (T : BilinearTensor a b o) :
    BilinearTensor a b (o + 1) := Fin.cases (fun _ _ => 0) T

def BilinearFormula.prependZero {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) : BilinearFormula T.prependZero r where
  left := F.left
  right := F.right
  output := Fin.cases (fun _ => 0) F.output
  correct := by
    intro s
    refine Fin.cases ?_ (fun t => ?_) s
    · intro i j
      simp [BilinearTensor.prependZero]
    · exact F.correct t

theorem BilinearTensor.prependZero_select_succ {a b o : Nat} (T : BilinearTensor a b o) :
    T.prependZero.selectOutputs Fin.succ = T := by
  funext s i j
  rfl

theorem bilinearRank_prependZero {a b o : Nat} (T : BilinearTensor a b o) :
    bilinearRank T.prependZero = bilinearRank T := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨F⟩ := Nat.find_spec T.hasFormula
    exact bilinearRank_le F.prependZero
  · simpa only [T.prependZero_select_succ] using
      bilinearRank_selectOutputs_le T.prependZero Fin.succ

#check BilinearFormula.mapOutputs
#check bilinearRank_mapOutputs_le
#check BilinearFormula.selectOutputs
#check bilinearRank_selectOutputs_le
#check BilinearFormula.prependZero
#check BilinearTensor.prependZero_select_succ
#check bilinearRank_prependZero
#print axioms BilinearFormula.mapOutputs
#print axioms bilinearRank_mapOutputs_le
#print axioms BilinearFormula.selectOutputs
#print axioms bilinearRank_selectOutputs_le
#print axioms BilinearFormula.prependZero
#print axioms BilinearTensor.prependZero_select_succ
#print axioms bilinearRank_prependZero
end
end UnrestrictedBooleanMul
