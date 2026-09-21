import UnrestrictedBooleanMul.BilinearRestriction
import UnrestrictedBooleanMul.BilinearOutput

/-! Tensor symmetries transport hyperplane restrictions in the actual
bilinear formula model. No orbit catalogue is part of this argument. -/
namespace UnrestrictedBooleanMul
noncomputable section

def BilinearTensor.restrictRight {a b d o : Nat} (T : BilinearTensor a b o)
    (R : Fin b → Fin d → F₂) : BilinearTensor a d o :=
  fun s i v => ∑ j, R j v * T s i j

def BilinearFormula.restrictRight {a b d o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (R : Fin b → Fin d → F₂) :
    BilinearFormula (T.restrictRight R) r where
  left := F.left
  right k v := ∑ j, R j v * F.right k j
  output := F.output
  correct s i v := by
    simp only [BilinearTensor.restrictRight, F.correct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl

theorem bilinearRank_restrictRight_le {a b d o : Nat} (T : BilinearTensor a b o)
    (R : Fin b → Fin d → F₂) : bilinearRank (T.restrictRight R) ≤ bilinearRank T := by
  classical
  obtain ⟨F⟩ := Nat.find_spec T.hasFormula
  exact bilinearRank_le (F.restrictRight R)

theorem BilinearTensor.restrictRight_left {a b c d o : Nat} (T : BilinearTensor a b o)
    (L : Fin a → Fin c → F₂) (R : Fin b → Fin d → F₂) :
    (T.restrictLeft L).restrictRight R = (T.restrictRight R).restrictLeft L := by
  funext s u v
  simp only [restrictLeft, restrictRight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem BilinearTensor.mapOutputs_left {a b c o o' : Nat} (T : BilinearTensor a b o)
    (L : Fin a → Fin c → F₂) (C : Fin o' → Fin o → F₂) :
    (T.restrictLeft L).mapOutputs C = (T.mapOutputs C).restrictLeft L := by
  funext s u j
  simp only [restrictLeft, mapOutputs, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro t _
  ac_rfl

theorem BilinearTensor.mapOutputs_involution {a b o : Nat} (T : BilinearTensor a b o)
    (C : Fin o → Fin o → F₂)
    (hC : ∀ s t, ∑ u, C s u * C u t = if s = t then 1 else 0) :
    (T.mapOutputs C).mapOutputs C = T := by
  classical
  funext s i j
  simp only [mapOutputs, Finset.mul_sum]
  simp_rw [← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hC]
  simp

/-- A left involution, with compensating right and output changes.
Only the identities used by the rank transport are required. -/
structure TensorInvolution {a b o : Nat} (T : BilinearTensor (a + 1) b o) where
  left : Fin (a + 1) → Fin (a + 1) → F₂
  right : Fin b → Fin b → F₂
  output : Fin o → Fin o → F₂
  left_sq : ∀ i j, ∑ k, left i k * left k j = if i = j then 1 else 0
  output_sq : ∀ s t, ∑ u, output s u * output u t = if s = t then 1 else 0
  covariance : (T.restrictLeft left).restrictRight right = T.mapOutputs output

namespace TensorInvolution
variable {a b o : Nat} {T : BilinearTensor (a + 1) b o}

def normal (S : TensorInvolution T) (h : Fin (a + 1) → F₂) : Fin (a + 1) → F₂ :=
  fun j => ∑ i, h i * S.left i j

theorem normal_zero (S : TensorInvolution T) : S.normal 0 = 0 := by
  funext j
  simp [normal]

theorem normal_involution (S : TensorInvolution T) (h : Fin (a + 1) → F₂) :
    S.normal (S.normal h) = h := by
  classical
  funext j
  simp only [normal, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, S.left_sq]
  simp

theorem normal_ne_zero (S : TensorInvolution T) {h : Fin (a + 1) → F₂} (hh : h ≠ 0) :
    S.normal h ≠ 0 := by
  intro hz
  have he := S.normal_involution h
  rw [hz, S.normal_zero] at he
  exact hh he.symm

theorem tensor_recover (S : TensorInvolution T) :
    ((T.restrictLeft S.left).restrictRight S.right).mapOutputs S.output = T := by
  rw [S.covariance, T.mapOutputs_involution S.output S.output_sq]

/-- Coordinates of the left symmetry between two hyperplane bases. -/
def hyperplaneChange (S : TensorInvolution T) (h : Fin (a + 1) → F₂)
    (p q : Fin (a + 1)) : Fin a → Fin a → F₂ :=
  fun u v => ∑ k, S.left (p.succAbove u) k * leftHyperplaneMatrix (S.normal h) q k v

theorem hyperplane_factorization (S : TensorInvolution T) (h : Fin (a + 1) → F₂)
    (p q : Fin (a + 1)) (hp : h p = 1) (hq : S.normal h q = 1)
    (i : Fin (a + 1)) (v : Fin a) :
    (∑ k, S.left i k * leftHyperplaneMatrix (S.normal h) q k v) =
      ∑ u, leftHyperplaneMatrix h p i u * S.hyperplaneChange h p q u v := by
  let x : Fin (a + 1) → F₂ :=
    fun i => ∑ k, S.left i k * leftHyperplaneMatrix (S.normal h) q k v
  have hx : ∑ i, h i * x i = 0 := by
    simp only [x, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ k, S.normal h k * leftHyperplaneMatrix (S.normal h) q k v) = 0
    simpa only [mul_comm] using leftHyperplaneMatrix_kills (S.normal h) q hq v
  exact (congrFun (leftHyperplaneEmbed_reconstruct h p hp x hx) i).symm

theorem hyperplane_transport (S : TensorInvolution T) (h : Fin (a + 1) → F₂)
    (p q : Fin (a + 1)) (hp : h p = 1) (hq : S.normal h q = 1) :
    (((T.restrictLeft (leftHyperplaneMatrix h p)).restrictLeft (S.hyperplaneChange h p q)).restrictRight
      S.right).mapOutputs S.output =
      T.restrictLeft (leftHyperplaneMatrix (S.normal h) q) := by
  let L := fun i v => ∑ k, S.left i k * leftHyperplaneMatrix (S.normal h) q k v
  have h1 := T.restrictLeft_factorization L S.left (leftHyperplaneMatrix (S.normal h) q)
    (fun _ _ => rfl)
  have h2 := T.restrictLeft_factorization L (leftHyperplaneMatrix h p) (S.hyperplaneChange h p q)
    (S.hyperplane_factorization h p q hp hq)
  rw [h2, ← h1, BilinearTensor.restrictRight_left, BilinearTensor.mapOutputs_left,
    S.tensor_recover]

theorem hyperplane_rank_le (S : TensorInvolution T) (h : Fin (a + 1) → F₂)
    (p q : Fin (a + 1)) (hp : h p = 1) (hq : S.normal h q = 1) :
    bilinearRank (T.restrictLeft (leftHyperplaneMatrix (S.normal h) q)) ≤
      bilinearRank (T.restrictLeft (leftHyperplaneMatrix h p)) := by
  rw [← S.hyperplane_transport h p q hp hq]
  exact (bilinearRank_mapOutputs_le _ _).trans
    ((bilinearRank_restrictRight_le _ _).trans (bilinearRank_restrictLeft_le _ _))

theorem hyperplane_rank_eq (S : TensorInvolution T) (h : Fin (a + 1) → F₂)
    (p q : Fin (a + 1)) (hp : h p = 1) (hq : S.normal h q = 1) :
    bilinearRank (T.restrictLeft (leftHyperplaneMatrix (S.normal h) q)) =
      bilinearRank (T.restrictLeft (leftHyperplaneMatrix h p)) := by
  apply Nat.le_antisymm (S.hyperplane_rank_le h p q hp hq)
  have hp' : S.normal (S.normal h) p = 1 := by simpa only [S.normal_involution] using hp
  simpa only [S.normal_involution] using S.hyperplane_rank_le (S.normal h) q p hq hp'

end TensorInvolution

#check BilinearFormula.restrictRight
#check bilinearRank_restrictRight_le
#check BilinearTensor.restrictRight_left
#check BilinearTensor.mapOutputs_left
#check BilinearTensor.mapOutputs_involution
#check TensorInvolution.normal_zero
#check TensorInvolution.normal_involution
#check TensorInvolution.normal_ne_zero
#check TensorInvolution.tensor_recover
#check TensorInvolution.hyperplane_factorization
#check TensorInvolution.hyperplane_transport
#check TensorInvolution.hyperplane_rank_le
#check TensorInvolution.hyperplane_rank_eq
#print axioms BilinearFormula.restrictRight
#print axioms bilinearRank_restrictRight_le
#print axioms BilinearTensor.restrictRight_left
#print axioms BilinearTensor.mapOutputs_left
#print axioms BilinearTensor.mapOutputs_involution
#print axioms TensorInvolution.normal_zero
#print axioms TensorInvolution.normal_involution
#print axioms TensorInvolution.normal_ne_zero
#print axioms TensorInvolution.tensor_recover
#print axioms TensorInvolution.hyperplane_factorization
#print axioms TensorInvolution.hyperplane_transport
#print axioms TensorInvolution.hyperplane_rank_le
#print axioms TensorInvolution.hyperplane_rank_eq
end
end UnrestrictedBooleanMul
