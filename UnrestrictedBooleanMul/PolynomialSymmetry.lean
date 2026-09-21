import UnrestrictedBooleanMul.BilinearSymmetry
import Mathlib.Data.Nat.Choose.Basic

/-! Translation and reversal as actual n=6 tensor symmetries. The finite
identities concern small coefficient matrices, not circuits or capacity
exclusions. Ordinary kernel reduction is used, never native evaluation. -/
namespace UnrestrictedBooleanMul.N6.Symmetry

def pascal (n : Nat) (i j : Fin n) : F₂ := (Nat.choose j.val i.val : F₂)
def reverseMatrix (n : Nat) (i j : Fin n) : F₂ := if i.val + j.val + 1 = n then 1 else 0

set_option maxRecDepth 4096 in
theorem pascal_six_squared : ∀ i j : Fin 6,
    ∑ k, pascal 6 i k * pascal 6 k j = if i = j then 1 else 0 := by decide

set_option maxRecDepth 4096 in
theorem pascal_eleven_squared : ∀ s t : Fin 11,
    ∑ u, pascal 11 s u * pascal 11 u t = if s = t then 1 else 0 := by decide

set_option maxRecDepth 4096 in
theorem reverse_six_squared : ∀ i j : Fin 6,
    ∑ k, reverseMatrix 6 i k * reverseMatrix 6 k j = if i = j then 1 else 0 := by decide

set_option maxRecDepth 4096 in
theorem reverse_eleven_squared : ∀ s t : Fin 11,
    ∑ u, reverseMatrix 11 s u * reverseMatrix 11 u t = if s = t then 1 else 0 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem translation_covariance_coeff : ∀ (s : Fin 11) (i j : Fin 6),
    (∑ v, pascal 6 v j * (∑ u, pascal 6 u i * polynomialTensor 6 6 s u v)) =
      ∑ t, pascal 11 s t * polynomialTensor 6 6 t i j := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem reversal_covariance_coeff : ∀ (s : Fin 11) (i j : Fin 6),
    (∑ v, reverseMatrix 6 v j * (∑ u, reverseMatrix 6 u i * polynomialTensor 6 6 s u v)) =
      ∑ t, reverseMatrix 11 s t * polynomialTensor 6 6 t i j := by decide

def translation : TensorInvolution (polynomialTensor 6 6) where
  left := pascal 6
  right := pascal 6
  output := pascal 11
  left_sq := pascal_six_squared
  output_sq := pascal_eleven_squared
  covariance := by
    funext s i j
    exact translation_covariance_coeff s i j

def reversal : TensorInvolution (polynomialTensor 6 6) where
  left := reverseMatrix 6
  right := reverseMatrix 6
  output := reverseMatrix 11
  left_sq := reverse_six_squared
  output_sq := reverse_eleven_squared
  covariance := by
    funext s i j
    exact reversal_covariance_coeff s i j

#check pascal_six_squared
#check pascal_eleven_squared
#check reverse_six_squared
#check reverse_eleven_squared
#check translation_covariance_coeff
#check reversal_covariance_coeff
#check translation
#check reversal
#print axioms pascal_six_squared
#print axioms pascal_eleven_squared
#print axioms reverse_six_squared
#print axioms reverse_eleven_squared
#print axioms translation_covariance_coeff
#print axioms reversal_covariance_coeff
#print axioms translation
#print axioms reversal
end UnrestrictedBooleanMul.N6.Symmetry
