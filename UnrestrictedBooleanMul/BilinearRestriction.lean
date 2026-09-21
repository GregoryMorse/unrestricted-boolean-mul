import UnrestrictedBooleanMul.Models

/-! Semantic input substitution and actual deletion of a vanished product.
These are tensor-formula operations, not assumptions about the dimensions
of a quotient or about an enumerated family of restrictions. -/
namespace UnrestrictedBooleanMul
noncomputable section

/-- Substitute old left coordinates by the columns of `L`. -/
def BilinearTensor.restrictLeft {a b c o : Nat} (T : BilinearTensor a b o)
    (L : Fin a → Fin c → F₂) : BilinearTensor c b o :=
  fun s u j => ∑ i, L i u * T s i j

def BilinearFormula.restrictLeft {a b c o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (L : Fin a → Fin c → F₂) :
    BilinearFormula (T.restrictLeft L) r where
  left k u := ∑ i, L i u * F.left k i
  right := F.right
  output := F.output
  correct s u j := by
    simp only [BilinearTensor.restrictLeft, F.correct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl

/-- Delete any term with identically zero left factor. The actual formula
has one fewer multiplication; this is stronger than a rank count alone. -/
def BilinearFormula.eraseZeroLeft {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T (r + 1)) (k : Fin (r + 1))
    (hk : ∀ i, F.left k i = 0) : BilinearFormula T r where
  left l := F.left (k.succAbove l)
  right l := F.right (k.succAbove l)
  output s l := F.output s (k.succAbove l)
  correct s i j := by
    rw [F.correct, Fin.sum_univ_succAbove _ k]
    simp only [hk i, mul_zero, zero_mul, zero_add]

def BilinearFormula.restrictLeftErase {a b c o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T (r + 1)) (L : Fin a → Fin c → F₂) (k : Fin (r + 1))
    (hk : ∀ u, ∑ i, L i u * F.left k i = 0) : BilinearFormula (T.restrictLeft L) r :=
  (F.restrictLeft L).eraseZeroLeft k hk

theorem bilinearRank_restrictLeft_le {a b c o : Nat} (T : BilinearTensor a b o)
    (L : Fin a → Fin c → F₂) : bilinearRank (T.restrictLeft L) ≤ bilinearRank T := by
  classical
  obtain ⟨F⟩ := Nat.find_spec T.hasFormula
  exact bilinearRank_le (F.restrictLeft L)

theorem bilinearRank_restrictLeft_le_of_killed_term {a b c o r : Nat}
    {T : BilinearTensor a b o} (F : BilinearFormula T (r + 1))
    (L : Fin a → Fin c → F₂) (k : Fin (r + 1))
    (hk : ∀ u, ∑ i, L i u * F.left k i = 0) : bilinearRank (T.restrictLeft L) ≤ r :=
  bilinearRank_le (F.restrictLeftErase L k hk)

/-- A lower bound for the restricted tensor translates to one extra
product in the original formula, provided a specific term is killed. -/
theorem restriction_lower_bound {a b c o r lower : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T (r + 1)) (L : Fin a → Fin c → F₂) (k : Fin (r + 1))
    (hk : ∀ u, ∑ i, L i u * F.left k i = 0)
    (hLower : lower ≤ bilinearRank (T.restrictLeft L)) : lower + 1 ≤ r + 1 := by
  exact Nat.add_le_add_right
    (hLower.trans (bilinearRank_restrictLeft_le_of_killed_term F L k hk)) 1

/-- Coordinates on the kernel of a binary row `h`, pivoting at a coordinate
where `h p = 1`. No canonical representative or orbit choice is assumed. -/
def leftHyperplaneMatrix {a : Nat} (h : Fin (a + 1) → F₂) (p : Fin (a + 1)) :
    Fin (a + 1) → Fin a → F₂ :=
  fun i u => if i = p then h (p.succAbove u) else if i = p.succAbove u then 1 else 0

theorem leftHyperplaneMatrix_kills {a : Nat} (h : Fin (a + 1) → F₂)
    (p : Fin (a + 1)) (hp : h p = 1) (u : Fin a) :
    ∑ i, leftHyperplaneMatrix h p i u * h i = 0 := by
  rw [Fin.sum_univ_succAbove _ p]
  simp [leftHyperplaneMatrix, hp, CharTwo.add_self_eq_zero]

def leftHyperplaneEmbed {a : Nat} (h : Fin (a + 1) → F₂) (p : Fin (a + 1))
    (x : Fin a → F₂) : Fin (a + 1) → F₂ :=
  fun i => ∑ u, leftHyperplaneMatrix h p i u * x u

@[simp] theorem leftHyperplaneEmbed_pivot {a : Nat} (h : Fin (a + 1) → F₂)
    (p : Fin (a + 1)) (x : Fin a → F₂) :
    leftHyperplaneEmbed h p x p = ∑ u, h (p.succAbove u) * x u := by
  simp [leftHyperplaneEmbed, leftHyperplaneMatrix]

@[simp] theorem leftHyperplaneEmbed_other {a : Nat} (h : Fin (a + 1) → F₂)
    (p : Fin (a + 1)) (x : Fin a → F₂) (u : Fin a) :
    leftHyperplaneEmbed h p x (p.succAbove u) = x u := by
  simp [leftHyperplaneEmbed, leftHyperplaneMatrix]

theorem leftHyperplaneEmbed_injective {a : Nat} (h : Fin (a + 1) → F₂)
    (p : Fin (a + 1)) : Function.Injective (leftHyperplaneEmbed h p) := by
  intro x y hxy
  funext u
  simpa only [leftHyperplaneEmbed_other] using congrFun hxy (p.succAbove u)

/-- The substitution parametrizes the whole hyperplane, not merely a
smaller subspace on which the selected factor happens to vanish. -/
theorem leftHyperplaneEmbed_range {a : Nat} (h : Fin (a + 1) → F₂)
    (p : Fin (a + 1)) (hp : h p = 1) :
    Set.range (leftHyperplaneEmbed h p) = {x | ∑ i, h i * x i = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (∑ i, h i * leftHyperplaneEmbed h p y i) = 0
    rw [Fin.sum_univ_succAbove _ p]
    simp [hp, CharTwo.add_self_eq_zero]
  · intro hx
    refine ⟨fun u => x (p.succAbove u), ?_⟩
    funext i
    by_cases hi : i = p
    · subst i
      change (∑ i, h i * x i) = 0 at hx
      rw [Fin.sum_univ_succAbove _ p, hp, one_mul] at hx
      simpa only [leftHyperplaneEmbed_pivot] using (CharTwo.add_eq_zero.mp hx).symm
    · obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq hi
      exact leftHyperplaneEmbed_other h p _ u

theorem BilinearFormula.exists_left_pivot {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (hT : T ≠ 0) : ∃ k p, F.left k p = 1 := by
  classical
  by_contra hn
  push Not at hn
  have hz : ∀ k p, F.left k p = 0 := fun k p =>
    (f2_eq_zero_or_one (F.left k p)).resolve_right (hn k p)
  apply hT
  funext s i j
  simp [F.correct, hz]

theorem BilinearFormula.size_lower_bound_of_hyperplanes {a b o r lower : Nat}
    {T : BilinearTensor (a + 1) b o} (F : BilinearFormula T r) (hT : T ≠ 0)
    (hLower : ∀ (h : Fin (a + 1) → F₂) (p : Fin (a + 1)), h p = 1 →
      lower ≤ bilinearRank (T.restrictLeft (leftHyperplaneMatrix h p))) :
    lower + 1 ≤ r := by
  obtain ⟨k, p, hp⟩ := F.exists_left_pivot hT
  cases r with
  | zero => exact Fin.elim0 k
  | succ r =>
    exact restriction_lower_bound F (leftHyperplaneMatrix (F.left k) p) k
      (leftHyperplaneMatrix_kills (F.left k) p hp) (hLower (F.left k) p hp)

/-- The full substitution front end: lower bounds for *all* binary left
hyperplanes imply one extra product for every nonzero tensor. The remaining
hyperplane lower bounds are explicit hypotheses, never table axioms. -/
theorem bilinearRank_lower_bound_of_hyperplanes {a b o lower : Nat}
    (T : BilinearTensor (a + 1) b o) (hT : T ≠ 0)
    (hLower : ∀ (h : Fin (a + 1) → F₂) (p : Fin (a + 1)), h p = 1 →
      lower ≤ bilinearRank (T.restrictLeft (leftHyperplaneMatrix h p))) :
    lower + 1 ≤ bilinearRank T := by
  classical
  obtain ⟨F⟩ := Nat.find_spec T.hasFormula
  exact F.size_lower_bound_of_hyperplanes hT hLower

theorem polynomialTensor_ne_zero (a b : Nat) : polynomialTensor (a + 1) (b + 1) ≠ 0 := by
  intro hz
  have hentry := congrFun (congrFun (congrFun hz ⟨0, by omega⟩) 0) 0
  simpa [polynomialTensor] using hentry

/-- The square n=6 lower-bound interface, with every restriction lower
bound still visible. This declaration does not discharge the capacity sectors. -/
theorem n6_square_lower_bound_of_hyperplanes
    (hLower : ∀ (h : Fin 6 → F₂) (p : Fin 6), h p = 1 →
      16 ≤ bilinearRank ((polynomialTensor 6 6).restrictLeft (leftHyperplaneMatrix h p))) :
    17 ≤ bilinearRank (polynomialTensor 6 6) :=
  bilinearRank_lower_bound_of_hyperplanes _ (polynomialTensor_ne_zero 5 5) hLower

/-- Restriction respects a literal factorization of input-coordinate maps. -/
theorem BilinearTensor.restrictLeft_factorization {a b c d o : Nat}
    (T : BilinearTensor a b o) (L : Fin a → Fin c → F₂)
    (M : Fin a → Fin d → F₂) (N : Fin d → Fin c → F₂)
    (hL : ∀ i v, L i v = ∑ u, M i u * N u v) :
    (T.restrictLeft M).restrictLeft N = T.restrictLeft L := by
  funext s v j
  simp only [BilinearTensor.restrictLeft, hL, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u _
  ac_rfl

theorem leftHyperplaneEmbed_reconstruct {a : Nat} (h : Fin (a + 1) → F₂)
    (p : Fin (a + 1)) (hp : h p = 1) (x : Fin (a + 1) → F₂)
    (hx : ∑ i, h i * x i = 0) :
    leftHyperplaneEmbed h p (fun u => x (p.succAbove u)) = x := by
  have hmem : x ∈ Set.range (leftHyperplaneEmbed h p) := by
    rw [leftHyperplaneEmbed_range h p hp]
    exact hx
  obtain ⟨y, rfl⟩ := hmem
  simp only [leftHyperplaneEmbed_other]

theorem leftHyperplaneMatrix_factorization {a : Nat} (h : Fin (a + 1) → F₂)
    (p q : Fin (a + 1)) (hp : h p = 1) (hq : h q = 1) (i : Fin (a + 1)) (v : Fin a) :
    leftHyperplaneMatrix h p i v =
      ∑ u, leftHyperplaneMatrix h q i u * leftHyperplaneMatrix h p (q.succAbove u) v := by
  have hx : ∑ i, h i * leftHyperplaneMatrix h p i v = 0 := by
    simpa only [mul_comm] using leftHyperplaneMatrix_kills h p hp v
  exact (congrFun (leftHyperplaneEmbed_reconstruct h q hq
    (fun i => leftHyperplaneMatrix h p i v) hx) i).symm

/-- A hyperplane's restricted rank does not depend on the chosen nonzero
pivot. This is proved by two formula transports, not by orbit enumeration. -/
theorem bilinearRank_hyperplane_pivot_eq {a b o : Nat}
    (T : BilinearTensor (a + 1) b o) (h : Fin (a + 1) → F₂)
    (p q : Fin (a + 1)) (hp : h p = 1) (hq : h q = 1) :
    bilinearRank (T.restrictLeft (leftHyperplaneMatrix h p)) =
      bilinearRank (T.restrictLeft (leftHyperplaneMatrix h q)) := by
  have hle : ∀ p q, h p = 1 → h q = 1 →
      bilinearRank (T.restrictLeft (leftHyperplaneMatrix h p)) ≤
        bilinearRank (T.restrictLeft (leftHyperplaneMatrix h q)) := by
    intro p q hp hq
    rw [← T.restrictLeft_factorization _ _ _ (leftHyperplaneMatrix_factorization h p q hp hq)]
    exact bilinearRank_restrictLeft_le _ _
  exact Nat.le_antisymm (hle p q hp hq) (hle q p hq hp)

/-- Only one parametrization per nonzero hyperplane needs a lower bound;
no pivot compatibility with the arbitrary completing formula is required. -/
theorem bilinearRank_lower_bound_of_hyperplane_family {a b o lower : Nat}
    (T : BilinearTensor (a + 1) b o) (hT : T ≠ 0)
    (hLower : ∀ h : Fin (a + 1) → F₂, h ≠ 0 → ∃ p, h p = 1 ∧
      lower ≤ bilinearRank (T.restrictLeft (leftHyperplaneMatrix h p))) :
    lower + 1 ≤ bilinearRank T := by
  apply bilinearRank_lower_bound_of_hyperplanes T hT
  intro h p hp
  have hh : h ≠ 0 := by
    intro hz
    have hp' := hp
    simp [hz] at hp'
  obtain ⟨q, hq, hl⟩ := hLower h hh
  rw [bilinearRank_hyperplane_pivot_eq T h p q hp hq]
  exact hl

#check BilinearFormula.restrictLeft
#check BilinearFormula.eraseZeroLeft
#check BilinearFormula.restrictLeftErase
#check bilinearRank_restrictLeft_le
#check bilinearRank_restrictLeft_le_of_killed_term
#check restriction_lower_bound
#print axioms BilinearFormula.restrictLeft
#print axioms BilinearFormula.eraseZeroLeft
#print axioms BilinearFormula.restrictLeftErase
#print axioms bilinearRank_restrictLeft_le
#print axioms bilinearRank_restrictLeft_le_of_killed_term
#print axioms restriction_lower_bound
#check leftHyperplaneMatrix_kills
#check leftHyperplaneEmbed_pivot
#check leftHyperplaneEmbed_other
#check leftHyperplaneEmbed_injective
#check leftHyperplaneEmbed_range
#check BilinearFormula.exists_left_pivot
#check BilinearFormula.size_lower_bound_of_hyperplanes
#check bilinearRank_lower_bound_of_hyperplanes
#print axioms leftHyperplaneMatrix_kills
#print axioms leftHyperplaneEmbed_pivot
#print axioms leftHyperplaneEmbed_other
#print axioms leftHyperplaneEmbed_injective
#print axioms leftHyperplaneEmbed_range
#print axioms BilinearFormula.exists_left_pivot
#print axioms BilinearFormula.size_lower_bound_of_hyperplanes
#print axioms bilinearRank_lower_bound_of_hyperplanes
#check polynomialTensor_ne_zero
#check n6_square_lower_bound_of_hyperplanes
#print axioms polynomialTensor_ne_zero
#print axioms n6_square_lower_bound_of_hyperplanes
#check BilinearTensor.restrictLeft_factorization
#check leftHyperplaneEmbed_reconstruct
#check leftHyperplaneMatrix_factorization
#check bilinearRank_hyperplane_pivot_eq
#check bilinearRank_lower_bound_of_hyperplane_family
#print axioms BilinearTensor.restrictLeft_factorization
#print axioms leftHyperplaneEmbed_reconstruct
#print axioms leftHyperplaneMatrix_factorization
#print axioms bilinearRank_hyperplane_pivot_eq
#print axioms bilinearRank_lower_bound_of_hyperplane_family
end
end UnrestrictedBooleanMul
