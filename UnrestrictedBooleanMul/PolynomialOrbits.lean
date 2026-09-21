import UnrestrictedBooleanMul.PolynomialSymmetry
import UnrestrictedBooleanMul.PolynomialEndpoint
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Complete fifteen-representative rank coverage for n=6. Finite witnesses
select words in proved tensor symmetries; their coverage is kernel-checked.
No numerical rank lower bound is inferred from coverage alone. -/
namespace UnrestrictedBooleanMul.N6.Orbits
noncomputable section
open Symmetry

abbrev Normal := Fin 6 → F₂

theorem nonzero_has_one (h : Normal) (hh : h ≠ 0) : ∃ p, h p = 1 := by
  by_contra hn
  apply hh
  funext i
  rcases f2_eq_zero_or_one (h i) with hz | ho
  · exact hz
  · exact (hn ⟨i, ho⟩).elim

def pivot (h : Normal) : Fin 6 := by
  classical
  exact if hp : ∃ p, h p = 1 then hp.choose else 0

theorem pivot_one (h : Normal) (hh : h ≠ 0) : h (pivot h) = 1 := by
  classical
  have hp := nonzero_has_one h hh
  simp only [pivot, dif_pos hp]
  exact hp.choose_spec

def restrictedRank (h : Normal) : Nat :=
  bilinearRank ((polynomialTensor 6 6).restrictLeft (leftHyperplaneMatrix h (pivot h)))

theorem restrictedRank_pivot (h : Normal) (p : Fin 6) (hp : h p = 1) :
    restrictedRank h = bilinearRank ((polynomialTensor 6 6).restrictLeft (leftHyperplaneMatrix h p)) := by
  have hh : h ≠ 0 := by intro hz; simp [hz] at hp
  exact bilinearRank_hyperplane_pivot_eq _ h (pivot h) p (pivot_one h hh) hp

theorem involution_rank (S : TensorInvolution (polynomialTensor 6 6)) (h : Normal) (hh : h ≠ 0) :
    restrictedRank (S.normal h) = restrictedRank h :=
  S.hyperplane_rank_eq h (pivot h) (pivot (S.normal h)) (pivot_one h hh)
    (pivot_one (S.normal h) (S.normal_ne_zero hh))

def wordAction (g : Fin 6) (h : Normal) : Normal :=
  match g.val with
  | 0 => h
  | 1 => translation.normal h
  | 2 => reversal.normal h
  | 3 => translation.normal (reversal.normal h)
  | 4 => reversal.normal (translation.normal h)
  | _ => translation.normal (reversal.normal (translation.normal h))

theorem wordAction_ne_zero (g : Fin 6) (h : Normal) (hh : h ≠ 0) : wordAction g h ≠ 0 := by
  fin_cases g <;> simp only [wordAction]
  · exact hh
  · exact translation.normal_ne_zero hh
  · exact reversal.normal_ne_zero hh
  · exact translation.normal_ne_zero (reversal.normal_ne_zero hh)
  · exact reversal.normal_ne_zero (translation.normal_ne_zero hh)
  · exact translation.normal_ne_zero (reversal.normal_ne_zero (translation.normal_ne_zero hh))

theorem wordAction_rank (g : Fin 6) (h : Normal) (hh : h ≠ 0) :
    restrictedRank (wordAction g h) = restrictedRank h := by
  have ht := translation.normal_ne_zero hh
  have hr := reversal.normal_ne_zero hh
  have hrt := reversal.normal_ne_zero ht
  fin_cases g <;> simp only [wordAction]
  · exact involution_rank translation h hh
  · exact involution_rank reversal h hh
  · rw [involution_rank translation _ hr, involution_rank reversal _ hh]
  · rw [involution_rank reversal _ ht, involution_rank translation _ hh]
  · rw [involution_rank translation _ hrt, involution_rank reversal _ ht, involution_rank translation _ hh]

def decode (w : Fin 64) : Normal := fun i => if w.val.testBit i.val then 1 else 0

def encode (h : Normal) : Fin 64 := Fin.ofNat 64 (∑ i : Fin 6, (h i).val * 2 ^ i.val)

theorem decode_zero : decode 0 = 0 := by
  funext i
  simp [decode]

set_option maxRecDepth 4096 in
theorem decode_encode : ∀ h : Normal, decode (encode h) = h := by decide

theorem encode_ne_zero (h : Normal) (hh : h ≠ 0) : encode h ≠ 0 := by
  intro hz
  have he := decode_encode h
  rw [hz, decode_zero] at he
  exact hh he.symm

def representatives : Fin 15 → Fin 64 := ![1, 2, 4, 5, 6, 9, 10, 11, 18, 19, 27, 30, 31, 35, 39]

theorem representative_ne_zero : ∀ r : Fin 15, decode (representatives r) ≠ 0 := by decide

/-- Each pair gives a representative index and a symmetry word. The zero
entry is unused; correctness is checked for every nonzero word below. -/
def orbitWitness : Fin 64 → Fin 15 × Fin 6 := ![
  (0, 0), (0, 0), (1, 0), (1, 5), (2, 0), (3, 0), (4, 0), (4, 5),
  (2, 2), (5, 0), (6, 0), (7, 0), (2, 1), (5, 5), (7, 5), (6, 5),
  (1, 2), (6, 3), (8, 0), (9, 0), (6, 2), (1, 3), (8, 3), (9, 5),
  (4, 2), (4, 3), (8, 1), (10, 0), (7, 4), (7, 1), (11, 0), (12, 0),
  (0, 2), (12, 1), (6, 1), (13, 0), (5, 2), (9, 1), (4, 1), (14, 0),
  (3, 2), (9, 3), (1, 1), (13, 3), (5, 4), (10, 1), (7, 3), (13, 4),
  (1, 4), (13, 2), (9, 2), (3, 1), (7, 2), (13, 1), (10, 2), (5, 1),
  (4, 4), (14, 1), (9, 4), (5, 3), (6, 4), (13, 5), (12, 2), (0, 1)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem orbitWitness_correct : ∀ w : Fin 64, w ≠ 0 →
    wordAction (orbitWitness w).2 (decode w) = decode (representatives (orbitWitness w).1) := by decide

theorem representative_coverage (h : Normal) (hh : h ≠ 0) :
    ∃ (r : Fin 15) (g : Fin 6), wordAction g h = decode (representatives r) := by
  refine ⟨(orbitWitness (encode h)).1, (orbitWitness (encode h)).2, ?_⟩
  simpa only [decode_encode] using orbitWitness_correct (encode h) (encode_ne_zero h hh)

theorem rank_representative_coverage (h : Normal) (hh : h ≠ 0) :
    ∃ r : Fin 15, restrictedRank h = restrictedRank (decode (representatives r)) := by
  obtain ⟨r, g, hg⟩ := representative_coverage h hh
  refine ⟨r, ?_⟩
  rw [← hg, wordAction_rank g h hh]

theorem first_representative_endpoint :
    restrictedRank (decode (representatives 0)) = bilinearRank (polynomialTensor 5 6) := by
  have hn : decode (representatives 0) = firstCoordinateNormal 5 := by
    funext i
    fin_cases i <;> decide
  rw [hn, restrictedRank_pivot _ 0 (firstCoordinateNormal_pivot 5)]
  exact N6.bilinearRank_endpoint

/-- The full square lower bound is reduced to exactly fifteen semantic
restriction lower bounds. All numerical sector bounds remain explicit. -/
theorem square_lower_bound_of_representatives
    (hLower : ∀ r : Fin 15, 16 ≤ restrictedRank (decode (representatives r))) :
    17 ≤ bilinearRank (polynomialTensor 6 6) := by
  apply bilinearRank_lower_bound_of_hyperplane_family _ (polynomialTensor_ne_zero 5 5)
  intro h hh
  obtain ⟨r, hr⟩ := rank_representative_coverage h hh
  refine ⟨pivot h, pivot_one h hh, ?_⟩
  change 16 ≤ restrictedRank h
  rw [hr]
  exact hLower r

theorem rectangle_lower_bound_of_first_representative
    (hLower : 16 ≤ restrictedRank (decode (representatives 0))) :
    16 ≤ bilinearRank (polynomialTensor 5 6) := by
  simpa only [first_representative_endpoint] using hLower

#check nonzero_has_one
#check pivot_one
#check restrictedRank_pivot
#check involution_rank
#check wordAction_ne_zero
#check wordAction_rank
#check decode_zero
#check decode_encode
#check encode_ne_zero
#check representative_ne_zero
#check orbitWitness_correct
#check representative_coverage
#check rank_representative_coverage
#check first_representative_endpoint
#check square_lower_bound_of_representatives
#check rectangle_lower_bound_of_first_representative
#print axioms nonzero_has_one
#print axioms pivot_one
#print axioms restrictedRank_pivot
#print axioms involution_rank
#print axioms wordAction_ne_zero
#print axioms wordAction_rank
#print axioms decode_zero
#print axioms decode_encode
#print axioms encode_ne_zero
#print axioms representative_ne_zero
#print axioms orbitWitness_correct
#print axioms representative_coverage
#print axioms rank_representative_coverage
#print axioms first_representative_endpoint
#print axioms square_lower_bound_of_representatives
#print axioms rectangle_lower_bound_of_first_representative
end
end UnrestrictedBooleanMul.N6.Orbits
