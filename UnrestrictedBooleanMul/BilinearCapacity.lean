import UnrestrictedBooleanMul.Models
import UnrestrictedBooleanMul.Capacity
import UnrestrictedBooleanMul.CapacityFiber
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The abstract capacity criterion in the repository's actual bilinear
formula model. Rank-one generators include zero; it never changes a span. -/
namespace UnrestrictedBooleanMul
noncomputable section

def BilinearTensor.targetSpace {a b o : Nat} (T : BilinearTensor a b o) :
    Submodule F₂ (Fin a → Fin b → F₂) := Submodule.span F₂ (Set.range T)

def bilinearRankOne (a b : Nat) : Set (Fin a → Fin b → F₂) :=
  {p | ∃ (x : Fin a → F₂) (y : Fin b → F₂), p = fun i j => x i * y j}

def BilinearFormula.productMatrices {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) : Fin r → Fin a → Fin b → F₂ :=
  fun k i j => F.left k i * F.right k j

theorem BilinearFormula.productMatrices_rankOne {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) (k : Fin r) : F.productMatrices k ∈ bilinearRankOne a b :=
  ⟨F.left k, F.right k, rfl⟩

theorem BilinearFormula.targetSpace_le_products {a b o r : Nat} {T : BilinearTensor a b o}
    (F : BilinearFormula T r) :
    T.targetSpace ≤ Submodule.span F₂ (Set.range F.productMatrices) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  apply (Submodule.mem_span_range_iff_exists_fun F₂).mpr
  refine ⟨F.output s, ?_⟩
  funext i j
  simpa [BilinearFormula.productMatrices, mul_assoc] using (F.correct s i j).symm

def BilinearFormula.of_rankOne_span {a b o r : Nat} (T : BilinearTensor a b o)
    (p : Fin r → Fin a → Fin b → F₂) (hp : ∀ k, p k ∈ bilinearRankOne a b)
    (hT : T.targetSpace ≤ Submodule.span F₂ (Set.range p)) : BilinearFormula T r := by
  classical
  change ∀ k, ∃ (x : Fin a → F₂) (y : Fin b → F₂), p k = fun i j => x i * y j at hp
  choose x y hxy using hp
  have hc : ∀ s, ∃ c : Fin r → F₂, ∑ k, c k • p k = T s := by
    intro s
    exact (Submodule.mem_span_range_iff_exists_fun F₂).mp (hT (Submodule.subset_span ⟨s, rfl⟩))
  choose c hc using hc
  refine { left := x, right := y, output := c, correct := ?_ }
  intro s i j
  have h := congrFun (congrFun (hc s) i) j
  simpa [hxy, mul_assoc] using h.symm

theorem hasBilinearFormula_iff_rankOne_span {a b o r : Nat} (T : BilinearTensor a b o) :
    HasBilinearFormula T r ↔ ∃ p : Fin r → Fin a → Fin b → F₂,
      (∀ k, p k ∈ bilinearRankOne a b) ∧ T.targetSpace ≤ Submodule.span F₂ (Set.range p) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.productMatrices, F.productMatrices_rankOne, F.targetSpace_le_products⟩
  · rintro ⟨p, hp, hT⟩
    exact ⟨BilinearFormula.of_rankOne_span T p hp hT⟩

/-- Proposition 4.1 for every tensor in the existing semantic model.
The needed full-capacity quotient subspace is still an explicit existential. -/
theorem bilinearRank_capacity_criterion {a b o : Nat} (T : BilinearTensor a b o) (e : Nat) :
    bilinearRank T ≤ Module.finrank F₂ T.targetSpace + e ↔
    ∃ Q : Submodule F₂ ((Fin a → Fin b → F₂) ⧸ T.targetSpace),
      Module.finrank F₂ Q ≤ e ∧
        Capacity.value T.targetSpace (bilinearRankOne a b) Q = Module.finrank F₂ T.targetSpace := by
  classical
  rw [← Capacity.criterion]
  constructor
  · intro hr
    obtain ⟨F⟩ := Nat.find_spec T.hasFormula
    exact ⟨bilinearRank T, hr, F.productMatrices, F.productMatrices_rankOne,
      F.targetSpace_le_products⟩
  · rintro ⟨r, hr, p, hp, hT⟩
    exact (bilinearRank_le (BilinearFormula.of_rankOne_span T p hp hT)).trans hr

/-- Identical criterion with the manuscript's nonzero rank-one catalogue.
The zero-generator convention is discharged, not left as a model assumption. -/
theorem bilinearRank_capacity_criterion_nonzero {a b o : Nat} (T : BilinearTensor a b o) (e : Nat) :
    bilinearRank T ≤ Module.finrank F₂ T.targetSpace + e ↔
    ∃ Q : Submodule F₂ ((Fin a → Fin b → F₂) ⧸ T.targetSpace),
      Module.finrank F₂ Q ≤ e ∧
        Capacity.value T.targetSpace (bilinearRankOne a b \ {0}) Q = Module.finrank F₂ T.targetSpace := by
  simpa only [Capacity.value_remove_zero] using bilinearRank_capacity_criterion T e

/-- The fiber formula is now attached to actual bilinear rank, not just an
abstract space. Population and all lifts are semantic; no stored table is
assumed complete. This equivalence still needs sector exclusions to yield
a numerical lower bound. -/
theorem bilinearRank_fiber_criterion {a b o : Nat} (T : BilinearTensor a b o) (e : Nat) :
    bilinearRank T ≤ Module.finrank F₂ T.targetSpace + e ↔
    ∃ Q : Submodule F₂ ((Fin a → Fin b → F₂) ⧸ T.targetSpace),
      Module.finrank F₂ Q ≤ e ∧
        Module.finrank F₂ (Capacity.localDisplacement T.targetSpace (bilinearRankOne a b \ {0}) Q) +
          Module.finrank F₂ (LinearMap.range
            (Capacity.populatedRelationMap T.targetSpace (bilinearRankOne a b \ {0}) Q)) =
              Module.finrank F₂ T.targetSpace := by
  simpa only [Capacity.value_populated_formula] using bilinearRank_capacity_criterion_nonzero T e

#check BilinearFormula.productMatrices_rankOne
#check BilinearFormula.targetSpace_le_products
#check BilinearFormula.of_rankOne_span
#check hasBilinearFormula_iff_rankOne_span
#check bilinearRank_capacity_criterion
#check bilinearRank_capacity_criterion_nonzero
#check bilinearRank_fiber_criterion
#print axioms BilinearFormula.productMatrices_rankOne
#print axioms BilinearFormula.targetSpace_le_products
#print axioms BilinearFormula.of_rankOne_span
#print axioms hasBilinearFormula_iff_rankOne_span
#print axioms bilinearRank_capacity_criterion
#print axioms bilinearRank_capacity_criterion_nonzero
#print axioms bilinearRank_fiber_criterion
end
end UnrestrictedBooleanMul
