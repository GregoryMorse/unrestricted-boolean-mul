import UnrestrictedBooleanMul.N5.QuadraticCoordinates
import UnrestrictedBooleanMul.N4.BooleanIdentities

/-!
# Algebraic substitution in Boolean ANFs

The idempotence argument used by `N4.PlaceSymmetry` works in every number of
variables.  These maps transport entire products and their affine corrections,
not merely their homogeneous exterior forms.
-/

namespace UnrestrictedBooleanMul
noncomputable section

private theorem anf_prod_union_generic {m n : Nat}
    (s t : Finset (Fin m)) (f : Fin m → ANF n) :
    (∏ i ∈ s ∪ t, f i) = (∏ i ∈ s, f i) * ∏ i ∈ t, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    by_cases hit : i ∈ t
    · have hu : insert i s ∪ t = s ∪ t := by
        ext j
        simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ((rfl | h) | h)
          · exact Or.inr hit
          · exact Or.inl h
          · exact Or.inr h
        · tauto
      rw [hu, ih, Finset.prod_insert hi]
      have ht : (∏ j ∈ t, f j) = f i * ∏ j ∈ t.erase i, f j :=
        (Finset.mul_prod_erase t f hit).symm
      rw [ht]
      calc
        _ = (f i * f i) * (∏ j ∈ s, f j) * ∏ j ∈ t.erase i, f j := by
          rw [N4.anf_mul_self]; ac_rfl
        _ = _ := by ac_rfl
    · rw [Finset.insert_union, Finset.prod_insert (by simp [hi, hit]),
        Finset.prod_insert hi, ih, mul_assoc]

/-- Substitution of arbitrary Boolean ANFs for the input variables. -/
def anfSubstitution {m n : Nat} (f : Fin m → ANF n) : ANF m →ₐ[F₂] ANF n :=
  MonoidAlgebra.lift F₂ (ANF n) (Monomial m)
    { toFun := fun s => ∏ i ∈ s.vars, f i
      map_one' := by simp
      map_mul' := fun s t => anf_prod_union_generic s.vars t.vars f }

@[simp] theorem anfSubstitution_monomial {m n : Nat}
    (f : Fin m → ANF n) (s : Finset (Fin m)) :
    anfSubstitution f (monomial s) = ∏ i ∈ s, f i := by
  simp [anfSubstitution, monomial, MonoidAlgebra.lift_apply]

@[simp] theorem anfSubstitution_X {m n : Nat}
    (f : Fin m → ANF n) (i : Fin m) :
    anfSubstitution f (X i) = f i := by simp [X]

theorem anfSubstitution_mem_affine {m n : Nat}
    (f : Fin m → ANF n) (hf : ∀ i, f i ∈ affine n)
    {p : ANF m} (hp : p ∈ affine m) :
    anfSubstitution f p ∈ affine n := by
  refine Submodule.span_induction (p := fun p _ =>
    anfSubstitution f p ∈ affine n) ?_ ?_ ?_ ?_ hp
  · intro p hp
    rcases hp with hp | ⟨i, rfl⟩
    · have heq : p = 1 := hp
      simpa [heq] using one_mem_affine n
    · simpa using hf i
  · simp
  · intro p q _ _ hp hq
    simpa only [map_add] using (affine n).add_mem hp hq
  · intro a p _ hp
    simpa only [map_smul] using (affine n).smul_mem a hp

namespace N5

/-- Linear coordinate substitutions preserve quadraticity. -/
theorem anfSubstitution_mem_quadratic
    (f : Fin 10 → ANF 10) (hf : ∀ i, f i ∈ affine 10)
    {p : ANF 10} (hp : p ∈ N4.quadraticANFSpace 10) :
    anfSubstitution f p ∈ N4.quadraticANFSpace 10 := by
  obtain ⟨a, ell, q, rfl⟩ := exists_quadraticCoordinates hp
  rw [quadraticCoordinateANF, map_add]
  apply (N4.quadraticANFSpace 10).add_mem
  · exact N4.affine_le_quadraticANFSpace
      (anfSubstitution_mem_affine f hf ((affine 10).add_mem
        ((affine 10).smul_mem a (one_mem_affine 10))
        (linearANFTen_mem_affine ell)))
  · rw [quadraticANFOfForm, map_sum]
    apply Submodule.sum_mem
    intro s _
    rw [map_smul]
    apply Submodule.smul_mem
    obtain ⟨i, j, hij, hs⟩ := QuadraticIndex.exists_pair s
    rw [hs]
    change anfSubstitution f (monomial {i, j}) ∈ _
    rw [anfSubstitution_monomial, Finset.prod_pair hij]
    exact (show N4.DegreeLE 1 (f i) from fun s hs =>
      N4.affine_coeff_zero_of_two_le (hf i) s (by omega)).mul
        (show N4.DegreeLE 1 (f j) from fun s hs =>
          N4.affine_coeff_zero_of_two_le (hf j) s (by omega))

/-- An exact target equation between quadratic parts lifts modulo Aff.
This avoids imposing an incorrect naturality law on lower-degree terms. -/
theorem exists_affine_add_target_of_quadraticProjection
    {p : ANF 10} (hp : p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff) (hc : quadraticProjection 10 p = targetTwo c) :
    ∃ a ∈ affine 10, p = a + targetANF c := by
  obtain ⟨a, ell, q, rfl⟩ := exists_quadraticCoordinates hp
  have hq : q = targetTwo c := by simpa using hc
  refine ⟨a • (1 : ANF 10) + linearANFTen ell,
    (affine 10).add_mem ((affine 10).smul_mem a (one_mem_affine 10))
      (linearANFTen_mem_affine ell), ?_⟩
  simp [quadraticCoordinateANF, hq, quadraticANFOfForm_targetTwo]

end N5
end
end UnrestrictedBooleanMul
