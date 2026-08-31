import UnrestrictedBooleanMul.N4.QuarticSeedNormalForm

/-!
# The degree-six seed-plane equation

The manuscript's degree-six identity is recorded through one squarefree
coefficient.  On the three rational-place quadratic directions this
coefficient is their alternating determinant.  Degree subadditivity removes
every term containing an affine factor, so no large exterior-power coordinate
space or circuit enumeration is needed.
-/

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- A six-variable probe on which the three rational places have coefficient
one in their exterior product: `a₀ a₁ a₃ b₀ b₁ b₃`. -/
def sexticProbeSet : Finset (Fin 8) := {0, 1, 3, 4, 5, 7}

def anfSexticProbe : ANF 8 →ₗ[F₂] F₂ where
  toFun p := p.coeff ⟨sexticProbeSet⟩
  map_add' p q := by simp
  map_smul' a p := by simp

@[simp] theorem anfSexticProbe_monomial (s : Finset (Fin 8)) :
    anfSexticProbe (monomial s) = if s = sexticProbeSet then 1 else 0 := by
  simp [anfSexticProbe, coeff_monomial]

@[simp] theorem sexticProbeSet_card : sexticProbeSet.card = 6 := by
  decide

theorem anfSexticProbe_eq_zero_of_degreeLE_five {p : ANF 8}
    (hp : DegreeLE 5 p) : anfSexticProbe p = 0 := by
  exact hp ⟨sexticProbeSet⟩ (by simp [sexticProbeSet_card])

theorem degreeLE_one_affineANF (a : F₂) (ell : LinearForm) :
    DegreeLE 1 (affineANF a ell) := by
  intro s hs
  exact affine_coeff_zero_of_two_le (affineANF_mem a ell) s (by omega)

theorem degreeLE_two_rationalANF (alpha : Fin 3 → F₂) :
    DegreeLE 2 (rationalANF alpha) := by
  exact targetAmbient_le_quadraticANFSpace
    (Submodule.mem_sup_right (targetANF_mem_mulTarget _))

theorem degreeLE_two_targetANF (c : TargetCoeff) :
    DegreeLE 2 (targetANF c) := by
  exact targetAmbient_le_quadraticANFSpace
    (Submodule.mem_sup_right (targetANF_mem_mulTarget c))

theorem degreeLE_two_of_mem_rationalLow {p : ANF 8}
    (hp : p ∈ rationalLowSpace) : DegreeLE 2 p := by
  exact targetAmbient_le_quadraticANFSpace
    (rationalLowSpace_le_targetAmbient hp)

/-- The characteristic-two determinant of three rational-place coefficient
vectors. -/
def rationalTripleDet (alpha beta delta : Fin 3 → F₂) : F₂ :=
  alpha 0 * beta 1 * delta 2 + alpha 0 * beta 2 * delta 1 +
  alpha 1 * beta 0 * delta 2 + alpha 1 * beta 2 * delta 0 +
  alpha 2 * beta 0 * delta 1 + alpha 2 * beta 1 * delta 0

private theorem anfSexticProbe_rationalPlaces_012 :
    anfSexticProbe
        (targetANF (rationalPlaceCoeff 0) *
          targetANF (rationalPlaceCoeff 1) *
            targetANF (rationalPlaceCoeff 2)) = 1 := by
  simp (disch := decide)
    [anfSexticProbe, sexticProbeSet, targetANF,
      rationalPlaceCoeff, rZeroCoeff, rOneCoeff, rInfinityCoeff,
      UnrestrictedBooleanMul.Mul, mulCoefficient,
      Fin.sum_univ_succ, aVar, bVar, X, monomial_mul,
      coeff_monomial, mul_add, add_mul] <;> decide

private theorem fin_three_pairwise_distinct
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨
    (i = 0 ∧ j = 2 ∧ k = 1) ∨
    (i = 1 ∧ j = 0 ∧ k = 2) ∨
    (i = 1 ∧ j = 2 ∧ k = 0) ∨
    (i = 2 ∧ j = 0 ∧ k = 1) ∨
    (i = 2 ∧ j = 1 ∧ k = 0) := by
  revert i j k
  decide

set_option maxHeartbeats 1000000 in
private theorem anfSexticProbe_rationalPlace_triple :
    ∀ i j k : Fin 3,
      anfSexticProbe
          (targetANF (rationalPlaceCoeff i) *
            targetANF (rationalPlaceCoeff j) *
              targetANF (rationalPlaceCoeff k)) =
        if i ≠ j ∧ i ≠ k ∧ j ≠ k then 1 else 0 := by
  intro i j k
  have pairZero (u v : Fin 3) :
      anfSexticProbe
          (targetANF (rationalPlaceCoeff u) *
            targetANF (rationalPlaceCoeff v)) = 0 := by
    apply anfSexticProbe_eq_zero_of_degreeLE_five
    exact ((degreeLE_two_targetANF _).mul
      (degreeLE_two_targetANF _)).mono (by omega)
  by_cases hij : i = j
  · subst j
    simp [anf_mul_self, pairZero]
  by_cases hik : i = k
  · subst k
    have hreorder :
        targetANF (rationalPlaceCoeff i) *
              targetANF (rationalPlaceCoeff j) *
            targetANF (rationalPlaceCoeff i) =
          targetANF (rationalPlaceCoeff i) *
            targetANF (rationalPlaceCoeff i) *
              targetANF (rationalPlaceCoeff j) := by ac_rfl
    rw [hreorder, anf_mul_self, pairZero]
    simp [hij]
  by_cases hjk : j = k
  · subst k
    rw [mul_assoc, anf_mul_self, pairZero]
    simp
  · have hdistinct : i ≠ j ∧ i ≠ k ∧ j ≠ k :=
      ⟨hij, hik, hjk⟩
    rw [if_pos hdistinct]
    rcases fin_three_pairwise_distinct i j k hij hik hjk with
      h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        anfSexticProbe_rationalPlaces_012

/-- The selected sextic coefficient of three rational quadratics is exactly
the determinant of their three coefficient vectors. -/
theorem anfSexticProbe_rational_triple
    (alpha beta delta : Fin 3 → F₂) :
    anfSexticProbe
        (rationalANF alpha * rationalANF beta * rationalANF delta) =
      rationalTripleDet alpha beta delta := by
  rw [rationalANF_eq_sum, rationalANF_eq_sum, rationalANF_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul,
    anfSexticProbe_rationalPlace_triple]
  simp (disch := decide) [Fin.sum_univ_succ, rationalTripleDet]
  ring

/-- In a product of three rational-low factors, the sextic probe sees only
the three rational quadratic parts. -/
theorem anfSexticProbe_lowProduct_mul_lowFactor
    (a b c : F₂) (ell m n : LinearForm)
    (alpha beta delta : Fin 3 → F₂) :
    anfSexticProbe
        (((affineANF a ell + rationalANF alpha) *
            (affineANF b m + rationalANF beta)) *
          (affineANF c n + rationalANF delta)) =
      rationalTripleDet alpha beta delta := by
  have ha := degreeLE_one_affineANF a ell
  have hb := degreeLE_one_affineANF b m
  have hc := degreeLE_one_affineANF c n
  have halpha := degreeLE_two_rationalANF alpha
  have hbeta := degreeLE_two_rationalANF beta
  have hdelta := degreeLE_two_rationalANF delta
  have vanish {p q r : ANF 8} {dp dq dr : Nat}
      (hp : DegreeLE dp p) (hq : DegreeLE dq q) (hr : DegreeLE dr r)
      (hsum : dp + dq + dr ≤ 5) : anfSexticProbe (p * q * r) = 0 := by
    apply anfSexticProbe_eq_zero_of_degreeLE_five
    exact ((hp.mul hq).mul hr).mono (by omega)
  simp only [add_mul, mul_add, map_add]
  rw [vanish ha hb hc (by omega), vanish ha hb hdelta (by omega),
    vanish ha hbeta hc (by omega), vanish ha hbeta hdelta (by omega),
    vanish halpha hb hc (by omega), vanish halpha hb hdelta (by omega),
    vanish halpha hbeta hc (by omega),
    anfSexticProbe_rational_triple]
  simp

/-- The degree-six part of a seed-using target equation forces the rational
quadratic part of the feedback factor into the seed coefficient plane.  This
lemma records the determinant equation; the finite three-dimensional plane
criterion below turns it into explicit span membership. -/
theorem rationalTripleDet_eq_zero_of_seedUsing_target
    {g correction factor target : ANF 8}
    {a b c : F₂} {ell m n : LinearForm}
    {alpha beta delta : Fin 3 → F₂}
    (hg : g =
      (affineANF a ell + rationalANF alpha) *
        (affineANF b m + rationalANF beta))
    (hcorrection : correction ∈ rationalLowSpace)
    (hfactor : factor = affineANF c n + rationalANF delta)
    (htarget : target = (g + correction) * factor)
    (htargetAmbient : target ∈ targetAmbient 8 (mulTarget 4)) :
    rationalTripleDet alpha beta delta = 0 := by
  have htargetDegree : DegreeLE 2 target :=
    targetAmbient_le_quadraticANFSpace htargetAmbient
  have htargetProbe : anfSexticProbe target = 0 :=
    anfSexticProbe_eq_zero_of_degreeLE_five
      (htargetDegree.mono (by omega))
  have hcorrectionDegree : DegreeLE 2 correction :=
    degreeLE_two_of_mem_rationalLow hcorrection
  have hfactorDegree : DegreeLE 2 factor := by
    rw [hfactor]
    intro s hs
    simp [degreeLE_one_affineANF c n s (by omega),
      degreeLE_two_rationalANF delta s hs]
  have hcorrectionProbe : anfSexticProbe (correction * factor) = 0 :=
    anfSexticProbe_eq_zero_of_degreeLE_five
      ((hcorrectionDegree.mul hfactorDegree).mono (by omega))
  calc
    rationalTripleDet alpha beta delta = anfSexticProbe (g * factor) := by
      rw [hg, hfactor, anfSexticProbe_lowProduct_mul_lowFactor]
    _ = anfSexticProbe ((g + correction) * factor) := by
      simp [add_mul, hcorrectionProbe]
    _ = anfSexticProbe target := by rw [htarget]
    _ = 0 := htargetProbe

def InRationalCoeffPlane
    (alpha beta delta : Fin 3 → F₂) : Prop :=
  ∃ p q : F₂, delta = p • alpha + q • beta

instance (alpha beta delta : Fin 3 → F₂) :
    Decidable (InRationalCoeffPlane alpha beta delta) := by
  unfold InRationalCoeffPlane
  infer_instance

set_option maxHeartbeats 1000000 in
/-- In `F₂³`, a zero determinant against two independent vectors is
equivalent to membership in their plane. -/
theorem rationalTripleDet_zero_mem_plane
    (alpha beta delta : Fin 3 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hab : alpha ≠ beta)
    (hdet : rationalTripleDet alpha beta delta = 0) :
    InRationalCoeffPlane alpha beta delta := by
  revert alpha beta delta
  decide

end

end N4
end UnrestrictedBooleanMul
