import UnrestrictedBooleanMul.N5.EffectiveFibers

/-!
# Rank of target secants

This module proves the algebraic bridge from arbitrary decomposable endpoints
to the Hankel rank condition used by the closed-place classification.  No
ambient-form enumeration is used: cancellation in the two diagonal blocks
forces the two endpoint planes to agree there, after which the cross block is
written as a sum of two outer products.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

abbrev Vec5 := Fin 5 → F₂

def vecWedge5 (u v : Vec5) : Fin 5 → Fin 5 → F₂ :=
  fun i j => u i * v j + u j * v i

def tripleWedge5 (u v x : Vec5) :
    Fin 5 → Fin 5 → Fin 5 → F₂ :=
  fun i j k =>
    x i * (u j * v k + u k * v j) +
    x j * (u i * v k + u k * v i) +
    x k * (u i * v j + u j * v i)

def TripleWedgeZero5 (u v x : Vec5) : Prop :=
  tripleWedge5 u v x = 0

instance (u v x : Vec5) : Decidable (TripleWedgeZero5 u v x) :=
  inferInstanceAs (Decidable (tripleWedge5 u v x = 0))

/-- If `u ∧ v` is nonzero and `x ∧ u ∧ v = 0`, then `x` is in the
two-plane spanned by `u,v`.  The proof solves from one nonzero minor. -/
theorem tripleWedgeZero5_mem_span (u v x : Vec5)
    (huv : vecWedge5 u v ≠ 0) (hx : TripleWedgeZero5 u v x) :
    ∃ a b : F₂, x = a • u + b • v := by
  have hex : ∃ i j, vecWedge5 u v i j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply huv
    funext i j
    exact hn i j
  rcases hex with ⟨i, j, hij⟩
  have hij1 : vecWedge5 u v i j = 1 :=
    (f2_eq_zero_or_one (vecWedge5 u v i j)).resolve_left hij
  refine ⟨x i * v j + x j * v i, u i * x j + u j * x i, ?_⟩
  funext k
  have hk := congrFun (congrFun (congrFun hx i) j) k
  change x i * (u j * v k + u k * v j) +
      x j * (u i * v k + u k * v i) +
      x k * (u i * v j + u j * v i) = 0 at hk
  have hij1' : u i * v j + u j * v i = 1 := by
    simpa [vecWedge5] using hij1
  rw [hij1', mul_one] at hk
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hs :
      (x i * (u j * v k + u k * v j) +
        x j * (u i * v k + u k * v i)) - x k = 0 := by
    simpa only [CharTwo.sub_eq_add] using hk
  have hk' : x k = x i * (u j * v k + u k * v j) +
      x j * (u i * v k + u k * v i) := (sub_eq_zero.mp hs).symm
  rw [hk']
  ring

theorem vecWedgeTwo_repeat5 (x y : Vec5) :
    (fun i j k =>
      x i * vecWedge5 x y j k + x j * vecWedge5 x y i k +
        x k * vecWedge5 x y i j) = 0 := by
  funext i j k
  simp [vecWedge5]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Cross-block coordinates of a decomposable ambient two-form. -/
def crossPart (u v : LinearForm) (i j : Fin 5) : F₂ :=
  u (aCoord i) * v (bCoord j) + u (bCoord j) * v (aCoord i)

def IsOuterCross (u v : LinearForm) : Prop :=
  ∃ a b : Fin 5 → F₂, ∀ i j, crossPart u v i j = a i * b j

theorem outerCross_of_A_dependent {u v : LinearForm}
    (h : vecWedge5 (aPart u) (aPart v) = 0) : IsOuterCross u v := by
  have hp : ∀ i j, aPart u i * aPart v j + aPart u j * aPart v i = 0 := by
    intro i j
    simpa [vecWedge5] using congrFun (congrFun h i) j
  rcases N4.dependent_of_vectorWedge_zero (aPart u) (aPart v) hp with
    hu | hv | huv
  · refine ⟨aPart v, bPart u, ?_⟩
    intro i j
    have hui : u (aCoord i) = 0 := congrFun hu i
    simp [crossPart, aPart, bPart, hui]
    ring
  · refine ⟨aPart u, bPart v, ?_⟩
    intro i j
    have hvi : v (aCoord i) = 0 := congrFun hv i
    simp [crossPart, aPart, bPart, hvi]
  · refine ⟨aPart u, fun j => bPart v j + bPart u j, ?_⟩
    intro i j
    have hui : u (aCoord i) = v (aCoord i) := congrFun huv i
    simp only [crossPart, aPart, bPart, hui]
    ring

/-- A target Hankel matrix expressed as the sum of two outer products. -/
def IsTwoOuterTarget (c : TargetCoeff) : Prop :=
  ∃ a b x y : Fin 5 → F₂,
    ∀ i j, c (hankelIndex i j) = a i * b j + x i * y j

theorem twoOuter_rankTwo {c : TargetCoeff} (hc : IsTwoOuterTarget c) :
    HankelRankLETwo c := by
  rcases hc with ⟨a, b, x, y, hc⟩
  intro i k m j l n
  simp only [hankelMinorThree, hankelMatrix]
  simp_rw [hc]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.six_eq_zero_f2]

/-- If a target two-form is the sum of two arbitrary decomposable two-forms,
then its `5 × 5` Hankel matrix has rank at most two. -/
theorem target_sum_two_decomposable_rankTwo {c : TargetCoeff}
    {u v x y : LinearForm}
    (h : targetTwo c = squarefreeWedge u v + squarefreeWedge x y) :
    HankelRankLETwo c := by
  have hAA : vecWedge5 (aPart u) (aPart v) =
      vecWedge5 (aPart x) (aPart y) := by
    funext i j
    by_cases hij : i = j
    · subst j
      simp only [vecWedge5]
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
    · have heq := congrFun h
          (quadraticPair (aCoord i) (aCoord j)
            (fun hcoord => hij (aCoord_injective hcoord)))
      rw [targetTwo_sameA c i j hij] at heq
      simp only [Pi.add_apply, squarefreeWedge_pair] at heq
      rw [← CharTwo.sub_eq_add] at heq
      have hz := sub_eq_zero.mp heq.symm
      simpa [vecWedge5, aPart] using hz
  by_cases hz : vecWedge5 (aPart u) (aPart v) = 0
  · have hz' : vecWedge5 (aPart x) (aPart y) = 0 := hAA ▸ hz
    rcases outerCross_of_A_dependent hz with ⟨a, b, hab⟩
    rcases outerCross_of_A_dependent hz' with ⟨p, q, hpq⟩
    apply twoOuter_rankTwo
    exact ⟨a, b, p, q, by
      intro i j
      have hij := congrFun h
        (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j))
      rw [targetTwo_cross] at hij
      calc
        c (hankelIndex i j) =
            crossPart u v i j + crossPart x y i j := by
              simpa [crossPart, squarefreeWedge_pair] using hij
        _ = a i * b j + p i * q j := by rw [hab i j, hpq i j]⟩
  · have hxTriple : TripleWedgeZero5 (aPart u) (aPart v) (aPart x) := by
      funext i j k
      have hr := congrFun (congrFun (congrFun
        (vecWedgeTwo_repeat5 (aPart x) (aPart y)) i) j) k
      change aPart x i * vecWedge5 (aPart u) (aPart v) j k +
          aPart x j * vecWedge5 (aPart u) (aPart v) i k +
          aPart x k * vecWedge5 (aPart u) (aPart v) i j = 0
      rw [hAA]
      simpa using hr
    have hyTriple : TripleWedgeZero5 (aPart u) (aPart v) (aPart y) := by
      funext i j k
      have hr := congrFun (congrFun (congrFun
        (vecWedgeTwo_repeat5 (aPart y) (aPart x)) i) j) k
      change aPart y i * vecWedge5 (aPart u) (aPart v) j k +
          aPart y j * vecWedge5 (aPart u) (aPart v) i k +
          aPart y k * vecWedge5 (aPart u) (aPart v) i j = 0
      rw [hAA]
      simpa [vecWedge5, add_comm, mul_comm] using hr
    rcases tripleWedgeZero5_mem_span (aPart u) (aPart v) (aPart x) hz hxTriple with
      ⟨α, β, hxspan⟩
    rcases tripleWedgeZero5_mem_span (aPart u) (aPart v) (aPart y) hz hyTriple with
      ⟨γ, δ, hyspan⟩
    apply twoOuter_rankTwo
    refine ⟨aPart u,
      fun j => bPart v j + α * bPart y j + γ * bPart x j,
      aPart v,
      fun j => bPart u j + β * bPart y j + δ * bPart x j, ?_⟩
    intro i j
    have hij := congrFun h
      (quadraticPair (aCoord i) (bCoord j) (aCoord_ne_bCoord i j))
    rw [targetTwo_cross] at hij
    have hxi : x (aCoord i) = α * u (aCoord i) + β * v (aCoord i) := by
      simpa [aPart] using congrFun hxspan i
    have hyi : y (aCoord i) = γ * u (aCoord i) + δ * v (aCoord i) := by
      simpa [aPart] using congrFun hyspan i
    simp only [Pi.add_apply, squarefreeWedge_pair] at hij
    rw [hxi, hyi] at hij
    change c (hankelIndex i j) =
      u (aCoord i) *
          (v (bCoord j) + α * y (bCoord j) + γ * x (bCoord j)) +
        v (aCoord i) *
          (u (bCoord j) + β * y (bCoord j) + δ * x (bCoord j))
    rw [hij]
    ring

end

end N5
end UnrestrictedBooleanMul
