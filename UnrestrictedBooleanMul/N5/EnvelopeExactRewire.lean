import UnrestrictedBooleanMul.N5.EnvelopeLocalDependentExact
import UnrestrictedBooleanMul.N5.EnvelopeTwoRotationShadow

/-!
# Exact Boolean cubic rewiring

The normalized envelope development rewires two products by bilinearity of
their exterior quartic and cubic parts.  The literal Boolean cubic has one
additional quadratic--quadratic overlap term.  That term is bilinear as
well, so the same rewire is valid without discarding any ANF coefficient.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem quadraticOverlapCubic_add_left
    (q c d : TwoForm) :
    quadraticOverlapCubic (q + c) d =
      quadraticOverlapCubic q d + quadraticOverlapCubic c d := by
  rw [quadraticOverlapCubic,
    show quadraticANFOfForm (q + c) =
        quadraticANFOfForm q + quadraticANFOfForm c by
      exact map_add quadraticANFOfFormLinear q c,
    add_mul, map_add]
  rfl

theorem quadraticOverlapCubic_add_right
    (q c d : TwoForm) :
    quadraticOverlapCubic q (c + d) =
      quadraticOverlapCubic q c + quadraticOverlapCubic q d := by
  rw [quadraticOverlapCubic,
    show quadraticANFOfForm (c + d) =
        quadraticANFOfForm c + quadraticANFOfForm d by
      exact map_add quadraticANFOfFormLinear c d,
    mul_add, map_add]
  rfl

/-- The Boolean cubic overlap obeys the same two-product rewire as the
exterior cubic component. -/
theorem quadraticOverlapCubic_twoProduct_rewire
    (q c q' c' : TwoForm) :
    quadraticOverlapCubic q c + quadraticOverlapCubic q' c' =
      quadraticOverlapCubic q (c + c') +
        quadraticOverlapCubic (q + q') c' := by
  rw [quadraticOverlapCubic_add_right,
    quadraticOverlapCubic_add_left]
  have hself :
      quadraticOverlapCubic q c' + quadraticOverlapCubic q c' = 0 := by
    funext i j k
    exact CharTwo.add_self_eq_zero
      (quadraticOverlapCubic q c' i j k)
  calc
    quadraticOverlapCubic q c + quadraticOverlapCubic q' c' =
        (quadraticOverlapCubic q c + quadraticOverlapCubic q' c') + 0 := by
      rw [add_zero]
    _ = (quadraticOverlapCubic q c + quadraticOverlapCubic q' c') +
        (quadraticOverlapCubic q c' + quadraticOverlapCubic q c') := by
      rw [hself]
    _ = (quadraticOverlapCubic q c + quadraticOverlapCubic q c') +
        (quadraticOverlapCubic q c' + quadraticOverlapCubic q' c') := by
      abel

/-- Exact literal cubic coefficients are preserved by the bilinear
two-product rewire. -/
theorem exactLowProductCubic_twoProduct_rewire
    (ell m ell' m' : LinearForm) (q c q' c' : TwoForm) :
    exactLowProductCubic ell m q c +
        exactLowProductCubic ell' m' q' c' =
      exactLowProductCubic ell (m + m') q (c + c') +
        exactLowProductCubic (ell + ell') m' (q + q') c' := by
  have hoverlap := quadraticOverlapCubic_twoProduct_rewire q c q' c'
  have hfactor := factorPlaneCubic_twoProduct_rewire
    ell m ell' m' q c q' c'
  simp only [exactLowProductCubic]
  calc
    (quadraticOverlapCubic q c + factorPlaneCubic ell m q c) +
          (quadraticOverlapCubic q' c' + factorPlaneCubic ell' m' q' c') =
        (quadraticOverlapCubic q c + quadraticOverlapCubic q' c') +
          (factorPlaneCubic ell m q c + factorPlaneCubic ell' m' q' c') := by
      abel
    _ = (quadraticOverlapCubic q (c + c') +
            quadraticOverlapCubic (q + q') c') +
          (factorPlaneCubic ell (m + m') q (c + c') +
            factorPlaneCubic (ell + ell') m' (q + q') c') := by
      rw [hoverlap, hfactor]
    _ = (quadraticOverlapCubic q (c + c') +
            factorPlaneCubic ell (m + m') q (c + c')) +
          (quadraticOverlapCubic (q + q') c' +
            factorPlaneCubic (ell + ell') m' (q + q') c') := by
      abel

/-- Equality of two literal cubics becomes equality of the two rewired
literal cubics. -/
theorem exactLowProductCubic_twoProduct_rewire_of_eq
    (ell m ell' m' : LinearForm) (q c q' c' : TwoForm)
    (hcubic : exactLowProductCubic ell m q c =
      exactLowProductCubic ell' m' q' c') :
    exactLowProductCubic ell (m + m') q (c + c') =
      exactLowProductCubic (ell + ell') m' (q + q') c' := by
  have hrewire := exactLowProductCubic_twoProduct_rewire
    ell m ell' m' q c q' c'
  have hzero :
      exactLowProductCubic ell (m + m') q (c + c') +
        exactLowProductCubic (ell + ell') m' (q + q') c' = 0 := by
    rw [← hrewire, hcubic]
    funext i j k
    exact CharTwo.add_self_eq_zero
      (exactLowProductCubic ell' m' q' c' i j k)
  funext i j k
  exact CharTwo.add_eq_zero.mp
    (congrFun (congrFun (congrFun hzero i) j) k)

/-- Applying the same ordered-plane basis change to the linear and
quadratic layers preserves the complete Boolean high quotient. -/
theorem PlaneBasisChange.lowProductHighClass_basisPair
    (g : PlaneBasisChange) (ell m : LinearForm) (q c : TwoForm) :
    lowProductHighClass
        (g.basisPair ell m).1 (g.basisPair ell m).2
        (g.basisPair q c).1 (g.basisPair q c).2 =
      lowProductHighClass ell m q c := by
  cases g with
  | identity => rfl
  | swap =>
      simpa only [PlaneBasisChange.basisPair] using
        (lowProductHighClass_swap ell m q c).symm
  | rotateRight =>
      simpa only [PlaneBasisChange.basisPair] using
        lowProductHighClass_rotate_right ell m q c
  | rotateLeft =>
      simpa only [PlaneBasisChange.basisPair] using
        lowProductHighClass_rotate_left ell m q c
  | cycleRight =>
      calc
        lowProductHighClass m (ell + m) c (q + c) =
            lowProductHighClass (ell + m) m (q + c) c :=
          lowProductHighClass_swap m (ell + m) c (q + c)
        _ = lowProductHighClass ell m q c :=
          lowProductHighClass_rotate_left ell m q c
  | cycleLeft =>
      calc
        lowProductHighClass (ell + m) ell (q + c) q =
            lowProductHighClass ell (ell + m) q (q + c) :=
          lowProductHighClass_swap (ell + m) ell (q + c) q
        _ = lowProductHighClass ell m q c :=
          lowProductHighClass_rotate_right ell m q c

/-- Exact high equality supplies the literal local-versus-dependent cubic
equation in the one-rotation normal form. -/
theorem oneRotation_local_eq_dependent_exactCubic_of_highClass_eq
    (g k : PlaneBasisChange) (ell m ell' m' : LinearForm)
    (q c q' c' p q₀ t : TwoForm)
    (hg : g.basisPair q c = (p, q₀))
    (hk : k.basisPair q' c' = (p, q₀ + t))
    (hhigh : lowProductHighClass ell m q c =
      lowProductHighClass ell' m' q' c') :
    exactLowProductCubic
        (g.basisPair ell m).1
        ((g.basisPair ell m).2 + (k.basisPair ell' m').2) p t =
      exactLowProductCubic
        ((g.basisPair ell m).1 + (k.basisPair ell' m').1)
        (k.basisPair ell' m').2 0 (q₀ + t) := by
  have hchanged :
      lowProductHighClass
          (g.basisPair ell m).1 (g.basisPair ell m).2
          (g.basisPair q c).1 (g.basisPair q c).2 =
        lowProductHighClass
          (k.basisPair ell' m').1 (k.basisPair ell' m').2
          (k.basisPair q' c').1 (k.basisPair q' c').2 := by
    calc
      _ = lowProductHighClass ell m q c :=
        g.lowProductHighClass_basisPair ell m q c
      _ = lowProductHighClass ell' m' q' c' := hhigh
      _ = _ := (k.lowProductHighClass_basisPair ell' m' q' c').symm
  have hcubic := exactLowProductCubic_eq_of_highClass_eq
    _ _ _ _ _ _ _ _ hchanged
  rw [hg, hk] at hcubic
  have hrewired := exactLowProductCubic_twoProduct_rewire_of_eq
    (g.basisPair ell m).1 (g.basisPair ell m).2
    (k.basisPair ell' m').1 (k.basisPair ell' m').2
    p q₀ p (q₀ + t) hcubic
  have hcancel (z w : TwoForm) : z + (z + w) = w := by
    funext s
    rw [Pi.add_apply, Pi.add_apply, ← add_assoc,
      CharTwo.add_self_eq_zero, zero_add]
  have hself (z : TwoForm) : z + z = 0 := by
    funext s
    exact CharTwo.add_self_eq_zero (z s)
  simpa only [hcancel, hself] using hrewired

end
end N5
end UnrestrictedBooleanMul
