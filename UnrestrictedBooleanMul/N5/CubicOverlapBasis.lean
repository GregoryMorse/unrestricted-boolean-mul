import UnrestrictedBooleanMul.N5.CubicSemantic
import UnrestrictedBooleanMul.N5.EnvelopeBasisChange

/-!
# Cubic overlap under quadratic-plane basis changes

The literal cubic overlap of two pure quadratic Boolean ANFs is invariant
under every ordered basis change of their two-dimensional `F₂`-plane.  This
is the semantic correction needed to transport the normalized envelope
classifier back to actual Boolean products.

The proof is only Boolean idempotence and linearity; it does not enumerate
assignments, circuits, or quadratic forms.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem quadraticOverlapCubic_swap (q c : TwoForm) :
    quadraticOverlapCubic c q = quadraticOverlapCubic q c := by
  simp only [quadraticOverlapCubic, mul_comm]

theorem quadraticOverlapCubic_rotate_right (q c : TwoForm) :
    quadraticOverlapCubic q (q + c) = quadraticOverlapCubic q c := by
  have hadd : quadraticANFOfForm (q + c) =
      quadraticANFOfForm q + quadraticANFOfForm c :=
    map_add quadraticANFOfFormLinear q c
  rw [quadraticOverlapCubic, hadd, mul_add, N4.anf_mul_self, map_add,
    anfThreeProjectionTen_quadraticANFOfForm, zero_add]
  rfl

theorem quadraticOverlapCubic_rotate_left (q c : TwoForm) :
    quadraticOverlapCubic (q + c) c = quadraticOverlapCubic q c := by
  calc
    quadraticOverlapCubic (q + c) c =
        quadraticOverlapCubic c (q + c) :=
      quadraticOverlapCubic_swap c (q + c)
    _ = quadraticOverlapCubic c q := by
      rw [add_comm q c]
      exact quadraticOverlapCubic_rotate_right c q
    _ = quadraticOverlapCubic q c :=
      (quadraticOverlapCubic_swap c q).symm

/-- Literal cubic overlap depends only on the underlying unordered
two-dimensional quadratic plane, not on its ordered basis. -/
theorem quadraticOverlapCubic_basisPair
    (g : PlaneBasisChange) (q c : TwoForm) :
    quadraticOverlapCubic (g.basisPair q c).1
        (g.basisPair q c).2 = quadraticOverlapCubic q c := by
  cases g with
  | identity => rfl
  | swap => exact quadraticOverlapCubic_swap q c
  | rotateRight => exact quadraticOverlapCubic_rotate_right q c
  | rotateLeft => exact quadraticOverlapCubic_rotate_left q c
  | cycleRight =>
      change quadraticOverlapCubic c (q + c) = quadraticOverlapCubic q c
      calc
        quadraticOverlapCubic c (q + c) =
            quadraticOverlapCubic c q := by
              simpa [add_comm] using quadraticOverlapCubic_rotate_right c q
        _ = quadraticOverlapCubic q c :=
          (quadraticOverlapCubic_swap c q).symm
  | cycleLeft =>
      change quadraticOverlapCubic (q + c) q = quadraticOverlapCubic q c
      calc
        quadraticOverlapCubic (q + c) q =
            quadraticOverlapCubic q (q + c) :=
              quadraticOverlapCubic_swap q (q + c)
        _ = quadraticOverlapCubic q c :=
          quadraticOverlapCubic_rotate_right q c

end
end N5
end UnrestrictedBooleanMul
