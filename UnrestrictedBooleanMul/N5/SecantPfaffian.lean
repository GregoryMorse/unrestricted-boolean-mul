import UnrestrictedBooleanMul.N5.RankTwoSecants

/-!
# Pfaffian equations for a two-wedge secant

A sum of two decomposable alternating forms has rank at most four.  This
module records the corresponding six-coordinate Pfaffian equation in a form
suited to the local sparse-gift pivots.  The proof is a single exterior-
algebra polynomial identity and does not enumerate forms or matrices.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- Symmetric squarefree coefficient lookup, extended by zero on the
diagonal. -/
def ambientTwoCoeff (p : TwoForm) (i j : Fin 10) : F₂ :=
  if h : i = j then 0 else p (quadraticPair i j h)

@[simp] theorem ambientTwoCoeff_same (p : TwoForm) (i : Fin 10) :
    ambientTwoCoeff p i i = 0 := by
  simp [ambientTwoCoeff]

theorem ambientTwoCoeff_add (p q : TwoForm) (i j : Fin 10) :
    ambientTwoCoeff (p + q) i j =
      ambientTwoCoeff p i j + ambientTwoCoeff q i j := by
  by_cases h : i = j
  · simp [ambientTwoCoeff, h]
  · simp [ambientTwoCoeff, h]

theorem ambientTwoCoeff_squarefreeWedge
    (u v : LinearForm) (i j : Fin 10) :
    ambientTwoCoeff (squarefreeWedge u v) i j =
      u i * v j + u j * v i := by
  by_cases h : i = j
  · subst j
    simp [ambientTwoCoeff, CharTwo.add_self_eq_zero]
  · simp [ambientTwoCoeff, h, squarefreeWedge_pair]

/-- The characteristic-two Pfaffian on six selected ambient coordinates.
All fifteen perfect matchings occur with a plus sign. -/
def secantPfaffianValue (p : TwoForm)
    (i j k l m n : Fin 10) : F₂ :=
  ambientTwoCoeff p i j * ambientTwoCoeff p k l * ambientTwoCoeff p m n +
  ambientTwoCoeff p i j * ambientTwoCoeff p k m * ambientTwoCoeff p l n +
  ambientTwoCoeff p i j * ambientTwoCoeff p k n * ambientTwoCoeff p l m +
  ambientTwoCoeff p i k * ambientTwoCoeff p j l * ambientTwoCoeff p m n +
  ambientTwoCoeff p i k * ambientTwoCoeff p j m * ambientTwoCoeff p l n +
  ambientTwoCoeff p i k * ambientTwoCoeff p j n * ambientTwoCoeff p l m +
  ambientTwoCoeff p i l * ambientTwoCoeff p j k * ambientTwoCoeff p m n +
  ambientTwoCoeff p i l * ambientTwoCoeff p j m * ambientTwoCoeff p k n +
  ambientTwoCoeff p i l * ambientTwoCoeff p j n * ambientTwoCoeff p k m +
  ambientTwoCoeff p i m * ambientTwoCoeff p j k * ambientTwoCoeff p l n +
  ambientTwoCoeff p i m * ambientTwoCoeff p j l * ambientTwoCoeff p k n +
  ambientTwoCoeff p i m * ambientTwoCoeff p j n * ambientTwoCoeff p k l +
  ambientTwoCoeff p i n * ambientTwoCoeff p j k * ambientTwoCoeff p l m +
  ambientTwoCoeff p i n * ambientTwoCoeff p j l * ambientTwoCoeff p k m +
  ambientTwoCoeff p i n * ambientTwoCoeff p j m * ambientTwoCoeff p k l

set_option maxRecDepth 10000 in
/-- Exterior-algebra secant identity: every sum of two decomposable forms
satisfies every six-coordinate Pfaffian equation. -/
theorem secantPfaffianValue_two_wedges
    (u v x y : LinearForm) (i j k l m n : Fin 10) :
    secantPfaffianValue
      (squarefreeWedge u v + squarefreeWedge x y) i j k l m n = 0 := by
  simp only [secantPfaffianValue, ambientTwoCoeff_add,
    ambientTwoCoeff_squarefreeWedge]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2,
    N3Certificate.six_eq_zero_f2]

/-- Bundled form used by local secant candidates. -/
theorem secantPfaffianValue_eq_zero_of_two_decomposable
    (p : TwoForm) (i j k l m n : Fin 10)
    (hsecant : ∃ u v x y : LinearForm,
      p = squarefreeWedge u v + squarefreeWedge x y) :
    secantPfaffianValue p i j k l m n = 0 := by
  rcases hsecant with ⟨u, v, x, y, rfl⟩
  exact secantPfaffianValue_two_wedges u v x y i j k l m n

end

end N5
end UnrestrictedBooleanMul
