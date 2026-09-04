import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic

/-!
# Semantic equation base for `ZeroOneAligned`

This file computes the exact ANF meaning of every original history
equation used by either correction-return branch.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The aligned representative selected by rational-place and
`GL(2,F₂)` normalization. -/
structure ZeroOneAlignedNormalForm
    (p : ZeroOneOffAxisHistoryParameters) : Prop where
  ell1 : p.ell 1 = (0 : F₂)
  ell2 : p.ell 2 = (0 : F₂)
  ell4 : p.ell 4 = (0 : F₂)
  ell6 : p.ell 6 = (1 : F₂)
  ell7 : p.ell 7 = (0 : F₂)
  y1 : p.rightShift 1 = (1 : F₂)
  y2 : p.rightShift 2 = (0 : F₂)
  y4 : p.rightShift 4 = (0 : F₂)
  y6 : p.rightShift 6 = (0 : F₂)
  y7 : p.rightShift 7 = (0 : F₂)

/-- Ordered union of the original history equations used by `ZeroOneAligned`. -/
def zeroOneAlignedBaseConstraint (v : Fin 71 → F₂) : Fin 34 → F₂ :=
  ![
    -- return-high-0x023
    v 21,
    -- return-high-0x025
    v 22,
    -- return-high-0x029
    v 23,
    -- return-high-0x031
    v 24,
    -- return-high-0x061
    v 26,
    -- return-high-0x0a1
    v 27,
    -- return-high-0x121
    v 28,
    -- return-high-0x221
    v 29,
    -- product-high-0x023
    v 1 + v 1 * v 10 + v 0 * v 11 + v 1 * v 11 + v 5 * v 11 + v 1 * v 15 + v 1 * v 40 + v 1 * v 41 + v 5 * v 11 * v 41 + v 1 * v 15 * v 41 + v 0 * v 42 + v 1 * v 42 + v 5 * v 42 + v 5 * v 10 * v 42 + v 0 * v 15 * v 42 + v 1 * v 46 + v 1 * v 10 * v 46 + v 0 * v 11 * v 46 + v 53 + v 42 * v 62 + v 63 + v 41 * v 63 + v 42 * v 63 + v 65 + v 41 * v 65 + v 66 + v 41 * v 66 + v 11 * v 20 * v 70 + v 21 * v 70 + v 10 * v 21 * v 70 + v 11 * v 21 * v 70 + v 15 * v 21 * v 70 + v 11 * v 25 * v 70 + v 1 * v 30 * v 70 + v 21 * v 30 * v 70 + v 0 * v 31 * v 70 + v 1 * v 31 * v 70 + v 5 * v 31 * v 70 + v 20 * v 31 * v 70 + v 21 * v 31 * v 70 + v 25 * v 31 * v 70 + v 1 * v 35 * v 70 + v 21 * v 35 * v 70 + v 21 * v 40 * v 70 + v 21 * v 41 * v 70 + v 15 * v 21 * v 41 * v 70 + v 11 * v 25 * v 41 * v 70 + v 5 * v 31 * v 41 * v 70 + v 25 * v 31 * v 41 * v 70 + v 1 * v 35 * v 41 * v 70 + v 21 * v 35 * v 41 * v 70 + v 20 * v 42 * v 70 + v 15 * v 20 * v 42 * v 70 + v 21 * v 42 * v 70 + v 25 * v 42 * v 70 + v 10 * v 25 * v 42 * v 70 + v 5 * v 30 * v 42 * v 70 + v 25 * v 30 * v 42 * v 70 + v 0 * v 35 * v 42 * v 70 + v 20 * v 35 * v 42 * v 70 + v 11 * v 20 * v 46 * v 70 + v 21 * v 46 * v 70 + v 10 * v 21 * v 46 * v 70 + v 1 * v 30 * v 46 * v 70 + v 21 * v 30 * v 46 * v 70 + v 0 * v 31 * v 46 * v 70 + v 20 * v 31 * v 46 * v 70,
    -- product-high-0x025
    v 2 + v 2 * v 10 + v 0 * v 12 + v 2 * v 12 + v 5 * v 12 + v 2 * v 15 + v 2 * v 40 + v 2 * v 41 + v 5 * v 12 * v 41 + v 2 * v 15 * v 41 + v 0 * v 43 + v 2 * v 43 + v 5 * v 43 + v 5 * v 10 * v 43 + v 0 * v 15 * v 43 + v 2 * v 46 + v 2 * v 10 * v 46 + v 0 * v 12 * v 46 + v 54 + v 43 * v 62 + v 63 + v 41 * v 63 + v 43 * v 63 + v 68 + v 41 * v 68 + v 12 * v 20 * v 70 + v 22 * v 70 + v 10 * v 22 * v 70 + v 12 * v 22 * v 70 + v 15 * v 22 * v 70 + v 12 * v 25 * v 70 + v 2 * v 30 * v 70 + v 22 * v 30 * v 70 + v 0 * v 32 * v 70 + v 2 * v 32 * v 70 + v 5 * v 32 * v 70 + v 20 * v 32 * v 70 + v 22 * v 32 * v 70 + v 25 * v 32 * v 70 + v 2 * v 35 * v 70 + v 22 * v 35 * v 70 + v 22 * v 40 * v 70 + v 22 * v 41 * v 70 + v 15 * v 22 * v 41 * v 70 + v 12 * v 25 * v 41 * v 70 + v 5 * v 32 * v 41 * v 70 + v 25 * v 32 * v 41 * v 70 + v 2 * v 35 * v 41 * v 70 + v 22 * v 35 * v 41 * v 70 + v 20 * v 43 * v 70 + v 15 * v 20 * v 43 * v 70 + v 22 * v 43 * v 70 + v 25 * v 43 * v 70 + v 10 * v 25 * v 43 * v 70 + v 5 * v 30 * v 43 * v 70 + v 25 * v 30 * v 43 * v 70 + v 0 * v 35 * v 43 * v 70 + v 20 * v 35 * v 43 * v 70 + v 12 * v 20 * v 46 * v 70 + v 22 * v 46 * v 70 + v 10 * v 22 * v 46 * v 70 + v 2 * v 30 * v 46 * v 70 + v 22 * v 30 * v 46 * v 70 + v 0 * v 32 * v 46 * v 70 + v 20 * v 32 * v 46 * v 70,
    -- product-high-0x043
    v 6 * v 11 * v 41 + v 1 * v 16 * v 41 + v 6 * v 10 * v 42 + v 0 * v 16 * v 42 + v 1 * v 10 * v 47 + v 0 * v 11 * v 47 + v 41 * v 63 + v 42 * v 63 + v 42 * v 65 + v 42 * v 66 + v 41 * v 68 + v 16 * v 21 * v 41 * v 70 + v 11 * v 26 * v 41 * v 70 + v 6 * v 31 * v 41 * v 70 + v 26 * v 31 * v 41 * v 70 + v 1 * v 36 * v 41 * v 70 + v 21 * v 36 * v 41 * v 70 + v 16 * v 20 * v 42 * v 70 + v 10 * v 26 * v 42 * v 70 + v 6 * v 30 * v 42 * v 70 + v 26 * v 30 * v 42 * v 70 + v 0 * v 36 * v 42 * v 70 + v 20 * v 36 * v 42 * v 70 + v 11 * v 20 * v 47 * v 70 + v 10 * v 21 * v 47 * v 70 + v 1 * v 30 * v 47 * v 70 + v 21 * v 30 * v 47 * v 70 + v 0 * v 31 * v 47 * v 70 + v 20 * v 31 * v 47 * v 70,
    -- product-high-0x061
    v 6 + v 6 * v 10 + v 6 * v 15 + v 0 * v 16 + v 5 * v 16 + v 6 * v 16 + v 6 * v 40 + v 6 * v 41 + v 6 * v 15 * v 41 + v 5 * v 16 * v 41 + v 6 * v 46 + v 6 * v 10 * v 46 + v 0 * v 16 * v 46 + v 0 * v 47 + v 5 * v 47 + v 6 * v 47 + v 5 * v 10 * v 47 + v 0 * v 15 * v 47 + v 58 + v 47 * v 62 + v 63 + v 46 * v 63 + v 47 * v 63 + v 65 + v 46 * v 65 + v 66 + v 46 * v 66 + v 16 * v 20 * v 70 + v 16 * v 25 * v 70 + v 26 * v 70 + v 10 * v 26 * v 70 + v 15 * v 26 * v 70 + v 16 * v 26 * v 70 + v 6 * v 30 * v 70 + v 26 * v 30 * v 70 + v 6 * v 35 * v 70 + v 26 * v 35 * v 70 + v 0 * v 36 * v 70 + v 5 * v 36 * v 70 + v 6 * v 36 * v 70 + v 20 * v 36 * v 70 + v 25 * v 36 * v 70 + v 26 * v 36 * v 70 + v 26 * v 40 * v 70 + v 16 * v 25 * v 41 * v 70 + v 26 * v 41 * v 70 + v 15 * v 26 * v 41 * v 70 + v 6 * v 35 * v 41 * v 70 + v 26 * v 35 * v 41 * v 70 + v 5 * v 36 * v 41 * v 70 + v 25 * v 36 * v 41 * v 70 + v 16 * v 20 * v 46 * v 70 + v 26 * v 46 * v 70 + v 10 * v 26 * v 46 * v 70 + v 6 * v 30 * v 46 * v 70 + v 26 * v 30 * v 46 * v 70 + v 0 * v 36 * v 46 * v 70 + v 20 * v 36 * v 46 * v 70 + v 20 * v 47 * v 70 + v 15 * v 20 * v 47 * v 70 + v 25 * v 47 * v 70 + v 10 * v 25 * v 47 * v 70 + v 26 * v 47 * v 70 + v 5 * v 30 * v 47 * v 70 + v 25 * v 30 * v 47 * v 70 + v 0 * v 35 * v 47 * v 70 + v 20 * v 35 * v 47 * v 70,
    -- product-high-0x062
    v 6 * v 15 * v 42 + v 5 * v 16 * v 42 + v 6 * v 11 * v 46 + v 1 * v 16 * v 46 + v 5 * v 11 * v 47 + v 1 * v 15 * v 47 + v 46 * v 63 + v 47 * v 63 + v 47 * v 65 + v 47 * v 66 + v 46 * v 68 + v 16 * v 25 * v 42 * v 70 + v 15 * v 26 * v 42 * v 70 + v 6 * v 35 * v 42 * v 70 + v 26 * v 35 * v 42 * v 70 + v 5 * v 36 * v 42 * v 70 + v 25 * v 36 * v 42 * v 70 + v 16 * v 21 * v 46 * v 70 + v 11 * v 26 * v 46 * v 70 + v 6 * v 31 * v 46 * v 70 + v 26 * v 31 * v 46 * v 70 + v 1 * v 36 * v 46 * v 70 + v 21 * v 36 * v 46 * v 70 + v 15 * v 21 * v 47 * v 70 + v 11 * v 25 * v 47 * v 70 + v 5 * v 31 * v 47 * v 70 + v 25 * v 31 * v 47 * v 70 + v 1 * v 35 * v 47 * v 70 + v 21 * v 35 * v 47 * v 70,
    -- product-high-0x063
    v 6 * v 11 + v 1 * v 16 + v 6 * v 42 + v 1 * v 47 + v 63 + v 68 + v 16 * v 21 * v 70 + v 11 * v 26 * v 70 + v 6 * v 31 * v 70 + v 26 * v 31 * v 70 + v 1 * v 36 * v 70 + v 21 * v 36 * v 70 + v 26 * v 42 * v 70 + v 21 * v 47 * v 70,
    -- product-high-0x064
    v 6 * v 15 * v 43 + v 5 * v 16 * v 43 + v 6 * v 12 * v 46 + v 2 * v 16 * v 46 + v 5 * v 12 * v 47 + v 2 * v 15 * v 47 + v 46 * v 63 + v 47 * v 63 + v 46 * v 66 + v 47 * v 68 + v 46 * v 69 + v 16 * v 25 * v 43 * v 70 + v 15 * v 26 * v 43 * v 70 + v 6 * v 35 * v 43 * v 70 + v 26 * v 35 * v 43 * v 70 + v 5 * v 36 * v 43 * v 70 + v 25 * v 36 * v 43 * v 70 + v 16 * v 22 * v 46 * v 70 + v 12 * v 26 * v 46 * v 70 + v 6 * v 32 * v 46 * v 70 + v 26 * v 32 * v 46 * v 70 + v 2 * v 36 * v 46 * v 70 + v 22 * v 36 * v 46 * v 70 + v 15 * v 22 * v 47 * v 70 + v 12 * v 25 * v 47 * v 70 + v 5 * v 32 * v 47 * v 70 + v 25 * v 32 * v 47 * v 70 + v 2 * v 35 * v 47 * v 70 + v 22 * v 35 * v 47 * v 70,
    -- product-high-0x065
    v 6 * v 12 + v 2 * v 16 + v 6 * v 43 + v 2 * v 47 + v 63 + v 66 + v 69 + v 16 * v 22 * v 70 + v 12 * v 26 * v 70 + v 6 * v 32 * v 70 + v 26 * v 32 * v 70 + v 2 * v 36 * v 70 + v 22 * v 36 * v 70 + v 26 * v 43 * v 70 + v 22 * v 47 * v 70,
    -- product-high-0x071
    v 6 * v 14 + v 4 * v 16 + v 6 * v 45 + v 4 * v 47 + v 63 + v 66 + v 68 + v 16 * v 24 * v 70 + v 14 * v 26 * v 70 + v 6 * v 34 * v 70 + v 26 * v 34 * v 70 + v 4 * v 36 * v 70 + v 24 * v 36 * v 70 + v 26 * v 45 * v 70 + v 24 * v 47 * v 70,
    -- product-high-0x0a1
    v 7 + v 7 * v 10 + v 7 * v 15 + v 0 * v 17 + v 5 * v 17 + v 7 * v 17 + v 7 * v 40 + v 7 * v 41 + v 7 * v 15 * v 41 + v 5 * v 17 * v 41 + v 7 * v 46 + v 7 * v 10 * v 46 + v 0 * v 17 * v 46 + v 0 * v 48 + v 5 * v 48 + v 7 * v 48 + v 5 * v 10 * v 48 + v 0 * v 15 * v 48 + v 59 + v 48 * v 62 + v 63 + v 46 * v 63 + v 48 * v 63 + v 68 + v 46 * v 68 + v 17 * v 20 * v 70 + v 17 * v 25 * v 70 + v 27 * v 70 + v 10 * v 27 * v 70 + v 15 * v 27 * v 70 + v 17 * v 27 * v 70 + v 7 * v 30 * v 70 + v 27 * v 30 * v 70 + v 7 * v 35 * v 70 + v 27 * v 35 * v 70 + v 0 * v 37 * v 70 + v 5 * v 37 * v 70 + v 7 * v 37 * v 70 + v 20 * v 37 * v 70 + v 25 * v 37 * v 70 + v 27 * v 37 * v 70 + v 27 * v 40 * v 70 + v 17 * v 25 * v 41 * v 70 + v 27 * v 41 * v 70 + v 15 * v 27 * v 41 * v 70 + v 7 * v 35 * v 41 * v 70 + v 27 * v 35 * v 41 * v 70 + v 5 * v 37 * v 41 * v 70 + v 25 * v 37 * v 41 * v 70 + v 17 * v 20 * v 46 * v 70 + v 27 * v 46 * v 70 + v 10 * v 27 * v 46 * v 70 + v 7 * v 30 * v 46 * v 70 + v 27 * v 30 * v 46 * v 70 + v 0 * v 37 * v 46 * v 70 + v 20 * v 37 * v 46 * v 70 + v 20 * v 48 * v 70 + v 15 * v 20 * v 48 * v 70 + v 25 * v 48 * v 70 + v 10 * v 25 * v 48 * v 70 + v 27 * v 48 * v 70 + v 5 * v 30 * v 48 * v 70 + v 25 * v 30 * v 48 * v 70 + v 0 * v 35 * v 48 * v 70 + v 20 * v 35 * v 48 * v 70,
    -- product-high-0x0a2
    v 7 * v 15 * v 42 + v 5 * v 17 * v 42 + v 7 * v 11 * v 46 + v 1 * v 17 * v 46 + v 5 * v 11 * v 48 + v 1 * v 15 * v 48 + v 46 * v 63 + v 48 * v 63 + v 48 * v 65 + v 46 * v 66 + v 48 * v 66 + v 46 * v 69 + v 17 * v 25 * v 42 * v 70 + v 15 * v 27 * v 42 * v 70 + v 7 * v 35 * v 42 * v 70 + v 27 * v 35 * v 42 * v 70 + v 5 * v 37 * v 42 * v 70 + v 25 * v 37 * v 42 * v 70 + v 17 * v 21 * v 46 * v 70 + v 11 * v 27 * v 46 * v 70 + v 7 * v 31 * v 46 * v 70 + v 27 * v 31 * v 46 * v 70 + v 1 * v 37 * v 46 * v 70 + v 21 * v 37 * v 46 * v 70 + v 15 * v 21 * v 48 * v 70 + v 11 * v 25 * v 48 * v 70 + v 5 * v 31 * v 48 * v 70 + v 25 * v 31 * v 48 * v 70 + v 1 * v 35 * v 48 * v 70 + v 21 * v 35 * v 48 * v 70,
    -- product-high-0x0a3
    v 7 * v 11 + v 1 * v 17 + v 7 * v 42 + v 1 * v 48 + v 63 + v 66 + v 69 + v 17 * v 21 * v 70 + v 11 * v 27 * v 70 + v 7 * v 31 * v 70 + v 27 * v 31 * v 70 + v 1 * v 37 * v 70 + v 21 * v 37 * v 70 + v 27 * v 42 * v 70 + v 21 * v 48 * v 70,
    -- product-high-0x0a5
    v 7 * v 12 + v 2 * v 17 + v 7 * v 43 + v 2 * v 48 + v 63 + v 17 * v 22 * v 70 + v 12 * v 27 * v 70 + v 7 * v 32 * v 70 + v 27 * v 32 * v 70 + v 2 * v 37 * v 70 + v 22 * v 37 * v 70 + v 27 * v 43 * v 70 + v 22 * v 48 * v 70,
    -- product-high-0x0a9
    v 7 * v 13 + v 3 * v 17 + v 7 * v 44 + v 3 * v 48 + v 63 + v 66 + v 68 + v 17 * v 23 * v 70 + v 13 * v 27 * v 70 + v 7 * v 33 * v 70 + v 27 * v 33 * v 70 + v 3 * v 37 * v 70 + v 23 * v 37 * v 70 + v 27 * v 44 * v 70 + v 23 * v 48 * v 70,
    -- product-high-0x0b1
    v 7 * v 14 + v 4 * v 17 + v 7 * v 45 + v 4 * v 48 + v 63 + v 69 + v 17 * v 24 * v 70 + v 14 * v 27 * v 70 + v 7 * v 34 * v 70 + v 27 * v 34 * v 70 + v 4 * v 37 * v 70 + v 24 * v 37 * v 70 + v 27 * v 45 * v 70 + v 24 * v 48 * v 70,
    -- product-high-0x0c1
    v 7 * v 16 * v 41 + v 6 * v 17 * v 41 + v 7 * v 10 * v 47 + v 0 * v 17 * v 47 + v 6 * v 10 * v 48 + v 0 * v 16 * v 48 + v 47 * v 63 + v 48 * v 63 + v 48 * v 65 + v 48 * v 66 + v 47 * v 68 + v 17 * v 26 * v 41 * v 70 + v 16 * v 27 * v 41 * v 70 + v 7 * v 36 * v 41 * v 70 + v 27 * v 36 * v 41 * v 70 + v 6 * v 37 * v 41 * v 70 + v 26 * v 37 * v 41 * v 70 + v 17 * v 20 * v 47 * v 70 + v 10 * v 27 * v 47 * v 70 + v 7 * v 30 * v 47 * v 70 + v 27 * v 30 * v 47 * v 70 + v 0 * v 37 * v 47 * v 70 + v 20 * v 37 * v 47 * v 70 + v 16 * v 20 * v 48 * v 70 + v 10 * v 26 * v 48 * v 70 + v 6 * v 30 * v 48 * v 70 + v 26 * v 30 * v 48 * v 70 + v 0 * v 36 * v 48 * v 70 + v 20 * v 36 * v 48 * v 70,
    -- product-high-0x0e0
    v 7 * v 16 * v 46 + v 6 * v 17 * v 46 + v 7 * v 15 * v 47 + v 5 * v 17 * v 47 + v 6 * v 15 * v 48 + v 5 * v 16 * v 48 + v 17 * v 26 * v 46 * v 70 + v 16 * v 27 * v 46 * v 70 + v 7 * v 36 * v 46 * v 70 + v 27 * v 36 * v 46 * v 70 + v 6 * v 37 * v 46 * v 70 + v 26 * v 37 * v 46 * v 70 + v 17 * v 25 * v 47 * v 70 + v 15 * v 27 * v 47 * v 70 + v 7 * v 35 * v 47 * v 70 + v 27 * v 35 * v 47 * v 70 + v 5 * v 37 * v 47 * v 70 + v 25 * v 37 * v 47 * v 70 + v 16 * v 25 * v 48 * v 70 + v 15 * v 26 * v 48 * v 70 + v 6 * v 35 * v 48 * v 70 + v 26 * v 35 * v 48 * v 70 + v 5 * v 36 * v 48 * v 70 + v 25 * v 36 * v 48 * v 70,
    -- product-high-0x0e1
    v 7 * v 16 + v 6 * v 17 + v 7 * v 47 + v 6 * v 48 + v 17 * v 26 * v 70 + v 16 * v 27 * v 70 + v 7 * v 36 * v 70 + v 27 * v 36 * v 70 + v 6 * v 37 * v 70 + v 26 * v 37 * v 70 + v 27 * v 47 * v 70 + v 26 * v 48 * v 70,
    -- product-high-0x131
    v 8 * v 14 + v 4 * v 18 + v 8 * v 45 + v 4 * v 49 + v 63 + v 66 + v 67 + v 18 * v 24 * v 70 + v 14 * v 28 * v 70 + v 8 * v 34 * v 70 + v 28 * v 34 * v 70 + v 4 * v 38 * v 70 + v 24 * v 38 * v 70 + v 28 * v 45 * v 70 + v 24 * v 49 * v 70,
    -- product-high-0x231
    v 9 * v 14 + v 4 * v 19 + v 9 * v 45 + v 4 * v 50 + v 63 + v 64 + v 19 * v 24 * v 70 + v 14 * v 29 * v 70 + v 9 * v 34 * v 70 + v 29 * v 34 * v 70 + v 4 * v 39 * v 70 + v 24 * v 39 * v 70 + v 29 * v 45 * v 70 + v 24 * v 50 * v 70,
    -- quotient-6
    v 17 * v 20 + v 15 * v 22 + v 12 * v 25 + v 10 * v 27 + v 7 * v 30 + v 27 * v 30 + v 5 * v 32 + v 25 * v 32 + v 2 * v 35 + v 22 * v 35 + v 0 * v 37 + v 20 * v 37 + v 7 * v 10 * v 40 + v 5 * v 12 * v 40 + v 2 * v 15 * v 40 + v 0 * v 17 * v 40 + v 7 * v 10 * v 41 + v 0 * v 17 * v 41 + v 7 * v 17 * v 41 + v 5 * v 12 * v 43 + v 2 * v 15 * v 43 + v 5 * v 15 * v 43 + v 2 * v 12 * v 46 + v 5 * v 12 * v 46 + v 2 * v 15 * v 46 + v 0 * v 10 * v 48 + v 7 * v 10 * v 48 + v 0 * v 17 * v 48 + v 48 * v 52 + v 46 * v 54 + v 43 * v 57 + v 41 * v 59 + v 41 * v 63 + v 43 * v 63 + v 46 * v 63 + v 48 * v 63 + v 41 * v 68 + v 43 * v 68 + v 46 * v 68 + v 48 * v 68 + v 17 * v 20 * v 40 * v 70 + v 15 * v 22 * v 40 * v 70 + v 12 * v 25 * v 40 * v 70 + v 10 * v 27 * v 40 * v 70 + v 7 * v 30 * v 40 * v 70 + v 27 * v 30 * v 40 * v 70 + v 5 * v 32 * v 40 * v 70 + v 25 * v 32 * v 40 * v 70 + v 2 * v 35 * v 40 * v 70 + v 22 * v 35 * v 40 * v 70 + v 0 * v 37 * v 40 * v 70 + v 20 * v 37 * v 40 * v 70 + v 17 * v 20 * v 41 * v 70 + v 10 * v 27 * v 41 * v 70 + v 17 * v 27 * v 41 * v 70 + v 7 * v 30 * v 41 * v 70 + v 27 * v 30 * v 41 * v 70 + v 0 * v 37 * v 41 * v 70 + v 7 * v 37 * v 41 * v 70 + v 20 * v 37 * v 41 * v 70 + v 27 * v 37 * v 41 * v 70 + v 15 * v 22 * v 43 * v 70 + v 12 * v 25 * v 43 * v 70 + v 15 * v 25 * v 43 * v 70 + v 5 * v 32 * v 43 * v 70 + v 25 * v 32 * v 43 * v 70 + v 2 * v 35 * v 43 * v 70 + v 5 * v 35 * v 43 * v 70 + v 22 * v 35 * v 43 * v 70 + v 25 * v 35 * v 43 * v 70 + v 12 * v 22 * v 46 * v 70 + v 15 * v 22 * v 46 * v 70 + v 12 * v 25 * v 46 * v 70 + v 2 * v 32 * v 46 * v 70 + v 5 * v 32 * v 46 * v 70 + v 22 * v 32 * v 46 * v 70 + v 25 * v 32 * v 46 * v 70 + v 2 * v 35 * v 46 * v 70 + v 22 * v 35 * v 46 * v 70 + v 10 * v 20 * v 48 * v 70 + v 17 * v 20 * v 48 * v 70 + v 10 * v 27 * v 48 * v 70 + v 0 * v 30 * v 48 * v 70 + v 7 * v 30 * v 48 * v 70 + v 20 * v 30 * v 48 * v 70 + v 27 * v 30 * v 48 * v 70 + v 0 * v 37 * v 48 * v 70 + v 20 * v 37 * v 48 * v 70,
    -- quotient-13
    v 16 * v 21 + v 15 * v 22 + v 12 * v 25 + v 11 * v 26 + v 6 * v 31 + v 26 * v 31 + v 5 * v 32 + v 25 * v 32 + v 2 * v 35 + v 22 * v 35 + v 1 * v 36 + v 21 * v 36 + v 6 * v 11 * v 40 + v 5 * v 12 * v 40 + v 2 * v 15 * v 40 + v 1 * v 16 * v 40 + v 6 * v 11 * v 42 + v 1 * v 16 * v 42 + v 6 * v 16 * v 42 + v 5 * v 12 * v 43 + v 2 * v 15 * v 43 + v 5 * v 15 * v 43 + v 2 * v 12 * v 46 + v 5 * v 12 * v 46 + v 2 * v 15 * v 46 + v 1 * v 11 * v 47 + v 6 * v 11 * v 47 + v 1 * v 16 * v 47 + v 47 * v 53 + v 46 * v 54 + v 43 * v 57 + v 42 * v 58 + v 42 * v 63 + v 43 * v 63 + v 46 * v 63 + v 47 * v 63 + v 42 * v 68 + v 43 * v 68 + v 46 * v 68 + v 47 * v 68 + v 16 * v 21 * v 40 * v 70 + v 15 * v 22 * v 40 * v 70 + v 12 * v 25 * v 40 * v 70 + v 11 * v 26 * v 40 * v 70 + v 6 * v 31 * v 40 * v 70 + v 26 * v 31 * v 40 * v 70 + v 5 * v 32 * v 40 * v 70 + v 25 * v 32 * v 40 * v 70 + v 2 * v 35 * v 40 * v 70 + v 22 * v 35 * v 40 * v 70 + v 1 * v 36 * v 40 * v 70 + v 21 * v 36 * v 40 * v 70 + v 16 * v 21 * v 42 * v 70 + v 11 * v 26 * v 42 * v 70 + v 16 * v 26 * v 42 * v 70 + v 6 * v 31 * v 42 * v 70 + v 26 * v 31 * v 42 * v 70 + v 1 * v 36 * v 42 * v 70 + v 6 * v 36 * v 42 * v 70 + v 21 * v 36 * v 42 * v 70 + v 26 * v 36 * v 42 * v 70 + v 15 * v 22 * v 43 * v 70 + v 12 * v 25 * v 43 * v 70 + v 15 * v 25 * v 43 * v 70 + v 5 * v 32 * v 43 * v 70 + v 25 * v 32 * v 43 * v 70 + v 2 * v 35 * v 43 * v 70 + v 5 * v 35 * v 43 * v 70 + v 22 * v 35 * v 43 * v 70 + v 25 * v 35 * v 43 * v 70 + v 12 * v 22 * v 46 * v 70 + v 15 * v 22 * v 46 * v 70 + v 12 * v 25 * v 46 * v 70 + v 2 * v 32 * v 46 * v 70 + v 5 * v 32 * v 46 * v 70 + v 22 * v 32 * v 46 * v 70 + v 25 * v 32 * v 46 * v 70 + v 2 * v 35 * v 46 * v 70 + v 22 * v 35 * v 46 * v 70 + v 11 * v 21 * v 47 * v 70 + v 16 * v 21 * v 47 * v 70 + v 11 * v 26 * v 47 * v 70 + v 1 * v 31 * v 47 * v 70 + v 6 * v 31 * v 47 * v 70 + v 21 * v 31 * v 47 * v 70 + v 26 * v 31 * v 47 * v 70 + v 1 * v 36 * v 47 * v 70 + v 21 * v 36 * v 47 * v 70,
    -- quotient-14
    v 17 * v 21 + v 15 * v 23 + v 13 * v 25 + v 11 * v 27 + v 7 * v 31 + v 27 * v 31 + v 5 * v 33 + v 25 * v 33 + v 3 * v 35 + v 23 * v 35 + v 1 * v 37 + v 21 * v 37 + v 7 * v 11 * v 40 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 1 * v 17 * v 40 + v 7 * v 11 * v 42 + v 1 * v 17 * v 42 + v 7 * v 17 * v 42 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 1 * v 11 * v 48 + v 7 * v 11 * v 48 + v 1 * v 17 * v 48 + v 48 * v 53 + v 46 * v 55 + v 44 * v 57 + v 42 * v 59 + v 42 * v 63 + v 44 * v 63 + v 46 * v 63 + v 48 * v 63 + v 42 * v 66 + v 44 * v 66 + v 46 * v 66 + v 48 * v 66 + v 42 * v 69 + v 44 * v 69 + v 46 * v 69 + v 48 * v 69 + v 17 * v 21 * v 40 * v 70 + v 15 * v 23 * v 40 * v 70 + v 13 * v 25 * v 40 * v 70 + v 11 * v 27 * v 40 * v 70 + v 7 * v 31 * v 40 * v 70 + v 27 * v 31 * v 40 * v 70 + v 5 * v 33 * v 40 * v 70 + v 25 * v 33 * v 40 * v 70 + v 3 * v 35 * v 40 * v 70 + v 23 * v 35 * v 40 * v 70 + v 1 * v 37 * v 40 * v 70 + v 21 * v 37 * v 40 * v 70 + v 17 * v 21 * v 42 * v 70 + v 11 * v 27 * v 42 * v 70 + v 17 * v 27 * v 42 * v 70 + v 7 * v 31 * v 42 * v 70 + v 27 * v 31 * v 42 * v 70 + v 1 * v 37 * v 42 * v 70 + v 7 * v 37 * v 42 * v 70 + v 21 * v 37 * v 42 * v 70 + v 27 * v 37 * v 42 * v 70 + v 15 * v 23 * v 44 * v 70 + v 13 * v 25 * v 44 * v 70 + v 15 * v 25 * v 44 * v 70 + v 5 * v 33 * v 44 * v 70 + v 25 * v 33 * v 44 * v 70 + v 3 * v 35 * v 44 * v 70 + v 5 * v 35 * v 44 * v 70 + v 23 * v 35 * v 44 * v 70 + v 25 * v 35 * v 44 * v 70 + v 13 * v 23 * v 46 * v 70 + v 15 * v 23 * v 46 * v 70 + v 13 * v 25 * v 46 * v 70 + v 3 * v 33 * v 46 * v 70 + v 5 * v 33 * v 46 * v 70 + v 23 * v 33 * v 46 * v 70 + v 25 * v 33 * v 46 * v 70 + v 3 * v 35 * v 46 * v 70 + v 23 * v 35 * v 46 * v 70 + v 11 * v 21 * v 48 * v 70 + v 17 * v 21 * v 48 * v 70 + v 11 * v 27 * v 48 * v 70 + v 1 * v 31 * v 48 * v 70 + v 7 * v 31 * v 48 * v 70 + v 21 * v 31 * v 48 * v 70 + v 27 * v 31 * v 48 * v 70 + v 1 * v 37 * v 48 * v 70 + v 21 * v 37 * v 48 * v 70,
    -- quotient-20
    v 16 * v 22 + v 15 * v 23 + v 13 * v 25 + v 12 * v 26 + v 6 * v 32 + v 26 * v 32 + v 5 * v 33 + v 25 * v 33 + v 3 * v 35 + v 23 * v 35 + v 2 * v 36 + v 22 * v 36 + v 6 * v 12 * v 40 + v 5 * v 13 * v 40 + v 3 * v 15 * v 40 + v 2 * v 16 * v 40 + v 6 * v 12 * v 43 + v 2 * v 16 * v 43 + v 6 * v 16 * v 43 + v 5 * v 13 * v 44 + v 3 * v 15 * v 44 + v 5 * v 15 * v 44 + v 3 * v 13 * v 46 + v 5 * v 13 * v 46 + v 3 * v 15 * v 46 + v 2 * v 12 * v 47 + v 6 * v 12 * v 47 + v 2 * v 16 * v 47 + v 47 * v 54 + v 46 * v 55 + v 44 * v 57 + v 43 * v 58 + v 43 * v 63 + v 44 * v 63 + v 46 * v 63 + v 47 * v 63 + v 43 * v 66 + v 44 * v 66 + v 46 * v 66 + v 47 * v 66 + v 43 * v 69 + v 44 * v 69 + v 46 * v 69 + v 47 * v 69 + v 16 * v 22 * v 40 * v 70 + v 15 * v 23 * v 40 * v 70 + v 13 * v 25 * v 40 * v 70 + v 12 * v 26 * v 40 * v 70 + v 6 * v 32 * v 40 * v 70 + v 26 * v 32 * v 40 * v 70 + v 5 * v 33 * v 40 * v 70 + v 25 * v 33 * v 40 * v 70 + v 3 * v 35 * v 40 * v 70 + v 23 * v 35 * v 40 * v 70 + v 2 * v 36 * v 40 * v 70 + v 22 * v 36 * v 40 * v 70 + v 16 * v 22 * v 43 * v 70 + v 12 * v 26 * v 43 * v 70 + v 16 * v 26 * v 43 * v 70 + v 6 * v 32 * v 43 * v 70 + v 26 * v 32 * v 43 * v 70 + v 2 * v 36 * v 43 * v 70 + v 6 * v 36 * v 43 * v 70 + v 22 * v 36 * v 43 * v 70 + v 26 * v 36 * v 43 * v 70 + v 15 * v 23 * v 44 * v 70 + v 13 * v 25 * v 44 * v 70 + v 15 * v 25 * v 44 * v 70 + v 5 * v 33 * v 44 * v 70 + v 25 * v 33 * v 44 * v 70 + v 3 * v 35 * v 44 * v 70 + v 5 * v 35 * v 44 * v 70 + v 23 * v 35 * v 44 * v 70 + v 25 * v 35 * v 44 * v 70 + v 13 * v 23 * v 46 * v 70 + v 15 * v 23 * v 46 * v 70 + v 13 * v 25 * v 46 * v 70 + v 3 * v 33 * v 46 * v 70 + v 5 * v 33 * v 46 * v 70 + v 23 * v 33 * v 46 * v 70 + v 25 * v 33 * v 46 * v 70 + v 3 * v 35 * v 46 * v 70 + v 23 * v 35 * v 46 * v 70 + v 12 * v 22 * v 47 * v 70 + v 16 * v 22 * v 47 * v 70 + v 12 * v 26 * v 47 * v 70 + v 2 * v 32 * v 47 * v 70 + v 6 * v 32 * v 47 * v 70 + v 22 * v 32 * v 47 * v 70 + v 26 * v 32 * v 47 * v 70 + v 2 * v 36 * v 47 * v 70 + v 22 * v 36 * v 47 * v 70,
    -- quotient-36
    v 17 * v 25 + v 15 * v 27 + v 7 * v 35 + v 27 * v 35 + v 5 * v 37 + v 25 * v 37 + v 7 * v 15 * v 40 + v 5 * v 17 * v 40 + v 7 * v 15 * v 46 + v 5 * v 17 * v 46 + v 7 * v 17 * v 46 + v 5 * v 15 * v 48 + v 7 * v 15 * v 48 + v 5 * v 17 * v 48 + v 48 * v 57 + v 46 * v 59 + v 17 * v 25 * v 40 * v 70 + v 15 * v 27 * v 40 * v 70 + v 7 * v 35 * v 40 * v 70 + v 27 * v 35 * v 40 * v 70 + v 5 * v 37 * v 40 * v 70 + v 25 * v 37 * v 40 * v 70 + v 17 * v 25 * v 46 * v 70 + v 15 * v 27 * v 46 * v 70 + v 17 * v 27 * v 46 * v 70 + v 7 * v 35 * v 46 * v 70 + v 27 * v 35 * v 46 * v 70 + v 5 * v 37 * v 46 * v 70 + v 7 * v 37 * v 46 * v 70 + v 25 * v 37 * v 46 * v 70 + v 27 * v 37 * v 46 * v 70 + v 15 * v 25 * v 48 * v 70 + v 17 * v 25 * v 48 * v 70 + v 15 * v 27 * v 48 * v 70 + v 5 * v 35 * v 48 * v 70 + v 7 * v 35 * v 48 * v 70 + v 25 * v 35 * v 48 * v 70 + v 27 * v 35 * v 48 * v 70 + v 5 * v 37 * v 48 * v 70 + v 25 * v 37 * v 48 * v 70,
    -- quotient-39
    v 17 * v 26 + v 16 * v 27 + v 7 * v 36 + v 27 * v 36 + v 6 * v 37 + v 26 * v 37 + v 7 * v 16 * v 40 + v 6 * v 17 * v 40 + v 7 * v 16 * v 47 + v 6 * v 17 * v 47 + v 7 * v 17 * v 47 + v 6 * v 16 * v 48 + v 7 * v 16 * v 48 + v 6 * v 17 * v 48 + v 48 * v 58 + v 47 * v 59 + v 17 * v 26 * v 40 * v 70 + v 16 * v 27 * v 40 * v 70 + v 7 * v 36 * v 40 * v 70 + v 27 * v 36 * v 40 * v 70 + v 6 * v 37 * v 40 * v 70 + v 26 * v 37 * v 40 * v 70 + v 17 * v 26 * v 47 * v 70 + v 16 * v 27 * v 47 * v 70 + v 17 * v 27 * v 47 * v 70 + v 7 * v 36 * v 47 * v 70 + v 27 * v 36 * v 47 * v 70 + v 6 * v 37 * v 47 * v 70 + v 7 * v 37 * v 47 * v 70 + v 26 * v 37 * v 47 * v 70 + v 27 * v 37 * v 47 * v 70 + v 16 * v 26 * v 48 * v 70 + v 17 * v 26 * v 48 * v 70 + v 16 * v 27 * v 48 * v 70 + v 6 * v 36 * v 48 * v 70 + v 7 * v 36 * v 48 * v 70 + v 26 * v 36 * v 48 * v 70 + v 27 * v 36 * v 48 * v 70 + v 6 * v 37 * v 48 * v 70 + v 26 * v 37 * v 48 * v 70
  ]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_0_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 0 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_1_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 1 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_2_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 2 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 3, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 3, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {3}, {0, 3}, {5}, {0, 5}, {3, 5}, {0, 3, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_3_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 3 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 4, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_4_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 4 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_5_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 5 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {7}, {0, 7}, {5, 7}, {0, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_6_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 6 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 5, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 8} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {8}, {0, 8}, {5, 8}, {0, 5, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_7_eq_returned_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 7 =
      (mixedReturnSection .zeroOne p).coeff
        ⟨({0, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {9}, {0, 9}, {5, 9}, {0, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_8_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 8 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 1, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_9_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 9 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 2, 5} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_10_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 10 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 1, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {6}, {0, 6}, {1, 6}, {0, 1, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_11_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 11 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_12_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 12 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({1, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {6}, {1, 6}, {5, 6}, {1, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_13_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 13 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 1, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {6}, {0, 6}, {1, 6}, {0, 1, 6}, {5, 6}, {0, 5, 6}, {1, 5, 6}, {0, 1, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_14_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 14 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({2, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({2, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {2}, {5}, {2, 5}, {6}, {2, 6}, {5, 6}, {2, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_15_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 15 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 2, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}, {6}, {0, 6}, {2, 6}, {0, 2, 6}, {5, 6}, {0, 5, 6}, {2, 5, 6}, {0, 2, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_16_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 16 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 4, 5, 6} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 6} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {6}, {0, 6}, {4, 6}, {0, 4, 6}, {5, 6}, {0, 5, 6}, {4, 5, 6}, {0, 4, 5, 6}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_17_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 17 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {7}, {0, 7}, {5, 7}, {0, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_18_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 18 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({1, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({1, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {1}, {5}, {1, 5}, {7}, {1, 7}, {5, 7}, {1, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_19_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 19 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 1, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 1, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {1}, {0, 1}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {7}, {0, 7}, {1, 7}, {0, 1, 7}, {5, 7}, {0, 5, 7}, {1, 5, 7}, {0, 1, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_20_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 20 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 2, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 2, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {2}, {0, 2}, {5}, {0, 5}, {2, 5}, {0, 2, 5}, {7}, {0, 7}, {2, 7}, {0, 2, 7}, {5, 7}, {0, 5, 7}, {2, 5, 7}, {0, 2, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_21_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 21 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 3, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 3, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {3}, {0, 3}, {5}, {0, 5}, {3, 5}, {0, 3, 5}, {7}, {0, 7}, {3, 7}, {0, 3, 7}, {5, 7}, {0, 5, 7}, {3, 5, 7}, {0, 3, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_22_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 22 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 4, 5, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {7}, {0, 7}, {4, 7}, {0, 4, 7}, {5, 7}, {0, 5, 7}, {4, 5, 7}, {0, 4, 5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_23_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 23 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 6, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 6, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {6}, {0, 6}, {7}, {0, 7}, {6, 7}, {0, 6, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_24_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 24 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({5, 6, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({5, 6, 7} : Finset (Fin 10)).powerset =
      {∅, {5}, {6}, {5, 6}, {7}, {5, 7}, {6, 7}, {5, 6, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_25_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 25 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 5, 6, 7} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 5, 6, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {5}, {0, 5}, {6}, {0, 6}, {5, 6}, {0, 5, 6}, {7}, {0, 7}, {5, 7}, {0, 5, 7}, {6, 7}, {0, 6, 7}, {5, 6, 7}, {0, 5, 6, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_26_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 26 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 4, 5, 8} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 8} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {8}, {0, 8}, {4, 8}, {0, 4, 8}, {5, 8}, {0, 5, 8}, {4, 5, 8}, {0, 4, 5, 8}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_27_eq_feedback_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 27 =
      (mixedReturnFeedbackProduct .zeroOne .zero p).coeff
        ⟨({0, 4, 5, 9} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({0, 4, 5, 9} : Finset (Fin 10)).powerset =
      {∅, {0}, {4}, {0, 4}, {5}, {0, 5}, {4, 5}, {0, 4, 5}, {9}, {0, 9}, {4, 9}, {0, 4, 9}, {5, 9}, {0, 5, 9}, {4, 5, 9}, {0, 4, 5, 9}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_28_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 28 =
      mixedReturnQuotientCoordinate 0
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 0
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({0, 7} : Finset (Fin 10)).powerset =
      {∅, {0}, {7}, {0, 7}} := by decide
  have hpowersetSecond : ({2, 5} : Finset (Fin 10)).powerset =
      {∅, {2}, {5}, {2, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_29_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 29 =
      mixedReturnQuotientCoordinate 2
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 2
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({1, 6} : Finset (Fin 10)).powerset =
      {∅, {1}, {6}, {1, 6}} := by decide
  have hpowersetSecond : ({2, 5} : Finset (Fin 10)).powerset =
      {∅, {2}, {5}, {2, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_30_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 30 =
      mixedReturnQuotientCoordinate 3
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 3
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({1, 7} : Finset (Fin 10)).powerset =
      {∅, {1}, {7}, {1, 7}} := by decide
  have hpowersetSecond : ({3, 5} : Finset (Fin 10)).powerset =
      {∅, {3}, {5}, {3, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_31_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 31 =
      mixedReturnQuotientCoordinate 5
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        mixedReturnQuotientCoordinate 5
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({2, 6} : Finset (Fin 10)).powerset =
      {∅, {2}, {6}, {2, 6}} := by decide
  have hpowersetSecond : ({3, 5} : Finset (Fin 10)).powerset =
      {∅, {3}, {5}, {3, 5}} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_32_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 32 =
      alignedReturnQuotientCoordinate 0
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        alignedReturnQuotientCoordinate 0
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [alignedReturnQuotientCoordinate, alignedReturnQuotientPair,
    quadraticProjection, quadraticPair, aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({5, 7} : Finset (Fin 10)).powerset =
      {∅, {5}, {7}, {5, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem zeroOneAligned_base_constraint_33_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    zeroOneAlignedBaseConstraint p.vector 33 =
      alignedReturnQuotientCoordinate 1
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) +
        alignedReturnQuotientCoordinate 1
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [alignedReturnQuotientCoordinate, alignedReturnQuotientPair,
    quadraticProjection, quadraticPair, aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({6, 7} : Finset (Fin 10)).powerset =
      {∅, {6}, {7}, {6, 7}} := by decide
  rw [hpowerset]
  simp (config := { decide := true }) [zeroOneAlignedBaseConstraint]
  simp_mixed_return_history
  ring_nf
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]

/-- Literal quadratic-history hypotheses discharge the complete
equation base for `ZeroOneAligned`. -/
theorem zeroOneAligned_base_equations_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .zeroOne p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne .zero p ∈
      N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p))) :
    ∀ i : Fin 34, zeroOneAlignedBaseConstraint p.vector i = 0 := by
  intro i
  fin_cases i
  · change zeroOneAlignedBaseConstraint p.vector (0 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_0_eq_returned_coeff]
    exact hreturned ⟨{0, 1, 5}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (1 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_1_eq_returned_coeff]
    exact hreturned ⟨{0, 2, 5}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (2 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_2_eq_returned_coeff]
    exact hreturned ⟨{0, 3, 5}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (3 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_3_eq_returned_coeff]
    exact hreturned ⟨{0, 4, 5}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (4 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_4_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 6}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (5 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_5_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (6 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_6_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 8}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (7 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_7_eq_returned_coeff]
    exact hreturned ⟨{0, 5, 9}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (8 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_8_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (9 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_9_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 5}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (10 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_10_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 6}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (11 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_11_eq_feedback_coeff]
    exact hfeedback ⟨{0, 5, 6}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (12 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_12_eq_feedback_coeff]
    exact hfeedback ⟨{1, 5, 6}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (13 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_13_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5, 6}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (14 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_14_eq_feedback_coeff]
    exact hfeedback ⟨{2, 5, 6}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (15 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_15_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 5, 6}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (16 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_16_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 6}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (17 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_17_eq_feedback_coeff]
    exact hfeedback ⟨{0, 5, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (18 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_18_eq_feedback_coeff]
    exact hfeedback ⟨{1, 5, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (19 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_19_eq_feedback_coeff]
    exact hfeedback ⟨{0, 1, 5, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (20 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_20_eq_feedback_coeff]
    exact hfeedback ⟨{0, 2, 5, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (21 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_21_eq_feedback_coeff]
    exact hfeedback ⟨{0, 3, 5, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (22 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_22_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (23 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_23_eq_feedback_coeff]
    exact hfeedback ⟨{0, 6, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (24 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_24_eq_feedback_coeff]
    exact hfeedback ⟨{5, 6, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (25 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_25_eq_feedback_coeff]
    exact hfeedback ⟨{0, 5, 6, 7}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (26 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_26_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 8}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (27 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_27_eq_feedback_coeff]
    exact hfeedback ⟨{0, 4, 5, 9}⟩ (by decide)
  · change zeroOneAlignedBaseConstraint p.vector (28 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_28_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection
      _ _ hprojection 0
  · change zeroOneAlignedBaseConstraint p.vector (29 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_29_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection
      _ _ hprojection 2
  · change zeroOneAlignedBaseConstraint p.vector (30 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_30_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection
      _ _ hprojection 3
  · change zeroOneAlignedBaseConstraint p.vector (31 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_31_eq_quotient_row]
    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection
      _ _ hprojection 5
  · change zeroOneAlignedBaseConstraint p.vector (32 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_32_eq_quotient_row]
    exact alignedReturnQuotientCoordinate_add_eq_zero_of_projection
      _ _ hprojection 0
  · change zeroOneAlignedBaseConstraint p.vector (33 : Fin 34) = 0
    rw [zeroOneAligned_base_constraint_33_eq_quotient_row]
    exact alignedReturnQuotientCoordinate_add_eq_zero_of_projection
      _ _ hprojection 1

end
end N5
end UnrestrictedBooleanMul
