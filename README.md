# Unrestricted Boolean Multiplicative Complexity of Binary Polynomial Multiplication

This repository collects computational verification artifacts for exact
unrestricted XOR--AND multiplicative-complexity results for binary polynomial
multiplication.

The repository is organized by input length so that later results can be added
without renaming or replacing the existing artifact:

- [`n4/`](n4/) -- four-term multiplication, with exact value 9.
- Future results will use parallel directories such as `n5/`, `n6/`, or
  `general/`.

The accompanying `n4` paper makes the current unrestricted small-instance
frontier explicit:

| Term count | `MC(Mul_n)` | Status |
|---:|---:|---|
| 0 | 0 | empty-input convention |
| 1 | 1 | elementary dimension bound and one product |
| 2 | 3 | elementary dimension bound and Karatsuba's three products |
| 3 | 6 | assumption-free Lean proof and explicit six-product circuit |
| 4 | 9 | unrestricted lower bound; artifact in [`n4/`](n4/) |

The manuscript contains the mathematical exposition and literature citations.
The Lean development in this repository now checks the first four rows.

## Lean 4 formalization

The root Lean project completes the first two formalization phases:

- canonical Boolean ANFs over `ZMod 2`, with squarefree monomials multiplied by
  union;
- unrestricted XOR--AND circuits, their `Computes` semantics, multiplicative
  complexity `MC`, and target dimension;
- exact results `MC(Mul 0) = 0`, `MC(Mul 1) = 1`, and `MC(Mul 2) = 3`;
- explicit upper circuits with 6 AND gates for `Mul 3` and 9 AND gates for
  `Mul 4`;
- the assumption-free exact theorem `MC(Mul 3) = 6`.

The five-gate exclusion for `Mul 3` is proved internally. Its finite
rational-place classification is reduced to seven quadratic coefficient
equations over `ZMod 2`. Two explicit Boolean-ideal identities derive the
required equality of the three middle Hankel coefficients. Lean checks those
identities by ordinary ring normalization and connects them to the ANF and
unrestricted-circuit semantics through nine explicit coefficient lemmas. The
development does not use `bv_decide`, `native_decide`, `sorry`, `admit`, or a
project axiom. In particular, `#print axioms mc_mul_three` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

The main entry points are:

- [`UnrestrictedBooleanMul/ANF.lean`](UnrestrictedBooleanMul/ANF.lean)
- [`UnrestrictedBooleanMul/Circuit.lean`](UnrestrictedBooleanMul/Circuit.lean)
- [`UnrestrictedBooleanMul/Mul.lean`](UnrestrictedBooleanMul/Mul.lean)
- [`UnrestrictedBooleanMul/SmallCases.lean`](UnrestrictedBooleanMul/SmallCases.lean)
- [`UnrestrictedBooleanMul/Phase2Certificate.lean`](UnrestrictedBooleanMul/Phase2Certificate.lean)
- [`UnrestrictedBooleanMul/Phase2.lean`](UnrestrictedBooleanMul/Phase2.lean)

Manuscript source and rendered papers are intentionally not mirrored here.
Papers are distributed through arXiv or their eventual publication venues;
this repository contains only reusable verification material and the
documentation needed to reproduce it.

## Versioning convention

Each paper snapshot receives a namespaced release tag:

- `n4-arxiv-v1` for the first arXiv version of the four-term result;
- `n5-arxiv-v1` for the future five-term result;
- and analogously for later versions and general results.

The paper, its arXiv metadata, and the corresponding directory README record
the exact tag and full commit hash. A mutable branch is not used as the
reproducibility pin.

## Toolchains

The Lean project is pinned by [`lean-toolchain`](lean-toolchain) to Lean
`v4.32.1`, and [`lake-manifest.json`](lake-manifest.json) pins the corresponding
mathlib revision. With `C:\Users\Gregory\.elan\bin` on `PATH`, replay it with:

```powershell
lake build
```

The existing `n4` computational checks additionally require Python 3 and a
C++17 compiler, as documented under [`n4/`](n4/).

## AI assistance disclosure

OpenAI GPT-5.6 Sol in extra-high thinking mode was used for research, proof
exploration and development, computational checking, literature and citation
verification, manuscript drafting and revision, and submission preparation.
Anthropic Opus 5 in high thinking mode was used as a referee. Gregory Morse
reviewed the resulting mathematical claims, proofs, computations, citations,
code, and manuscript text and assumes full responsibility for the final work.

## License

Copyright (c) 2026 Gregory Morse. The verification software and associated
repository documentation are released under the permissive
[MIT License](LICENSE). Manuscripts are distributed separately and are not
covered by this repository license.
