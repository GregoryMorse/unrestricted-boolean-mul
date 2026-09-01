# Unrestricted Boolean Multiplicative Complexity of Binary Polynomial Multiplication

This repository contains formal Lean proofs and legacy computational
verification artifacts for exact unrestricted XOR--AND
multiplicative-complexity results for binary polynomial multiplication.

The repository is organized by input length so that later results can be added
without renaming or replacing the existing artifact:

- [`n4/`](n4/) -- four-term multiplication, with exact value 9.
- [`n5/`](n5/) -- five-term multiplication, with hand proof of exact value 13
  and Lean formalization in progress.
- Future results will use parallel directories such as `n6/` or `general/`.

The accompanying `n4` paper makes the current unrestricted small-instance
frontier explicit:

| Term count | `MC(Mul_n)` | Status |
|---:|---:|---|
| 0 | 0 | empty-input convention |
| 1 | 1 | elementary dimension bound and one product |
| 2 | 3 | elementary dimension bound and Karatsuba's three products |
| 3 | 6 | assumption-free Lean proof and explicit six-product circuit |
| 4 | 9 | kernel-checked Lean proof and explicit nine-product circuit |
| 5 | 13 | algebraic hand proof; Lean target/upper circuit, quadratic quotient, relation map, rank-two/secant support, local Klein counts, and the injective 43-point atlas kernel-checked; full lower-bound formalization in progress |

The manuscripts contain the mathematical exposition and literature citations.
The Lean development checks the five rows `n = 0` through `n = 4`. For `n = 5`,
the statement interface, target-dimension layer, explicit upper circuit, and
the first lower-bound infrastructure have passed the pinned kernel. The final
thirteen-gate lower bound remains in progress.

## Lean 4 formalization

The root Lean project formalizes the exact results through `n = 4` and the
first independent layer of the `n = 5` proof:

- canonical Boolean ANFs over `ZMod 2`, with squarefree monomials multiplied by
  union;
- unrestricted XOR--AND circuits, their `Computes` semantics, multiplicative
  complexity `MC`, and target dimension;
- exact results `MC(Mul 0) = 0`, `MC(Mul 1) = 1`, and `MC(Mul 2) = 3`;
- explicit upper circuits with 6 AND gates for `Mul 3` and 9 AND gates for
  `Mul 4`;
- the assumption-free exact theorems `MC(Mul 3) = 6` and
  `MC(Mul 4) = 9`;
- a separated canonical proposition for `MC(Mul 5) = 13`;
- a proof that the nine outputs of `Mul 5` are independent, yielding the
  unconditional nine-AND dimension lower bound; and
- an explicit thirteen-product `Mul 5` circuit with nine recombination
  identities proved by ring normalization;
- an intrinsic 45-dimensional squarefree quadratic space, nine-dimensional
  Hankel target, and 36-dimensional quotient;
- the zero-fiber classification proved from Hankel minors; and
- the target/defect ledger and exact relation-map formula;
- dimension-polymorphic secant support and the symbolic local Klein counts;
- an exact Hermite certificate proving that the four effective local charts
  embed as 43 distinct global quotient points; and
- the exact algebraic classification proving that those 43 points are all and
  only the effective quadratic fibers; and
- algebraic Pluecker certificates excluding every pair of distinct effective
  closed-place types, including all rational--degree-two pairs; and
- a choice-independent defect-capacity span with the exact specialized ledger
  `rho(Q) = 3 + d + rank(lambda)` and algebraic localization of every
  effective fiber difference to its closed-place target plane; and
- the exact represented-place profile of the displacement space, including
  the one-jet rational and two-direction degree-two local contributions and
  the proof that ineffective fibers contribute only rational directions; and
- the sparse Fano relation reduction, the sharp zero-place and three-rational
  capacity rows, and a fully algebraic Pluecker proof of the representative
  `P_* + 2` rational row, where the triple-sum fiber is empty, the relation
  gift vanishes, and the target capacity is exactly seven; and
- explicit translation and reversal actions on the ten input coordinates,
  their functorial exterior-square action, the four local Klein charts, and
  the nine-dimensional Hankel target, transporting the representative row to
  the other two rational-place pairs without enumeration; all three
  degree-two-plus-two-rational profiles have empty triple fibers, zero
  relation gift, and target capacity exactly seven; and
- symmetry-complete four-pivot local secant spaces at all three rational
  places and at the degree-two place, together with a translation-in-the-
  defect proof that pointed Fano lines have codimension at most one in the
  full relation kernel.  These close every represented-place profile without
  enumerating defect planes, prove the universal displacement bound
  `d + rank(lambda) <= 4`, and establish the exact capacity `rho_3(5) = 7`;
  and
- the exact-sequence capacity obstruction for arbitrary finite decomposable
  presentations, including the algebraic exclusion of twelve quadratic
  products spanning the five-term target; and
- unrestricted-prefix target/defect bookkeeping together with a
  ten-variable semantic flattening theorem.  The flattening reuses the
  recursive Reed--Muller minimum-word argument, performs no truth-table
  enumeration, and excludes every all-quadratic circuit with at most twelve
  ANDs; and
- a canonical last-quadratic-prefix state.  Quotient-image monotonicity and
  the algebraic first-high defect-birth lemma show that this state has defect
  at most two in every relevant nonredundant circuit; and
- a gate-count-free definition of every finite defect-legal unrestricted
  suffix, with the corrected equal-defect-two monotonicity theorem for target
  gain and the resulting monotonicity of the completion deficit.

The five-gate exclusion for `Mul 3` is proved internally. Its finite
rational-place classification is reduced to seven quadratic coefficient
equations over `ZMod 2`. Two explicit Boolean-ideal identities derive the
required equality of the three middle Hankel coefficients. Lean checks those
identities by ordinary ring normalization and connects them to the ANF and
unrestricted-circuit semantics through nine explicit coefficient lemmas. The
development does not use `bv_decide`, `native_decide`, `sorry`, `admit`, or a
project axiom. In particular, the audit of both `mc_mul_three` and
`N4.mc_mul_four` reports only `propext`, `Classical.choice`, and `Quot.sound`.
The checked `n = 5` declarations are included in `AxiomAudit.lean`; the
repository does not yet claim a completed Lean proof of `MC(Mul 5) = 13`.

The main entry points are:

- [`UnrestrictedBooleanMul/ANF.lean`](UnrestrictedBooleanMul/ANF.lean)
- [`UnrestrictedBooleanMul/Circuit.lean`](UnrestrictedBooleanMul/Circuit.lean)
- [`UnrestrictedBooleanMul/Mul.lean`](UnrestrictedBooleanMul/Mul.lean)
- [`UnrestrictedBooleanMul/SmallCases.lean`](UnrestrictedBooleanMul/SmallCases.lean)
- [`UnrestrictedBooleanMul/N3Certificate.lean`](UnrestrictedBooleanMul/N3Certificate.lean)
- [`UnrestrictedBooleanMul/N3.lean`](UnrestrictedBooleanMul/N3.lean)
- [`UnrestrictedBooleanMul/N3TruthTable.lean`](UnrestrictedBooleanMul/N3TruthTable.lean)
- [`UnrestrictedBooleanMul/N4/Main.lean`](UnrestrictedBooleanMul/N4/Main.lean)
- [`UnrestrictedBooleanMul/N5/Target.lean`](UnrestrictedBooleanMul/N5/Target.lean)
- [`UnrestrictedBooleanMul/N5/Upper.lean`](UnrestrictedBooleanMul/N5/Upper.lean)
- [`UnrestrictedBooleanMul/N5/Statement.lean`](UnrestrictedBooleanMul/N5/Statement.lean)
- [`UnrestrictedBooleanMul/N5/QuadraticSpace.lean`](UnrestrictedBooleanMul/N5/QuadraticSpace.lean)
- [`UnrestrictedBooleanMul/N5/Fiber.lean`](UnrestrictedBooleanMul/N5/Fiber.lean)
- [`UnrestrictedBooleanMul/N5/RelationMap.lean`](UnrestrictedBooleanMul/N5/RelationMap.lean)
- [`UnrestrictedBooleanMul/N5/ClosedPlaces.lean`](UnrestrictedBooleanMul/N5/ClosedPlaces.lean)
- [`UnrestrictedBooleanMul/N5/HankelSupport.lean`](UnrestrictedBooleanMul/N5/HankelSupport.lean)
- [`UnrestrictedBooleanMul/N5/LocalKlein.lean`](UnrestrictedBooleanMul/N5/LocalKlein.lean)
- [`UnrestrictedBooleanMul/N5/EffectiveFibers.lean`](UnrestrictedBooleanMul/N5/EffectiveFibers.lean)
- [`UnrestrictedBooleanMul/N5/RankTwoSecants.lean`](UnrestrictedBooleanMul/N5/RankTwoSecants.lean)
- [`UnrestrictedBooleanMul/N5/EffectiveClassification.lean`](UnrestrictedBooleanMul/N5/EffectiveClassification.lean)
- [`UnrestrictedBooleanMul/N5/MixedPlace.lean`](UnrestrictedBooleanMul/N5/MixedPlace.lean)
- [`UnrestrictedBooleanMul/N5/MixedPlaceDegree.lean`](UnrestrictedBooleanMul/N5/MixedPlaceDegree.lean)
- [`UnrestrictedBooleanMul/N5/MixedPlaceDegreeOne.lean`](UnrestrictedBooleanMul/N5/MixedPlaceDegreeOne.lean)
- [`UnrestrictedBooleanMul/N5/MixedPlaceDegreeInfinity.lean`](UnrestrictedBooleanMul/N5/MixedPlaceDegreeInfinity.lean)
- [`UnrestrictedBooleanMul/N5/Displacement.lean`](UnrestrictedBooleanMul/N5/Displacement.lean)
- [`UnrestrictedBooleanMul/N5/DisplacementProfile.lean`](UnrestrictedBooleanMul/N5/DisplacementProfile.lean)
- [`UnrestrictedBooleanMul/N5/DisplacementRank.lean`](UnrestrictedBooleanMul/N5/DisplacementRank.lean)
- [`UnrestrictedBooleanMul/N5/FanoRelations.lean`](UnrestrictedBooleanMul/N5/FanoRelations.lean)
- [`UnrestrictedBooleanMul/N5/RelationIncidence.lean`](UnrestrictedBooleanMul/N5/RelationIncidence.lean)
- [`UnrestrictedBooleanMul/N5/RelationGiftCoefficients.lean`](UnrestrictedBooleanMul/N5/RelationGiftCoefficients.lean)
- [`UnrestrictedBooleanMul/N5/RelationGiftPivots.lean`](UnrestrictedBooleanMul/N5/RelationGiftPivots.lean)
- [`UnrestrictedBooleanMul/N5/EffectivePointPlaces.lean`](UnrestrictedBooleanMul/N5/EffectivePointPlaces.lean)
- [`UnrestrictedBooleanMul/N5/FourPlaceRelation.lean`](UnrestrictedBooleanMul/N5/FourPlaceRelation.lean)
- [`UnrestrictedBooleanMul/N5/FourPlaceExclusion.lean`](UnrestrictedBooleanMul/N5/FourPlaceExclusion.lean)
- [`UnrestrictedBooleanMul/N5/DecomposableAnchor.lean`](UnrestrictedBooleanMul/N5/DecomposableAnchor.lean)
- [`UnrestrictedBooleanMul/N5/SparseAnchorGifts.lean`](UnrestrictedBooleanMul/N5/SparseAnchorGifts.lean)
- [`UnrestrictedBooleanMul/N5/ThreeRationalProfile.lean`](UnrestrictedBooleanMul/N5/ThreeRationalProfile.lean)
- [`UnrestrictedBooleanMul/N5/ThreePlaceDegreeTwo.lean`](UnrestrictedBooleanMul/N5/ThreePlaceDegreeTwo.lean)
- [`UnrestrictedBooleanMul/N5/RationalPlaceSymmetry.lean`](UnrestrictedBooleanMul/N5/RationalPlaceSymmetry.lean)
- [`UnrestrictedBooleanMul/N5/TwoRationalDegreeTwoProfile.lean`](UnrestrictedBooleanMul/N5/TwoRationalDegreeTwoProfile.lean)
- [`UnrestrictedBooleanMul/N5/TwoPlaceProfile.lean`](UnrestrictedBooleanMul/N5/TwoPlaceProfile.lean)
- [`UnrestrictedBooleanMul/N5/DefectTwoCapacity.lean`](UnrestrictedBooleanMul/N5/DefectTwoCapacity.lean)
- [`UnrestrictedBooleanMul/N5/DefectThreeWitness.lean`](UnrestrictedBooleanMul/N5/DefectThreeWitness.lean)
- [`UnrestrictedBooleanMul/N5/SecantPfaffian.lean`](UnrestrictedBooleanMul/N5/SecantPfaffian.lean)
- [`UnrestrictedBooleanMul/N5/LocalSecantPivots.lean`](UnrestrictedBooleanMul/N5/LocalSecantPivots.lean)
- [`UnrestrictedBooleanMul/N5/DegreeTwoSecantQ2.lean`](UnrestrictedBooleanMul/N5/DegreeTwoSecantQ2.lean)
- [`UnrestrictedBooleanMul/N5/DegreeTwoSecantPivots.lean`](UnrestrictedBooleanMul/N5/DegreeTwoSecantPivots.lean)
- [`UnrestrictedBooleanMul/N5/LineSecantGifts.lean`](UnrestrictedBooleanMul/N5/LineSecantGifts.lean)
- [`UnrestrictedBooleanMul/N5/FanoLineIncidencePivots.lean`](UnrestrictedBooleanMul/N5/FanoLineIncidencePivots.lean)
- [`UnrestrictedBooleanMul/N5/PointedFanoRelations.lean`](UnrestrictedBooleanMul/N5/PointedFanoRelations.lean)
- [`UnrestrictedBooleanMul/N5/RationalSecantSymmetry.lean`](UnrestrictedBooleanMul/N5/RationalSecantSymmetry.lean)
- [`UnrestrictedBooleanMul/N5/AllRationalPointedPivots.lean`](UnrestrictedBooleanMul/N5/AllRationalPointedPivots.lean)
- [`UnrestrictedBooleanMul/N5/StrongDegreeTwoPointedPivots.lean`](UnrestrictedBooleanMul/N5/StrongDegreeTwoPointedPivots.lean)
- [`UnrestrictedBooleanMul/N5/DisplacementBound.lean`](UnrestrictedBooleanMul/N5/DisplacementBound.lean)
- [`UnrestrictedBooleanMul/N5/Capacity.lean`](UnrestrictedBooleanMul/N5/Capacity.lean)
- [`UnrestrictedBooleanMul/N5/Prefix.lean`](UnrestrictedBooleanMul/N5/Prefix.lean)
- [`UnrestrictedBooleanMul/N5/QuadraticFlattening.lean`](UnrestrictedBooleanMul/N5/QuadraticFlattening.lean)
- [`UnrestrictedBooleanMul/N5/PrefixState.lean`](UnrestrictedBooleanMul/N5/PrefixState.lean)
- [`UnrestrictedBooleanMul/N5/SuffixBudget.lean`](UnrestrictedBooleanMul/N5/SuffixBudget.lean)
- [`UnrestrictedBooleanMul/QuadraticSupport.lean`](UnrestrictedBooleanMul/QuadraticSupport.lean)
- [`n5/FORMALIZATION_HANDOFF.md`](n5/FORMALIZATION_HANDOFF.md)
- [`AxiomAudit.lean`](AxiomAudit.lean)

The `N3`, `N4`, and `N5` names describe input sizes; they are not labels for
internal research phases.

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
mathlib revision. [`lakefile.toml`](lakefile.toml) is the repository's
first-class Lake configuration; Lake supports this TOML form directly, so a
duplicate `lakefile.lean` would add configuration drift rather than improve
scraper visibility. Its default target is the complete
`UnrestrictedBooleanMul` library. Install
[Elan](https://github.com/leanprover/elan), ensure its
binary directory is on `PATH`, and replay the project on any supported platform
with:

```bash
lake exe cache --cache-from=legacy get
lake build
lake env lean AxiomAudit.lean
lake env leanchecker UnrestrictedBooleanMul
```

The checker module is named explicitly because the Lake package uses a
snake-case package name while the Lean library uses `UnrestrictedBooleanMul`.
Continuous integration repeats the build and axiom audit on every push and
pull request, runs `leanchecker` on the explicit library module, and performs a
fresh source replay on its weekly schedule.

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
