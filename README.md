# Unrestricted Boolean multiplicative complexity

[![n4 Lean verification](https://github.com/GregoryMorse/unrestricted-boolean-mul/actions/workflows/lean.yml/badge.svg)](https://github.com/GregoryMorse/unrestricted-boolean-mul/actions/workflows/lean.yml)

The default build and `lean.yml` verify the published **n=4** result:
`MC(Mul 4) = 9` for unrestricted XOR–AND circuits, together with the exact
values `0,1,3,6` for n=0,1,2,3. Both factors of an AND may use earlier
nonlinear wires; Boolean idempotence is built into the model.

Paper: Gregory Morse, [arXiv:2608.30238v1](https://arxiv.org/abs/2608.30238v1).
See [the n4 artifact](n4/README.md), [Palomar audit](n4/PALOMAR_AUDIT.md),
[metadata](formalization.yaml), and [submission preparation](n4/SUBMISSION.md).
The immutable `n4-arxiv-v2` release remains the paper's historical snapshot.
The new n4 release updates the toolchain and verification interface, not the
paper's mathematical claim.

## Published proof and Palomar statement

- [ANF](UnrestrictedBooleanMul/ANF.lean): squarefree monomials multiply by
  union; evaluation is proved equivalent to Boolean-function semantics.
- [Circuit](UnrestrictedBooleanMul/Circuit.lean): constants and XOR are
  free, gates may reuse all previous outputs, and complexity is the minimum
  AND count.
- [Mul](UnrestrictedBooleanMul/Mul.lean): ordinary binary-polynomial
  convolution coefficients, including the empty n=0 convention.
- [Main theorem](UnrestrictedBooleanMul/N4/Main.lean): eight gates are
  impossible and nine suffice.
- [Challenge](Challenge.lean): readable, Mathlib-only statement of the
  same model and six headline results. Its six theorem holes are deliberate.
- [Solution](Solution.lean): imports the original proved declarations;
  it never imports Challenge. [Comparator](comparator.json) checks their
  correspondence. The permitted axioms are only `propext`,
  `Classical.choice`, and `Quot.sound`.

The complete proof is in this repository, not a thin wrapper. The Python/C++
regressions are not trusted premises. The n3 formal proof replaces a
literature-bound invocation with an internal algebraic certificate.
No general solution of the Boyar–Find question is asserted.

## Reproduction

Pinned Lean **4.33.1**, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib and its dependencies
are locked in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake env leanchecker UnrestrictedBooleanMul
```

On Linux, the CI-equivalent serial check also builds Challenge and Solution,
enforces the named axiom allowlist, and records source hashes and command logs:

```sh
python3 scripts/ci_verify.py --profile n4 --build --replay
```

CI is the preferred place for fresh replay. Do not run memory-intensive
parallel builds on Windows. The runner processes the local dependency
closure one module at a time, uses one CPU/thread, a 4-GiB Lean heap and
a 10-GiB virtual-address cap, and kills timed-out process groups.
`lake build` without arguments imports no n5/n6 research.

## Separate research workflows

| Workflow | What a green run establishes | What it does not establish |
| --- | --- | --- |
| `lean.yml` | Published n=0 through n=4 proof, axiom audit and leanchecker | n5/n6 lower bounds |
| `models-upper.yml` | Semantic model conversions and n6/5x6 upper witnesses | Exact n6 ranks |
| `n5.yml` | The thirteen-declaration quadratic-capacity, flattening and upper-bound audit | Unrestricted `MC(Mul 5)=13` |
| `n6-bilinear.yml` | Conditional reductions, orbit/output-profile lemmas, artifact integrity and positive witnesses | Discharge of the lower-bound hypotheses or fresh exhaustive enumeration |
| `palomar.yml` | Official pinned full mechanical preflight, when its report passes | Submission, editorial approval or permanent registration |

The research profiles are individually dispatchable and do not run as part
of the default n4 job. Their manual equivalents are
`python3 scripts/ci_verify.py --profile PROFILE --build`.
See [n5 scope](n5/CI_SCOPE.md) and [n6 scope](n6/CI_SCOPE.md).
Open SC3/endpoint work and unpublished manuscripts are outside this release
update. This does not claim that every exploratory file builds on 4.33.1.

## Authorship, automation and review

Gregory Morse is the human author and responsible maintainer. The paper
discloses OpenAI GPT-5.6 Sol (extra-high) for research and development and
Anthropic Opus 5 (high) as a critical AI referee, with author review and
responsibility. Codex assisted this release preparation; see
`formalization.yaml` for the scope and limitations of review.

[VibeMathed](https://vibemathed.com/problem/unrestricted-multiplicative-complexity-mul4)
reports an independent replay of `n4-arxiv-v2` on 3 September 2026.
That historical check is not a fresh check of this release or independent
statement anchoring. This submission formalizes the published paper and
does not claim independent novelty.

## License and release boundaries

Repository software and documentation are MIT-licensed. Manuscripts are
distributed separately and are not covered by this repository license.
Old tags are immutable. Preparing or tagging an n4 release does not submit
to Palomar or authorize permanent registration.
