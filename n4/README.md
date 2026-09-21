# Four-term binary polynomial multiplication (`n = 4`)

The associated preprint proves

```text
MC(Mul4) = 9
```

for unrestricted XOR--AND circuits. The lower bound permits nonlinear
intermediate reuse and Boolean reduction modulo idempotence, so it is stronger
than the classical bilinear and quadratic lower bounds for this instance.
Together with the paper's explicit treatment of `n = 0,1,2,3`, this gives the
small-instance frontier `0,1,3,6,9`; `n = 4` is the first case requiring a
nonzero defect-budget argument.

## Artifact contents

- The root Lean project is the formal certificate for `MC(Mul 4) = 9`; its
  headline declaration is `UnrestrictedBooleanMul.N4.mc_mul_four`.
- [`../AxiomAudit.lean`](../AxiomAudit.lean) prints the trusted assumptions of
  every headline exact theorem.
- [`LEAN_SHA256SUMS.txt`](LEAN_SHA256SUMS.txt) fixes every Lean source,
  toolchain lock, and trust/CI file used for the formal proof.
- [`AXIOM_AUDIT.txt`](AXIOM_AUDIT.txt) records the reviewed audit output for
  the release commit.
- [`verification/`](verification/) contains the Python and C++ regression
  checks and their recorded outputs.
- [`verification/README.txt`](verification/README.txt) maps every program to
  the proof bookkeeping it checks and gives exact reproduction commands.
- [`verification/LICENSE`](verification/LICENSE) preserves the MIT terms when
  this paper-specific verification subtree is distributed independently.
- [`SHA256SUMS.txt`](SHA256SUMS.txt) fixes the exact bytes of this result's
  verification snapshot.

The Lean proof is the formal certificate. The Python and C++ programs are
independent regression checks for development and reproducibility; no program
output is a trusted premise of the theorem.

## Paper

*Unrestricted Boolean Multiplicative Complexity of Four-Term Binary Polynomial
Multiplication: Rational Places, Hasse Jets, and the Failure of Nonlinear
Feedback*, Gregory Morse.

The manuscript is [arXiv:2608.30238v1](https://arxiv.org/abs/2608.30238v1).
No TeX or PDF copy is kept in this repository. The default Lean build and
`lean.yml` now isolate this published result from n5/n6 research.
See [Palomar audit](PALOMAR_AUDIT.md) and [submission preparation](SUBMISSION.md).

## Immutable snapshot

Published-paper snapshot: [`n4-arxiv-v2`](https://github.com/GregoryMorse/unrestricted-boolean-mul/releases/tag/n4-arxiv-v2).
The [`n4-arxiv-v3` release](https://github.com/GregoryMorse/unrestricted-boolean-mul/releases/tag/n4-arxiv-v3)
pins Lean 4.33.1 and the isolated n4 CI plus Palomar interface. The
[completed audit](PALOMAR_AUDIT.md) records passing CI, leanchecker,
Comparator and NanoDa checks. Release notes and attached reports identify
the exact commit for each run, including documentation-only corrections.

Historical pre-Lean computational snapshot:
[`n4-arxiv-v1`](https://github.com/GregoryMorse/unrestricted-boolean-mul/releases/tag/n4-arxiv-v1).
That tag remains unchanged. The paper continues to identify v2; the v3
release is a later toolchain/CI and documentation update, not a rewrite of
the paper's historical snapshot.
