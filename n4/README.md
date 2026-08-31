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

The manuscript is distributed separately through arXiv. Its public identifier
will be added here after announcement. No TeX or PDF copy is kept in this
repository.

## Immutable snapshot

Current Lean-complete release: [`n4-arxiv-v2`](https://github.com/GregoryMorse/unrestricted-boolean-mul/releases/tag/n4-arxiv-v2).

Historical pre-Lean computational snapshot:
[`n4-arxiv-v1`](https://github.com/GregoryMorse/unrestricted-boolean-mul/releases/tag/n4-arxiv-v1).
That tag remains unchanged. The current tag resolves to the exact public
commit recorded by the associated paper together with its clean-checkout
verification date.
