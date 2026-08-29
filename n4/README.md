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

- [`verification/`](verification/) contains the Python and C++ regression
  checks and their recorded outputs.
- [`verification/README.txt`](verification/README.txt) maps every program to
  the proof bookkeeping it checks and gives exact reproduction commands.
- [`verification/LICENSE`](verification/LICENSE) preserves the MIT terms when
  this paper-specific verification subtree is distributed independently.
- [`SHA256SUMS.txt`](SHA256SUMS.txt) fixes the exact bytes of this result's
  verification snapshot.

The checks support development and reproducibility; no program output is a
logical premise of the theorem.

## Paper

*Unrestricted Boolean Multiplicative Complexity of Four-Term Binary Polynomial
Multiplication: Rational Places, Hasse Jets, and the Failure of Nonlinear
Feedback*, Gregory Morse.

The manuscript is distributed separately through arXiv. Its public identifier
will be added here after announcement. No TeX or PDF copy is kept in this
repository.

## Immutable snapshot

Intended release tag: `n4-arxiv-v1`  
Full commit hash: `PENDING`  
Live verification date: `PENDING`
