# `n = 5` verification and discovery code

This directory contains finite discovery/regression checks and a bounded
Linux Lean-check helper.  The discovery calculations are not proof premises.

## Focused Lean checks

The standard build remains `lake build`, using the pinned `lean-toolchain`
and `lakefile.toml`.  For repair iterations on Linux with existing project
objects, check selected sources sequentially with explicit resource limits:

```bash
python3 n5/verification/check_lean_modules.py --memory-mb 8192 --timeout 240 \
  UnrestrictedBooleanMul.N5.QuadraticReturnHistoryChart \
  UnrestrictedBooleanMul.N5.PopulatedReturnCapacity
lake env lean n5/ReturnRepairAudit.lean
lake env leanchecker UnrestrictedBooleanMul.N5.QuadraticReturnHistoryChart \
  UnrestrictedBooleanMul.N5.PopulatedReturnCapacity
```

Run these from the repository root.  `--plan` shows exactly which sources
will be checked; `--lake /path/to/lake` selects the installed launcher.
Requested sources are always checked, missing project dependencies are
checked first, and existing dependency objects are reused.  This is not a
fresh repository replay.  The helper refuses to launch Lean on Windows.

The algebraic return repair uses factor shears, projective symmetry, and a
sextic obstruction.  The former 140-file `(0,1),RInf` candidate and redundant
`(1,2),RInf` raw certificate have been removed.  The discovery generator now
refuses to emit an aggregate Lean certificate with a nonzero XOR residual.

## Finite discovery and regression checks

The two top-level programs are small, curated regression checks.  The
independent-shadow check for the `W_*` envelope is:

- [`wstar_independent_shadow_check.cpp`](wstar_independent_shadow_check.cpp)
- [`wstar_independent_shadow_check_results.txt`](wstar_independent_shadow_check_results.txt)

The upper-circuit check is
[`five_upper_formula_check.py`](five_upper_formula_check.py), a dependency-free
symbolic expansion of the thirteen displayed affine products.  It checks all
nine output identities against the 25 bilinear monomials:

```bash
python3 five_upper_formula_check.py
```

The expected line is
`PASS gates=13 outputs=9 bilinear_monomials=25`.  This duplicates the
ring-normalization proof intended for `N5/Upper.lean`; it is a regression
checksum, not a Lean theorem.

It enumerates all 15 local independent planes and all `2^20` pairs of linear
corrections per plane, for `15,728,640` presentations.  Fixing the cubic high
part and the quadratic residue outside the envelope always fixes the target
tag.  The additional `affine_possible=0` datum says that this well-defined
shadow is not represented by one global affine functional on the combined key
space; the manuscript uses the local radical argument instead.

Replay with a C++20 compiler (the program uses `std::countr_zero` and
`std::popcount`):

```bash
g++ -O3 -std=c++20 wstar_independent_shadow_check.cpp -o wstar_check
./wstar_check >actual.txt 2>&1
diff -u wstar_independent_shadow_check_results.txt actual.txt
```

The final `CONSTANT` line is the pass condition.  On the 2026-09-01 handoff
container the replay completed successfully and matched the recorded counts.

## Recovered discovery programs

The [`exploration/`](exploration/) directory preserves nine Python programs
used to discover and stress-test the `W_{PQ}`, `W_{3P}`, and defect-at-most-one
arguments.  They are retained because the coordinate models, pivots, rank
profiles, and counterexample searches are useful guides for the Lean
formalization.  They are labelled as discovery code rather than certificates;
the manuscript replaces every load-bearing conclusion by an algebraic proof.

All nine files pass Python bytecode compilation.  The short deterministic
local-orbit program has a recorded transcript.  Two accelerated scans require
NumPy; the other seven use only the Python standard library.  See
[`exploration/README.md`](exploration/README.md) for the inventory and replay
status.

The source of the much larger 166,199,235-presentation projection run and the
original 43-fiber census was not recoverable from this workspace.  The
manuscript replaces their conclusions by algebraic proofs and does not claim
that this repository reproduces those historical searches.
