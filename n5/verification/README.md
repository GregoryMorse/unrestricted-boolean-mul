# `n = 5` regression checks

This directory is for finite checks used during discovery or as regression
tests.  They are not proof premises and must not be imported into Lean.

The initial handoff contains the independent-shadow check for the `W_*`
envelope:

- [`wstar_independent_shadow_check.cpp`](wstar_independent_shadow_check.cpp)
- [`wstar_independent_shadow_check_results.txt`](wstar_independent_shadow_check_results.txt)

It also contains
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

The final `CONSTANT` line is the pass condition.  On the 2026-08-31 audit
container the replay completed successfully and matched the recorded counts.

The much larger 166,199,235-presentation projection run, 43-fiber census, and
other exploratory programs are not present in this snapshot.  The manuscript
replaces their conclusions by algebraic proofs and does not claim that this
repository reproduces those historical searches.
