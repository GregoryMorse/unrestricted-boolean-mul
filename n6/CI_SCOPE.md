# Separate n6 verification scope

`models-upper.yml` checks the semantic model comparisons and the explicit
17-product 6-by-6 and 16-product 5-by-6 upper witnesses, with eleven enforced
axiom audits. The fixed witness transcription is independently replayed.

`n6-bilinear.yml` checks the proved hyperplane substitution, orbit reduction,
and output-profile/capacity interfaces. Their numerical lower-bound
hypotheses remain explicit. It also verifies the unchanged 50-file handoff
manifest, archived-log consistency and positive witnesses. Those checks
are **not** fresh exhaustive enumeration or Lean proofs of the exact ranks.

No C14/CF/CP certificate campaign, dense endpoint work, full-root research
build, manuscript upload, or claim of full lower-bound closure is included.
The original handoff can contain historical completion language; this scope
statement governs what these workflows establish.

On bounded Linux after restoring the Mathlib cache:

```sh
python3 scripts/ci_verify.py --profile models-upper --build
python3 scripts/ci_verify.py --profile n6-bilinear --build
python3 n6/quick.py
```
