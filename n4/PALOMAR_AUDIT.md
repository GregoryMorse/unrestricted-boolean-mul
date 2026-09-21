# Palomar audit — completed n4 verification

Audit date: 2026-09-21. **READY WITH WARNINGS** for the verified proof snapshot
identified below. All required checks for that snapshot passed; the warnings
are ordinary Lean lint messages and a GitHub action-runtime deprecation
notice. There are no blocking proof, axiom, metadata or statement-interface
findings.

No Palomar submission or registration has been performed.

## Verified snapshot and evidence

Repository: `GregoryMorse/unrestricted-boolean-mul`.
Verified proof snapshot:
[`a6bb4bd5e6aa89d89783fa41f8dfc8d5c5a5b430`](https://github.com/GregoryMorse/unrestricted-boolean-mul/tree/a6bb4bd5e6aa89d89783fa41f8dfc8d5c5a5b430).

This is the completed audit, replacing the initial pre-repair checklist.
The initial findings remain in Git history; they are not current findings.

| Gate | Result | Completed evidence |
| --- | --- | --- |
| Public reproducible snapshot | PASS | Clean detached checkout of the public commit; committed toolchain and dependency pins; 98-file source/configuration manifest. |
| n4 isolation | PASS | Default build and `lean.yml` select 78 local modules, with no n5/n6/Research imports. Seven CI regression tests passed. |
| Build and declared results | PASS | [n4 CI 35626656382](https://github.com/GregoryMorse/unrestricted-boolean-mul/actions/runs/35626656382) completed successfully, including default `lake build`, Challenge and Solution. |
| Axiom audit | PASS | All six selected declarations have exactly `propext`, `Classical.choice`, `Quot.sound`; no extra axiom or admitted proof. |
| Lean replay | PASS | The same CI run executed `lake env leanchecker UnrestrictedBooleanMul`: exit 0, 223.557 seconds. |
| Protected statement comparison | PASS | [Official full Palomar run 35626656656](https://github.com/GregoryMorse/unrestricted-boolean-mul/actions/runs/35626656656) accepted all six theorem names and their Challenge/Solution correspondence. |
| Independent kernel verification | PASS | The official report records both “nanoda kernel accepts the solution” and “Lean default kernel accepts the solution”. |
| Challenge provenance | PASS | Official trust level `high`; Mathlib-only statement dependencies, no untrusted sources; 131 lines, 5,346 bytes. |
| Metadata, license and dependencies | PASS | Official full verification accepted v0.4 metadata, MIT license, classifications and pinned public dependencies; independent schema validation also passed. |
| Responsibility and scope | PASS | Gregory Morse confirmed responsible-author/maintainer status and authorized verification. Intake and registration were not authorized or performed. |

The official mechanical report says `status: pass`, `stage: complete`,
checked at **2026-09-21T17:18:28Z**, with empty error and warning lists.
The n4 CI job passed in 46m10s. Its report has `complete: true`, every command
exited 0, and its proof-source hashes match the clean public checkout.

The [v3 release](https://github.com/GregoryMorse/unrestricted-boolean-mul/releases/tag/n4-arxiv-v3)
carries the reports, exact submission fields and checksum manifests.
For a later documentation-only correction, its release packet records the
new exact commit and that commit's verification separately. A passing earlier
run is never relabelled as a run on a different commit.

## Statement-by-statement audit

All names have prefix `UnrestrictedBooleanMul.`.

| Declaration | Formal conclusion | Published source |
| --- | --- | --- |
| `mc_mul_zero` | `MC(Mul 0) = 0` | Proposition 2.3 |
| `mc_mul_one` | `MC(Mul 1) = 1` | Proposition 2.3 |
| `mc_mul_two` | `MC(Mul 2) = 3` | Proposition 2.3 |
| `mc_mul_three` | `MC(Mul 3) = 6` | Proposition 2.4 |
| `N4.no_eight_gate_circuit` | No eight-AND circuit computes `Mul 4` | Proof of Theorem 9.1 |
| `N4.mc_mul_four` | `MC(Mul 4) = 9` | Theorem 9.1 |

Source: Gregory Morse,
[arXiv:2608.30238v1](https://arxiv.org/html/2608.30238v1), Definition 2.1
and the cited results.

The audited model is unrestricted XOR–AND complexity over Boolean ANFs.
Constants and XOR are free; each AND input may use affine inputs and any
earlier nonlinear wires. Monomial union enforces Boolean idempotence.
Outputs are polynomial convolution coefficients, not integer multiplication.
The empty `n=0` output type is intentional. The minimum's fallback value
does not affect these targets because explicit circuits exist.

The n3 lower-bound proof is internal and algebraic rather than importing
the paper's cited coding bound. This changes the proof method, not the
statement. Six deliberate Challenge theorem holes state the independent
problem; Solution does not import Challenge and has no such premise.
No statement was weakened to obtain Comparator acceptance.

## Provenance, review and scope

This is a substantive source-based formalization, not a novelty claim or a
thin wrapper. Its audience is Boolean circuit complexity, finite-field
arithmetic and formal verification: the n4 result permits nonlinear
feedback, beyond bilinear/quadratic restrictions.

Gregory Morse is the paper's author and responsible maintainer.
`formalization.yaml` records human responsibility and AI assistance,
including the original development/referee roles disclosed in the paper.
It does not invent unrecorded costs or imply independent human peer review.

The published paper's
[`n4-arxiv-v2`](https://github.com/GregoryMorse/unrestricted-boolean-mul/tree/2ebc0cf42039e4b5de84cb7f9d97cad4791c669d)
snapshot remains unchanged. The
[VibeMathed record](https://vibemathed.com/problem/unrestricted-multiplicative-complexity-mul4)
concerns that historical replay, not the new commit and not an independent
statement-anchoring review. Palomar mechanical acceptance is not editorial
acceptance or registration.

Separate workflows passed for
[models/upper witnesses](https://github.com/GregoryMorse/unrestricted-boolean-mul/actions/runs/35620596935),
[n5 quadratic geometry](https://github.com/GregoryMorse/unrestricted-boolean-mul/actions/runs/35620600594),
and [n6 reductions](https://github.com/GregoryMorse/unrestricted-boolean-mul/actions/runs/35620604923).
Their recorded source hashes match the verified n4 snapshot. They do not
claim unrestricted n5 closure or a full Lean n6 bilinear lower bound.
The archived computer-assisted n6 argument is a separate verification scope.

## Toolchain, policy and reproduction

- Lean: `leanprover/lean4:v4.33.1`, compiler
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Palomar policy: `792c7c0b9e798bd02719e795ef11fa2b5929e067`.
- Official workflow and `pipeline_commit`:
  `3561d237dcc4b28482558ad28a64d767d7cc8615`.
- Comparator: `575674928e239f5bc452aab72d1dd7b0f1326494`.
- NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`.

Official policy, protocol and revision heads were refreshed on 2026-09-21;
the policy/verifier/schema revisions were unchanged. Binding policy permits
zero MSC codes, despite the overview's recommendation. The accepted metadata
uses `cs.CC`, `cs.DS` and no invented MSC classification.

Reproduction on a sufficiently provisioned Linux runner:

```sh
python3 scripts/check_n4_manifest.py
python3 -m unittest discover -s scripts -p test_ci_verify.py -v
lake exe cache get
python3 scripts/ci_verify.py --profile n4 --build --replay
```

The CI driver enforces one CPU, an 8-GiB Lean limit, a 12-GiB address-space
cap and at least 14 GiB physical RAM. The official full check is dispatched
through `.github/workflows/palomar.yml` with the exact public commit.
No heavy Windows build or use of either research server was required.

## Hashes are not circular proof evidence

This audit does **not** contain its own file hash or the hash of the commit
that first adds this completed report. The commit cited above identifies the
already verified proof snapshot, not this document.

`n4/LEAN_SHA256SUMS.txt` hashes the source/configuration files, including this
audit, but deliberately excludes itself. The release's separate
`SHA256SUMS.txt` likewise excludes itself. The paper-specific
`n4/SHA256SUMS.txt` covers its README, the inner Lean manifest and regression
artifacts; it also excludes itself. Thus the hash references run from source
files through separate manifests, never back into the same manifest.
The manifest checker is hashed as
an ordinary file; it does not embed its own digest. These checks detect byte
changes. They do not prove the theorem or certify the audit's truth:
the completed CI, Comparator and independent kernel runs provide that evidence.

## Handoff

For the verified proof snapshot above:

- Palomar readiness: **READY WITH WARNINGS**.
- Blocking findings: **0**.
- Unverified mandatory checks: **0**.
- Non-blocking warnings: Lean lint and GitHub action-runtime notices only.
- Submission performed: **no**.
- Registration performed: **no**.

Use [SUBMISSION.md](SUBMISSION.md) and the release's exact-commit
`submission-fields.json` / `SUBMISSION_PACKET.md` for a later intake
decision. Before intake, match its commit to the attached official passing
mechanical report. Do not use a branch name, mutable tag, or assumed result.
