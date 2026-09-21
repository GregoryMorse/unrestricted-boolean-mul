# Palomar preparation audit

Initial inspection: 2026-09-21. No submission or registration performed.

## Initial verdict: NOT READY — REPAIRABLE

The supplied `palomar-submission-auditor.zip` was inspected before repair.
Its static preflight ran against the original working tree and exited 1:
three errors (dirty worktree, missing Comparator configuration, missing
formalization metadata), eight mandatory checks unverified, five static passes.
The starting public commit was `07afc265e72c66fd39f0a4ba9635ce39271d703d`.
The passing public run 35561693014 verified that commit, not the uncommitted
Lean 4.33.1 migration and research files.

| ID | Gate | Initial status | Finding / required action |
| --- | --- | --- | --- |
| M-01 | Snapshot | FAIL | Freeze only the reviewed delivery; preserve unrelated dirty research. |
| M-02 | CI scope | FAIL | `lean.yml` and the default root included n5 repair work; isolate n4. |
| M-03 | Statement | FAIL | Add a Mathlib-only Challenge, distinct proved Solution, and Comparator config. |
| M-04 | Metadata | FAIL | Add source-based metadata for the published paper and explicit automation/scope. |
| M-05 | Proof | UNVERIFIED | Rebuild the exact new public snapshot, enforce axiom audits, replay n4. |
| M-06 | Palomar | UNVERIFIED | Official full pinned workflow must pass, including Comparator and NanoDa. |
| M-07 | Provenance | WARNING | README lacked the announced arXiv identifier; citation overstated n5 closure. |
| M-08 | Authorization | UNVERIFIED | Intake/registration are not authorized by this preparation request. |

The existing MIT license and pinned Lake layout are present. The old
`n4-arxiv-v2` release, commit `2ebc0cf42039e4b5de84cb7f9d97cad4791c669d`,
is preserved. The new tag will be created only after n4 verification passes.

## Live-policy evidence

Policy: `PalomarRegistry/PalomarPolicy` at
`792c7c0b9e798bd02719e795ef11fa2b5929e067`.
Official verifier: `PalomarRegistry/PalomarSubmission` at
`3561d237dcc4b28482558ad28a64d767d7cc8615`.
Template reference: `PalomarRegistry/PalomarTemplate` at
`d06eea17a234d0936798a78fa23f8a69e80374a7`.

The current [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md)
requires an independently auditable Challenge and only the standard three
axioms in Solution. [Agent preflight instructions](https://submit.palomar-registry.org/llms.txt)
add the official full-workflow gate. Preparation is not intake, and intake
is not permanent registration. The policy permits zero MSC codes despite
the overview recommending at least one; only defensible codes will be used.

## Semantic alignment

All compared names are in `UnrestrictedBooleanMul` (the last two in `N4`).

| Declaration | Statement | Source |
| --- | --- | --- |
| `mc_mul_zero` | Empty-input complexity 0 | Proposition 2.3 |
| `mc_mul_one` | One-term complexity 1 | Proposition 2.3 |
| `mc_mul_two` | Two-term complexity 3 | Proposition 2.3 |
| `mc_mul_three` | Three-term unrestricted complexity 6 | Proposition 2.4 |
| `N4.no_eight_gate_circuit` | No eight-AND four-term circuit | Proof of Theorem 9.1 |
| `N4.mc_mul_four` | Four-term unrestricted complexity 9 | Theorem 9.1 |

Source: Gregory Morse, [arXiv:2608.30238v1](https://arxiv.org/html/2608.30238v1),
Definition 2.1 and the cited results. Constants and XOR are free. AND
inputs may use all previous nonlinear wires. Monomial union implements
Boolean idempotence. Outputs are convolution coefficients, not integer
multiplication. The n=0 output type is empty. The minimum's fallback zero
does not affect these targets, which have explicit circuits.

The n3 Lean lower bound uses an internal algebraic certificate rather than
taking the paper's cited coding lower bound as a premise. This is a proof
method difference, not a weaker statement. Nothing here solves the general
Boyar–Find problem or the open unrestricted n5 / bilinear n6 lower bounds.

The submission formalizes this published source; it does not claim a new
result or independent novelty. Its audience is researchers in Boolean
circuit complexity, finite-field arithmetic, and proof verification.
VibeMathed's [record](https://vibemathed.com/problem/unrestricted-multiplicative-complexity-mul4)
reports a historical independent kernel replay, not an independent audit
of mathematical statement alignment and not verification of this new SHA.

## Finalization gates

The final public SHA, exact CI runs, post-repair preflight and complete form
packet will be recorded separately. Until they are present and the official
mechanical report passes, readiness is not asserted.

Submission performed: no. Registration performed: no.
