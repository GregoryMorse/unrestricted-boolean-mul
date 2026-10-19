# Palomar submission preparation (n4 only)

## Current toolchain successor (2026-10-19)

Use the exact public commit checked by the fresh Lean **4.35.0-rc3** CI
and official source-preparation report. Do not reuse the `n4-arxiv-v4`
source commit: it pins historical Lean 4.33.1. All submitted Lean files
have been ported to the module system. The headline results, permitted
axioms and mathematical model are unchanged.

The first rc3 submission exposed a Comparator mismatch in the generated
`bVar._proof_2` auxiliary. Input embeddings now use explicit standard `Fin`
maps on both sides instead of separately generated `omega` proof auxiliaries.
Use a fresh CI report that includes both actual sandboxed Comparator commands;
the earlier compile/leanchecker-only rc3 report did not test that comparison.
No declaration or auxiliary has been added to the permitted-axiom list or
exempted as an extra Comparator hole.

The GitHub `palomar.yml` workflow performs current official preliminary
checks. The full upstream workflow now requires a provisioned Namespace
runner, so full verification is to be requested through Palomar itself.
A preliminary PASS or a skipped optional full job is not kernel acceptance.
The current official pipeline pin is
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
Use the existing n4 Palomar registration identity when updating its record;
do not create a duplicate registration. The September preparation below is
retained as historical context, not as this successor's verification report.

Gregory Morse reports that n4 has been registered and requests a new tag to
resubmit the MSC metadata correction. This document prepares that successor;
no new intake or registration is performed by these repository changes.
The author remains responsible for the submission and maintainer attestation.

| Form field | Prepared value |
| --- | --- |
| Repository | `GregoryMorse/unrestricted-boolean-mul` |
| Commit | Exact public 40-character SHA from the current 4.35.0-rc3 CI report; never an old release/tag string |
| Comparator configuration | `comparator.json` |
| Project directory | blank (repository root) |
| Formalization metadata | `formalization.yaml` |
| Existing Palomar ID | the existing registered n4 identity, confirmed from the public record |
| Relationship | `maintainer` — responsible author/maintainer |
| Approval evidence | not needed for the responsible maintainer's own attestation |
| Notes | Published n4 source-based formalization; toolchain/CI and Comparator update, no n5/n6 lower-bound claim. |
| Preliminary-check override | none |

The selected claims and source correspondence are in
[PALOMAR_AUDIT.md](PALOMAR_AUDIT.md). Metadata previews the public name,
description, author, AI roles, MIT license and source-based origin.
Classifications `cs.CC` and `cs.DS` follow the paper's categories. MSC2020
codes match the [arXiv record](https://arxiv.org/abs/2608.30238): **68Q06
(primary); 68Q17, 68W30, 15A75, 94D10 (secondary)**. Schema v0.4 stores a
flat list, so the primary code is first and its role is also documented in
the YAML comment. No definition hole is compared.

## MSC metadata correction (2026-09-22)

The v3 metadata inadvertently left `msc2020` empty. The optional schema
field accepted that omission; it was not a theorem or kernel-verification
failure. The v4 successor restores all five published classifications and
adds a regression check. It does not change the Lean proofs, their stated
hypotheses, the toolchain, Comparator, or workflow scope. Historical audit
reports retain their original commit identifiers. Use v4's exact commit
and its own verification results for the author's requested resubmission;
do not relabel a v3 report as verification of v4.

## Completed evidence and exact-commit handoff

The [completed audit](PALOMAR_AUDIT.md) records the passing proof checks on
`a6bb4bd5e6aa89d89783fa41f8dfc8d5c5a5b430`, replacing the initial inspection.
The release's `SUBMISSION_PACKET.md` and `submission-fields.json` identify
the exact final public commit, with its own official report. This avoids
embedding the hash of this document's containing commit inside itself.

The evidence consists of:

1. A clean checkout and complete source/configuration manifest.
2. Passing n4 CI: default build, six enforced axiom audits and leanchecker.
3. Passing separate models-upper, n5 and n6 jobs, with their scope kept distinct.
4. Schema/static checks and official Palomar `mode: full` report `status: pass`.
   `.github/workflows/palomar.yml` pins both the reusable workflow and
   `pipeline_commit` to `3561d237dcc4b28482558ad28a64d767d7cc8615`.
5. Final live registration-identity check and exact SHA/field packet.

For any documentation-only successor, use its actual attached report rather
than assuming a prior run verified a new Git commit. Gregory Morse can then
decide separately whether to authorize intake.
Permanent registration requires a later, separate decision on the actual
review and its `review_sha256`. A release tag is not a Palomar proof tag.
