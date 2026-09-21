# Palomar submission preparation (n4 only)

No submission or registration has been performed. Gregory Morse confirmed
responsible-author/maintainer status and authorized the official mechanical
preflight, but not intake or permanent registration.

| Form field | Prepared value |
| --- | --- |
| Repository | `GregoryMorse/unrestricted-boolean-mul` |
| Commit | Full public SHA in the final `n4-arxiv-v3` release notes; never a branch/tag string |
| Comparator configuration | `comparator.json` |
| Project directory | blank (repository root) |
| Formalization metadata | `formalization.yaml` |
| Existing Palomar ID | blank unless the final registration-identity lookup finds an existing entry |
| Relationship | `maintainer` — responsible author/maintainer |
| Approval evidence | not needed for the responsible maintainer's own attestation |
| Notes | Published n4 source-based formalization; toolchain/CI and Comparator update, no n5/n6 lower-bound claim. |
| Preliminary-check override | none |

The selected claims and source correspondence are in
[PALOMAR_AUDIT.md](PALOMAR_AUDIT.md). Metadata previews the public name,
description, author, AI roles, MIT license and source-based origin.
Classifications `cs.CC` and `cs.DS` follow the paper's categories; no MSC
classification is invented. No definition hole is compared.

## Evidence required for the final SHA

1. A clean checkout of the public commit, with all required files tracked.
2. Passing n4 CI: default build, six enforced axiom audits and leanchecker.
3. Passing separate models-upper, n5 and n6 jobs, with their scope kept distinct.
4. Schema/static checks and official Palomar `mode: full` report `status: pass`.
   `.github/workflows/palomar.yml` pins both the reusable workflow and
   `pipeline_commit` to `3561d237dcc4b28482558ad28a64d767d7cc8615`.
5. Final live registration-identity check and exact SHA/field packet.

Only after these gates should the user decide whether to authorize intake.
Permanent registration requires a later, separate decision on the actual
review and its `review_sha256`. A release tag is not a Palomar proof tag.
