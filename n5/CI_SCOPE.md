# Separate n5 verification scope

`n5.yml` builds only the import closure of Capacity, QuadraticFlattening and
Upper, then enforces all thirteen audits in `Paper2Audit.lean`. These are
the proved quadratic-capacity results, the all-quadratic twelve-gate
exclusion and the thirteen-product upper witness. The closure does not
import the withdrawn restart/SC3 repair chain.

A green job does **not** prove unrestricted `MC(Mul 5)=13`, complete any
research manuscript, or certify all exploratory n5 modules. The previously
broad default research imports and audit are preserved locally as
`UnrestrictedBooleanMul/Research.lean` and `n5/ResearchAudit.lean`, outside
this scoped release. No manuscript is published here.

Run manually on bounded Linux after restoring the pinned Mathlib cache:
`python3 scripts/ci_verify.py --profile n5 --build`.
