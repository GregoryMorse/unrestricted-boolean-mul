# Five-term binary polynomial multiplication (`n = 5`)

The associated manuscript proves

```text
MC(Mul5) = 13
```

for unrestricted XOR--AND circuits.  Nonlinear intermediate wires may be
reused, so the theorem is stronger than the classical bilinear and quadratic
rank statement for this instance.

## Current formalization status

The Lean formalization is in progress and is not a premise of the manuscript.
The repository currently contains:

- a separated canonical proposition `UnrestrictedBooleanMul.N5.MainStatement`;
- nine private target coordinates for `Mul 5`;
- a staged Lean proof that the nine output coordinates are linearly
  independent;
- the resulting staged dimension bound that every circuit for `Mul 5` has at
  least nine AND gates;
- an explicit thirteen-product bilinear circuit, with all nine recombination
  identities staged for ring normalization; and
- a dependency-ordered handoff for the closed-place and nonlinear-feedback
  proof needed to strengthen nine to thirteen.

The current declarations awaiting their first clean kernel replay are in:

- [`../UnrestrictedBooleanMul/N5/Target.lean`](../UnrestrictedBooleanMul/N5/Target.lean)
- [`../UnrestrictedBooleanMul/N5/Upper.lean`](../UnrestrictedBooleanMul/N5/Upper.lean)
- [`../UnrestrictedBooleanMul/N5/Statement.lean`](../UnrestrictedBooleanMul/N5/Statement.lean)

No theorem named `mc_mul_five` is present yet, and the new declarations above
must not be described as checked until the pinned toolchain has replayed them.
In particular, this directory must not be described as a Lean certificate for
the paper until the final lower bound and staged upper circuit have both been
kernel checked.

## Formalization handoff

- [`FORMALIZATION_HANDOFF.md`](FORMALIZATION_HANDOFF.md) fixes the module
  architecture, dependency order, trust policy, and completion gates.
- [`THEOREM_LEDGER.md`](THEOREM_LEDGER.md) maps every load-bearing manuscript
  result to its planned Lean module and current status.
- [`verification/`](verification/) contains curated regression checks and the
  recovered Python discovery programs for the later envelopes.  They are
  explicitly not proof premises, but preserve useful coordinate models and
  search structure for the Lean work.

The existing `n = 4` development is the reusable framework.  It already
contains the unrestricted circuit semantics, Boolean ANFs, homogeneous-degree
bookkeeping, exterior algebra, target projections, quadratic-prefix
normalization, and feedback/idempotence machinery.  The `n = 5` work should
extend those interfaces without rewriting the checked `n = 4` proof.

## Trust and release policy

The completed proof must:

1. build under the pinned `lean-toolchain` and `lake-manifest.json`;
2. contain no `sorry`, `admit`, project axiom, `native_decide`, or unchecked
   generated theorem;
3. expose the final theorem as `UnrestrictedBooleanMul.N5.mc_mul_five`;
4. add that declaration to `AxiomAudit.lean` and record the output;
5. keep the formal statement separated from the proof for a later independent
   statement-fidelity audit; and
6. receive a new pinned release only after a clean anonymous-checkout replay.

The manuscript is distributed through arXiv rather than copied into this
software repository.
