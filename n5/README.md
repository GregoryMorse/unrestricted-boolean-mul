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
- a kernel-checked Lean proof that the nine output coordinates are linearly
  independent;
- the resulting checked dimension bound that every circuit for `Mul 5` has at
  least nine AND gates;
- an explicit thirteen-product bilinear circuit, with all nine recombination
  identities checked by ring normalization;
- the 45-dimensional squarefree quadratic space, nine-dimensional target,
  and 36-dimensional quotient;
- the zero-fiber theorem, target--defect exact sequence, and exact relation-map
  formula;
- exact classification of the 43 effective fibers and the full strong
  mixed-place exclusion; and
- a choice-independent defect-capacity construction with the specialized
  displacement/relation-gift formula;
- exact local and global represented-place profiles for its intrinsic
  displacement space; and
- the four-dimensional cubic kernel and complete missing-coset shadow
  exclusion for the unique non-rational degree-two translate;
- exact algebraic fixed-block classifications for all three nonextremal
  two-defect envelopes, with explicit rank-two completions and fixed nonzero
  minors for equations (10.6), (10.8), and (10.11);
- the normalized extremal degree-two-plus-rational-jet envelope, including
  its exact eight-dimensional size, six-dimensional target intersection,
  defect two, and stable-suffix interface;
- the algebraic companion classification at all three rational places into
  the regular Koszul-kernel case or one of the three exceptional planes
  through that rational direction; and
- a kernel-checked two-gate, defect-legal counterexample to the history-free
  anchored stable-envelope interface (and, in particular, its rational-zero
  `001` anchor-shadow obligation), showing that the suffix reduction must
  retain an additional reachability or gate-cost invariant; and
- an exact-length defect-legal suffix relation, its target-plus-defect gain
  ledger, and a circuit-tail bridge that charges every remaining AND gate;
- a corrected cost-preserving final regime split reducing the twelve-gate
  exclusion to two circuit-facing algebraic obligations, without assuming
  the refuted fixed-envelope saturation theorem; and
- a dependency-ordered handoff for the closed-place and nonlinear-feedback
  proof needed to strengthen nine to thirteen.

The checked declarations are in:

- [`../UnrestrictedBooleanMul/N5/Target.lean`](../UnrestrictedBooleanMul/N5/Target.lean)
- [`../UnrestrictedBooleanMul/N5/Upper.lean`](../UnrestrictedBooleanMul/N5/Upper.lean)
- [`../UnrestrictedBooleanMul/N5/Statement.lean`](../UnrestrictedBooleanMul/N5/Statement.lean)
- [`../UnrestrictedBooleanMul/N5/QuadraticSpace.lean`](../UnrestrictedBooleanMul/N5/QuadraticSpace.lean)
- [`../UnrestrictedBooleanMul/N5/Fiber.lean`](../UnrestrictedBooleanMul/N5/Fiber.lean)
- [`../UnrestrictedBooleanMul/N5/RelationMap.lean`](../UnrestrictedBooleanMul/N5/RelationMap.lean)
- [`../UnrestrictedBooleanMul/N5/ClosedPlaces.lean`](../UnrestrictedBooleanMul/N5/ClosedPlaces.lean)
- [`../UnrestrictedBooleanMul/N5/HankelSupport.lean`](../UnrestrictedBooleanMul/N5/HankelSupport.lean)
- [`../UnrestrictedBooleanMul/N5/LocalKlein.lean`](../UnrestrictedBooleanMul/N5/LocalKlein.lean)
- [`../UnrestrictedBooleanMul/N5/EffectiveFibers.lean`](../UnrestrictedBooleanMul/N5/EffectiveFibers.lean)
- [`../UnrestrictedBooleanMul/N5/EffectiveClassification.lean`](../UnrestrictedBooleanMul/N5/EffectiveClassification.lean)
- [`../UnrestrictedBooleanMul/N5/MixedPlaceDegreeInfinity.lean`](../UnrestrictedBooleanMul/N5/MixedPlaceDegreeInfinity.lean)
- [`../UnrestrictedBooleanMul/N5/Displacement.lean`](../UnrestrictedBooleanMul/N5/Displacement.lean)
- [`../UnrestrictedBooleanMul/N5/DisplacementProfile.lean`](../UnrestrictedBooleanMul/N5/DisplacementProfile.lean)

No theorem named `mc_mul_five` is present yet, and the new declarations above
do not yet constitute the final lower bound. This directory must not be
described as a Lean certificate for the paper until that final theorem has
also been kernel checked.

In particular, `N5.not_firstOrderSaturation` proves that even the
circuit-facing fixed-envelope premise is false: a genuine two-gate
all-quadratic prefix of defect at most one admits a two-gate defect-legal
escape exposing the missing target coordinate.  The companion theorem
`N5.not_anchoredFirstOrderStability` gives the same failure for the canonical
history-free state, and the smaller theorem
`N5.not_nonzeroRationalZeroAnchoredEnvelopeFunctionalCase_001` identifies the
same obstruction in the rational-zero local coordinates.  The final proof
must replace that route with a circuit-facing invariant that remembers which
correction products were actually born (or charges their gate cost); assuming
the three scalar cases, anchored stability, or fixed-envelope saturation
would be unsound.

The replacement interface is now checked in `N5/CostedSuffix.lean` and
`N5/CostedRegimeClosure.lean`. It retains the exact suffix length and proves
that target-rank gain plus quotient-defect gain is at most that length. The
final circuit bookkeeping is complete; the two predicates
`CostedTwoDefectQuadraticPrefixes` and
`CostedFirstOrderQuadraticPrefixes` remain the honest algebraic completion
obligations.

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
