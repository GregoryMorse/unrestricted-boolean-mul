# n=5 lower-bound repair state

This note is the crash-safe mathematical handoff for the current repair.  It
is not a substitute for a proof and must not be cited as establishing
`MC(Mul 5) = 13`.

## Withdrawn step

The repeated use of the restart clause in manuscript Lemma 9.1 is invalid
after a genuinely high wire has been born.  If a retained product has an old
high class, subtracting an old representative produces a new quadratic wire,
but its quadratic quotient need not contain a decomposable representative.
Consequently it cannot automatically be appended to the decomposable
presentation used by intrinsic-capacity replay.

One exact counterexample starts from
`Aff + <r_0,r_1,r_infinity>`.  The products

```
g = (a_2 + b_2)(a_2 + r_0),
h = (a_2 + b_2 + b_0)(a_2 + a_0 + r_0)
```

have the same nonzero high part.  Their sum `z = g + h` is quadratic, while
every Hankel-target translate of its quadratic form has alternating rank at
least four.  Thus the returned quotient class is unpopulated.

The TeX and release archive under `paper/n5-handoff` remain blocked until the
replacement chain below is complete.

## Implemented replacement chain

The following distinctions are now explicit in Lean.

1. `CapacityRestart.lean` applies only when the first retained gate starts
   from a purely quadratic intrinsic-capacity state.  In that setting its
   factors are quadratic and a retained quadratic output has a decomposable
   quadratic form.
2. `QuadraticReturn.lean` treats the post-high alternative.  At fixed high
   rank, an old representative can be subtracted to expose the literal new
   quadratic section without changing the generated wire state.
3. `QuadraticReturnSecant.lean` proves that an equal-high return supported in
   the first-order envelope does not enlarge its Hankel-target intersection.
   This uses the complete algebraic envelope-shadow theorem and includes
   dependent, independent, same-plane, and cross-plane products.
4. `QuadraticReturnFeedback.lean` factors the feedback question into its
   actual algebraic branches.  For an unpopulated section it excludes a
   zero-colour target escape even with a correction from the whole returned
   quadratic section.  It also generalizes the rank-one Boolean-absorption
   contradiction from a decomposable anchor to any quadratic section with
   exact first-order target intersection.  If both the quadratic factor and
   the old correction use the returned section, their section coefficients
   cancel and the missing-coset exterior kernel gives the same contradiction.
   The populated/unpopulated split is now exhaustive in Lean.  In the
   populated branch the returned form is exposed as a decomposable lift plus
   an explicit target row, so later costed replay cannot absorb that row for
   free.
   Consequently every remaining normalized rank-one escape is forced into
   one asymmetric case: the correction uses the returned section while the
   quadratic factor stays in the old first-order envelope.
5. `QuadraticReturnOrbit.lean` closes that asymmetric case for four fixed
   rational-return representatives.  The proof is an exterior-kernel
   calculation with sparse quartic coordinates; the two rank-four
   representatives are killed by nine triangular coordinates, and the two
   remaining representatives use the missing-coset functional.  These are
   witnesses and regression cases, not representatives of all returned
   quadratic-section orbits.
6. `QuadraticReturnRankTwo.lean` proves the post-return rank-two budget
   contradiction.  An unpopulated return contributes positive quadratic
   defect, while two independent localized high colours and their product
   contribute three high directions, contradicting total defect at most
   three.
7. `QuadraticReturnKernel.lean` and `QuadraticReturnHankelKernel.lean`
   reduce a target exterior annihilator of an arbitrary unpopulated section
   to zero or one of the three rational rank-one directions.  This is the
   sharp section-only statement: the rational alternatives cannot be
   removed from unpopulatedness alone.
8. `quadratic_return_history_polynomial.py` now closes the previously open
   rational branch at the parameterized Boolean-algebra level while retaining
   the old high representative.  The `(1,2)` and `(1,3)` factor pairs have
   direct degree-one identities in all rational directions.  Rational-place
   symmetry reduces `(0,1)` and `(1,1)` to aligned and off-axis directions;
   every off-axis branch is degree one, and only the six-element
   `GL(2,F₂)` aligned orbit needs a second step.  Splitting the single
   returned-section correction bit there gives four sparse `liftstd` unit
   certificates (16, 16, 13, and 13 semantic terms), all independently
   replayed by the Python Boolean-polynomial engine.  No unpopulatedness or
   nonzero-high premise is used in these identities.  The exact ledger is in
   `quadratic_return_history_results.txt`.  The raw, non-eliminated off-axis
   `(0,1)` leaf is now a kernel-checked explicit identity in
   `N5/QuadraticReturnHistoryRaw.lean`, with its 71 coordinates named by the
   checked interface in `N5/QuadraticReturnHistoryModel.lean`.
   `N5/QuadraticReturnHistorySemantic.lean` identifies every raw equation
   with its literal return, feedback, or genuine quadratic-quotient
   coordinate and exposes the canonical off-axis `(0,1)` missing-coset
   exclusion.  The six direct `(1,2)` and `(1,3)` leaves are likewise fully
   connected in `N5/QuadraticReturnHistory*Semantic.lean`: all 198 selected
   equations are discharged from the literal quadratic-history hypotheses,
   and each generated certificate now ends in a circuit-facing
   first-order-missing-functional theorem.  The normalized off-axis
   `(1,1), R1` leaf is also kernel-connected: its 28 raw equations retain
   the equal-factor difference chart `m = mDifference + ell`, and its
   semantic bridge explicitly applies Boolean idempotence before exposing
   the same circuit-facing theorem.  The four compact aligned exceptional
   unit identities (both returned-section correction bits for `(0,1)` and
   `(1,1)`) are now also replayed by Lean in the generated
   `N5/QuadraticReturnHistory*AlignedCorrection*Raw.lean` modules.  They use
   16, 16, 13, and 13 reduced semantic generators, respectively.  Their
   affine elimination is now also kernel-replayed: the generated
   `N5/QuadraticReturnHistory*Normalization.lean` modules identify each
   compact generator with an entry of a shared original-equation base, while
   the four `N5/QuadraticReturnHistory*Semantic.lean` modules prove every one
   of the 29 substitutions by explicit ideal-membership certificates.  The
   shared bases identify all required return-high, feedback-high, and quotient
   equations with literal ANF coefficients, including the two same-side
   quotient rows omitted from the earlier mixed table.
   `N5/QuadraticReturnHistoryAlignedSemantic.lean` splits the returned-section
   correction bit and excludes both aligned normal forms with no preprocessing
   assumption.  The direct off-axis `(1,1),RInf` certificate is also
   kernel-checked.  The much larger `(0,1),RInf` candidate has been divided
   into bounded product leaves and assemblies, but its aggregate is not yet a
   theorem: an independent parser finds a 576-monomial residual between the
   50 stored products and the stated target.  The unverified chart module is
   retained as the intended twelve-leaf interface, but must not be cited until
   that residual is repaired and the aggregate and semantic bridge compile.
   Finally,
   `N5/QuadraticReturnFactorPair.lean` gives the finite algebraic simultaneous
   normalization of every admissible rational factor-colour pair into
   `(0,1)`, `(1,1)`, `(1,2)`, or `(1,3)`.  It explicitly distinguishes the
   third rank-one point `rInfinity` from the incident rank-two colour
   `r0 + r1`.  What remains is the circuit/ANF transport that extracts this
   admissible pair and, in the two aligned cases, the checked normal-form
   hypotheses.

The exact counterexample has also been retested with its history restored.
Keeping its already-born high representative and allowing every correction
from the returned quadratic state, none of the 2,048 lower factors with
quadratic part `r0` reaches the missing target coset.  This finite calculation
is recorded by `quadratic_return_feedback_probe.py`.  It does not prove the
parameterized return theorem, but confirms that the retained representative
contains information discarded by the false section-only formulation.

The broad normalized SAT encoding was run for 60 seconds on each of the 220
possible twelve-gate defect chronologies.  Every branch returned `unknown`;
there was neither a circuit witness nor an UNSAT certificate.  The global SAT
route is therefore retired rather than being treated as evidence for the
lower bound.

These modules are checked only by the pinned Linux CI.  The focused replay
bridge, including the four canonical rank-one return kernels and the generic
rank-two defect budget, compiles with pinned Lean 4.32.1.  Windows Lean is not
used for this repair.  A complete repository build and `leanchecker` replay
are reserved for a stable closure checkpoint.

## Remaining closure obligations

The paper cannot be unblocked until all of the following are proved and then
connected to the exact-cost circuit suffix.

- Charge the explicit target row in the now-formal populated-return
  decomposition; the populated/unpopulated quotient split itself is complete.
- Connect the now-formal four-type factor-pair normalization and twelve-leaf
  normalized history chart to actual circuit factors.  First repair and
  kernel-check the outstanding `(0,1),RInf` 576-monomial residual.  The direct
  `(1,2)` and `(1,3)` certificates, the other off-axis directions, and the four
  aligned unit certificates are kernel-connected to literal ANF semantics.
  The remaining transport must extract an admissible factor-colour pair from
  the circuit and prove the two aligned normal-form hypotheses.  These
  arguments retain the
  returned section and old high representative; the section-only injectivity
  theorem remains false and must not be restored.
- Extract the two independent localized high colours from the circuit return.
  Once supplied, the actual unpopulated representative is now connected to
  the generic positive-quadratic-defect contradiction in
  `QuadraticReturnRankTwo.lean`.
- Prove the corresponding one-defect return statement (both the rational and
  degree-two capacity types) and the remaining two-defect stable-envelope
  suffix theorem.
- Instantiate `CostedTwoDefectQuadraticPrefixes` and
  `CostedFirstOrderQuadraticPrefixes`, then expose `no_twelve_gate_circuit`
  and `mc_mul_five` with no assumptions.

The fixed-state multiplication-map, bounded return-class, and SAT probes in
`n5/verification/exploration` are discovery checks only.  In particular,
`quadratic_return_class_sample.py` finds at least 64 unpopulated returned
classes in each tested factor-pair type, so the former four-fixed-section
orbit plan is false.  Its first 64 ordered samples missed a second exact
obstruction now recorded by `quadratic_return_kernel_counterexample.py`.
With

```
q = 0,  c = r0,
ell = a0 + a1 + b0,
x = a0 + b0,
y = a0 + b1,
m = a1 + a3 + a4 + b0 + b1 + b2 + b3,
```

the products with linear pairs `(ell,m)` and `(ell+x,m+y)` have the same
nonzero high part.  Their quadratic difference `z` has minimum alternating
rank four over every target translate, but
`(targetTwo E2 + z) wedge targetTwo r0 = 0`.  Thus even the parameterized
four-factor-pair exterior-kernel proposal is false.  Any valid closure must
retain more of the Boolean idempotence equations and circuit history, or
prove the weaker costed gain bound actually needed at the endpoint.
