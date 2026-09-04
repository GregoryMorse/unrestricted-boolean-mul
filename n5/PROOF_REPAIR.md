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
   Consequently every remaining normalized rank-one escape is forced into
   one asymmetric case: the correction uses the returned section while the
   quadratic factor stays in the old first-order envelope.

These modules are checked only by the pinned Linux CI.  The focused replay
bridge, including the rank-one asymmetric reduction, compiles with pinned
Lean 4.32.1.  Windows Lean is not used for this repair.  A complete repository
build and `leanchecker` replay are reserved for a stable closure checkpoint.

## Remaining closure obligations

The paper cannot be unblocked until all of the following are proved and then
connected to the exact-cost circuit suffix.

- Split returned sections into populated and unpopulated quotient cases and
  account for the populated case without granting an uncharged target row.
- In the unpopulated case, close the remaining asymmetric rank-one branch:
  the old correction uses the returned section while the quadratic factor
  stays in the first-order envelope.
- Close the independent/rank-two high-colour branch after a return.
- Prove the corresponding one-defect return statement (both the rational and
  degree-two capacity types) and the remaining two-defect stable-envelope
  suffix theorem.
- Instantiate `CostedTwoDefectQuadraticPrefixes` and
  `CostedFirstOrderQuadraticPrefixes`, then expose `no_twelve_gate_circuit`
  and `mc_mul_five` with no assumptions.

The fixed-state multiplication-map and SAT probes in
`n5/verification/exploration` are discovery checks only.  Their negative
answers guide the algebraic normal forms but are not premises of the proof.
