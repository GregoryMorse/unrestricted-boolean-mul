# Lean formalization handoff for `MC(Mul 5) = 13`

## Objective

Prove in the existing unrestricted-circuit semantics:

```lean
theorem UnrestrictedBooleanMul.N5.mc_mul_five : MC (Mul 5) = 13
```

The informal proof has two logically different halves:

1. a quadratic capacity theorem based on decomposable two-forms, closed-place
   fibers, and an exact relation map; and
2. a suffix theorem showing that nonlinear reuse cannot recover the remaining
   target directions after the last all-quadratic state.

Keep those halves separate in Lean.  Their interface is the target/defect
ledger, not a shared case-analysis implementation.

## Existing reusable foundation

Use the following kernel-checked `n = 4` modules directly:

- `ANF.lean`, `Circuit.lean`, and `Mul.lean` for semantics;
- `N4/Degree.lean`, `N4/Homogeneous.lean`, and `N4/Exterior.lean` for
  homogeneous and wedge bookkeeping;
- `N4/TwoForm.lean` and `N4/Hankel.lean` for two-form coordinates;
- `N4/QuadraticCircuit.lean` and `N4/QuadraticProjection.lean` for the last
  quadratic prefix;
- `N4/BooleanIdentities.lean`, `N4/Rewiring.lean`, and the quartic/cubic
  modules for nonlinear gate normalization; and
- `N4/Feedback*.lean` and `N4/SecondFeedback*.lean` for idempotence and
  high-colour proof patterns.

Do not begin by refactoring the completed `N4` namespace.  Generalize a lemma
only when the `N5` proof needs the exact abstraction and the old theorem can be
reproved by a short wrapper.  This keeps the 24,885-line checked development
stable while the new proof grows.

## Recovered computational guide

The programs in `n5/verification/exploration/` preserve the coordinate engines
and finite scans used while discovering the `W_{PQ}`, `W_{3P}`, and
defect-at-most-one arguments.  They may be used to test Lean definitions or to
locate the intended pivots, but no printed table is an allowed theorem premise.
The directory README records which programs are exhaustive, accelerated,
sampled, or only syntax-replayed in this handoff.

## Dependency-ordered module plan

### Phase 0: target and upper circuit

- `N5/Target.lean` — private target projection, target independence, rank nine
  (checked).
- `N5/Statement.lean` — separated canonical proposition (checked).
- `N5/Upper.lean` — explicit thirteen-product bilinear circuit and
  `mul_five_upper : HasCircuit (Mul 5) 13` (checked).

The upper circuit is explicit ANF data rather than a literature axiom.  Its
nine recombination identities are written as a ring-normalization proof, and
`n5/verification/five_upper_formula_check.py` independently checks the same
25 bilinear monomial coefficients.

### Phase 1: quadratic quotient and relation map

- `N5/QuadraticSpace.lean` — the 45-dimensional squarefree quadratic
  coefficient space, the nine-dimensional Hankel target, quotient projection,
  and decomposability.
- `N5/Fiber.lean` — decomposable fibers, difference spaces, the zero-fiber
  theorem, and the target--defect exact sequence.
- `N5/RelationMap.lean` — relation kernel `K_X`, displacement map `lambda`, and
  the exact formula `rho(Q) = 3 + d + rank lambda`.

These three Phase 1 modules are checked. The exact theorem is first stated as
a submodule identity in the ambient quotient and only then converted to a
finrank formula.

Formalize the equality as a finite-dimensional submodule identity first; use
finrank only in the final corollary.  This avoids arithmetic obscuring the
linear map.

### Phase 2: closed-place classification

- `N5/ClosedPlaces.lean` — the three rational places, the degree-two place,
  their first jets, and coordinate symmetries.
- `N5/HankelSupport.lean` — rank-two Hankel support and the dimension-
  polymorphic secant-support lemma (checked).
- `N5/LocalKlein.lean` — the two local Klein-quadric calculations and counts
  `11,11,11,10` (checked).
- `N5/EffectiveFibers.lean` — the four local quotient charts, their exact
  Hermite rank certificate, and 43-point injective atlas (checked);
  localization exhaustiveness remains pending.
- `N5/MixedPlace.lean` — strong mixed-place exclusion.
- `N5/Displacement.lean` — the relation-gift rank bound.
- `N5/Capacity.lean` — `rho_2(5)=6`, `rho_3(5)=7`, their equality cases, and
  the quadratic lower bound thirteen.

The key completion gate for this phase is a theorem excluding a twelve-gate
all-quadratic circuit with no imported search result.

The checked Phase 2 prefix consists of the eight independent closed-place
directions, an algebraic five-minor/Boolean-ideal proof of rank-two Hankel
support, the secant-support theorem, the two symbolic local Klein equations
with counts `11,11,11,10`, and the injective 43-point Hermite atlas.  Its
localization exhaustiveness theorem and the remaining Phase 2 modules are
still pending.

### Phase 3: unrestricted prefix bookkeeping

- `N5/Prefix.lean` — choose the last all-quadratic circuit state, define its
  target rank and quotient defect, and prove the defect alternatives
  `e in {0,1,2,3}`.
- `N5/SuffixBudget.lean` — define `d_post` over every finite suffix constrained
  only by total defect at most three.  There is deliberately no gate-count
  parameter.

The monotonicity theorem must assume equal defect in the envelope transfer:

```text
W' <= W, e(W') = e(W) = 2
```

and prove monotonicity of the deficit after the `Delta = t(W)-t(W')`
correction.  Do not assert the false raw inequality `d_post(W') <= d_post(W)`.

### Phase 4: two-defect suffixes

- `N5/E2/Envelopes.lean` — exhaustive classification by the extremal envelope
  and `W_*`, `W_PQ`, `W_3P`; include the no-effective-fiber state explicitly
  and prove it is dominated by `W_3P`.
- `N5/E2/Extremal.lean` — the already-closed equality state, including the
  dependency of the exceptional annihilator branch on the hard `Q=0` branch.
- `N5/E2/WStar.lean`, `WPQ.lean`, and `W3P.lean` — stable total suffix bounds.
- `N5/E2/Main.lean` — combine the envelopes using suffix-deficit monotonicity.

Budgets are totals.  Every Lean statement should bound the span generated by
all gate types jointly; do not add separately proved per-source maxima unless
a non-addition theorem justifies the sum.

### Phase 5: defects zero and one

- `N5/FirstEnvelope.lean` — the codimension-one envelope
  `U = R + D_* + <j_0,j_1,j_infinity>`.
- `N5/MissingCoset.lean` — cross-rank-three missing-coset rigidity via the
  explicit pivot contradiction.
- `N5/TargetClean.lean` — the target-clean second-jet module and functional.
- `N5/ColourBirth.lean` — independent colours create a third high direction.
- `N5/ColourNormalization.lean` — rank-one colour normalization, including
  the equal nonzero colour case and Boolean idempotence identities.
- `N5/ThreeColour.lean` — saturation under `e + s <= 3` for every target
  subspace `J <= U`, so zero-high gates are included rather than imported from
  an older bounded-`J` theorem.

In the old-product-colour branch, record explicitly that three prior high
directions plus `e+s <= 3` forces `e=0`.

### Phase 6: final theorem

- `N5/Main.lean` — exclude twelve gates by the four defect regimes and combine
  with `mul_five_upper`.
- add `N5.Main` to `UnrestrictedBooleanMul.lean`;
- add `N5.no_twelve_gate_circuit` and `N5.mc_mul_five` to `AxiomAudit.lean`.

## Proof engineering rules

- Prefer finite coordinate linear maps and submodule equalities to large
  elementwise Boolean expansions.
- Keep all coordinate tables in named definitions and prove each table row by
  a small pivot/minor lemma.  A computed table may test a definition but may
  not enter a theorem as an assumed list.
- Separate symmetry reduction from the representative calculation.  Every
  orbit theorem needs an explicit action and invariance proof.
- Preserve the distinction between quadratic defect directions and high
  nonlinear colours in types or namespaces; many informal budget mistakes
  came from conflating them.
- Add theorem-level docstrings containing the manuscript label and equation
  number so statement-fidelity review is mechanical.
- Avoid `native_decide`.  If a bounded finite case is eventually discharged by
  `decide`, expose the proposition and verify that reduction remains kernel
  tractable; otherwise replace it by algebraic pivot lemmas.

## Completion gates

The formalization is complete only when all of the following hold:

1. `lake build` succeeds from a clean checkout.
2. `rg -n "sorry|admit|axiom|native_decide" UnrestrictedBooleanMul/N5` has no
   trust-affecting hit.
3. `lake env lean AxiomAudit.lean` reports only standard Mathlib foundations
   for `N5.mc_mul_five`.
4. the formal statement is independently compared with the manuscript's
   unrestricted XOR--AND model and nine output functions;
5. the final release records the Lean version, mathlib revision, full commit,
   checksums, and anonymous-checkout commands; and
6. the manuscript is updated from “formalization in progress” only after that
   release exists.

## Cost estimate

The current evidence still supports a broad estimate of 75,000--170,000 new
Lean lines.  The uncertainty is concentrated in the envelope classifications,
relation-map quotient infrastructure, and three-colour saturation, not in the
target coordinates or final arithmetic.  Formalization proceeds in parallel;
publication of the hand proof does not wait for this estimate to resolve.
