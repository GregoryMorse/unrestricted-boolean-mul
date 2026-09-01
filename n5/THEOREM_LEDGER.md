# Manuscript-to-Lean theorem ledger (`n = 5`)

Status meanings:

- **checked** — implemented and included in a clean kernel build;
- **replay pending** — implemented, but not yet accepted by a clean kernel
  build under the pinned toolchain;
- **interface fixed** — statement and dependencies are fixed, proof absent;
- **in progress** — kernel-checked supporting declarations exist, but the
  named manuscript theorem is not yet complete;
- **planned** — module and proof route identified;
- **regression only** — computational checksum, never a theorem premise.

| Manuscript result | Planned Lean declaration/module | Dependencies | Status |
|---|---|---|---|
| Nine target coordinates are independent | `N5.mulFive_linearIndependent`, `N5/Target.lean` | generic ANF coefficient projection | checked |
| Every circuit for `Mul 5` has at least nine ANDs | `N5.mul_five_dimension_lower`, `N5/Target.lean` | preceding row, generic circuit projection bound | checked |
| Explicit thirteen-product upper circuit | `N5.mul_five_upper`, `N5/Upper.lean` | thirteen affine products and nine ring identities | checked |
| Main statement `MC(Mul_5)=13` | `N5.MainStatement`, `N5/Statement.lean` | existing `MC`, `Mul` definitions | checked (statement only) |
| Lemma 2.1, zero fiber | `N5.zeroFiber_eq_rational`, `N5/Fiber.lean` | quadratic quotient, Hankel rank one | checked |
| Lemma 2.2, target--defect exact sequence | `N5.targetDefect_exact`, `N5/Fiber.lean` | finite submodule quotient | checked |
| Theorem 3.2, exact relation-map formula | `N5.relationMap_finrank`, `N5/RelationMap.lean` | relation kernel and displacement map | checked |
| Lemma 4.1, rank-two Hankel support | `N5.rankTwoHankel_support`, `N5/HankelSupport.lean` | Hankel coordinates and Boolean ideal certificate | checked |
| Lemma 4.2, secant support | `N5.secant_support`, `N5/HankelSupport.lean` | dimension-polymorphic contraction support | checked |
| Lemma 5.2, local Klein counts | `N5.localKlein_counts`, `N5/LocalKlein.lean` | two symbolic local Klein equations | checked |
| Theorem 5.3, 43 fibers | `N5.effectiveFibers_eq`, `N5.effectiveFibers_card`, `N5/EffectiveClassification.lean` | algebraic rank-two secants, localization, and local Klein counts | checked |
| Theorem 6.1, mixed-place exclusion | `N5.strongMixedPlace`, `N5/MixedPlaceDegreeInfinity.lean` | closed-place support | checked |
| Theorem 6.2, displacement bound | `N5.displacement_rank_le`, `N5/DisplacementBound.lean` | exact represented-place profile, algebraic Fano generators, symmetry-complete four-pivot secant spaces, and pointed codimension-one incidence | checked |
| Theorem 7.1, `rho_2(5)=6` | `N5.targetCapacity_le_six_of_finrank_le_two`, `N5.exists_finrank_le_two_targetCapacity_eq_six`, `N5/DefectTwoCapacity.lean` | algebraic defect-line relation bound and explicit rational-plus-degree-two witness; the separate equality-case classification is not yet formalized | checked |
| Theorem 7.2, `rho_3(5)=7` | `N5.targetCapacity_rank_three_exact`, `N5/DefectThreeWitness.lean` | universal displacement upper bound and explicit two-rational-plus-degree-two equality witness | checked |
| Proposition 8.1, capacity obstruction | `N5.capacity_obstruction`, `N5/Capacity.lean` | target--defect exact sequence and geometric capacity span | checked |
| Lemma 9.1, circuit bookkeeping | `N5.circuit_bookkeeping`, `N5/Prefix.lean` | generic circuit flags | planned |
| Proposition 10.2, two-defect envelopes | `N5.E2.envelopes_exhaustive`, `N5/E2/Envelopes.lean` | equality classification and symmetries | interface fixed |
| Theorem 10.4, stable two-defect bound | `N5.E2.suffix_target_le`, `N5/E2/Main.lean` | four envelope modules | planned |
| Lemma 10.6, suffix-deficit monotonicity | `N5.suffixDeficit_mono`, `N5/SuffixBudget.lean` | equal defect two, no length allowance | interface fixed |
| Lemma 11.1, missing-coset rigidity | `N5.missingCoset_crossRank`, `N5/MissingCoset.lean` | explicit pivot minors | planned |
| Lemma 11.2, envelope kernel and shadows | `N5.envelope_shadow`, `N5/FirstEnvelope.lean` | local radical structure | planned |
| Lemma 11.4, target-clean second jet | `N5.targetClean`, `N5/TargetClean.lean` | symbolic 4-by-4 contradiction | planned |
| Lemma 12.1, independent colours create a third | `N5.independentColours_birth`, `N5/ColourBirth.lean` | degree-six and degree-five slices | planned |
| Lemma 12.2, rank-one normalization | `N5.rankOneColour_normalize`, `N5/ColourNormalization.lean` | rewiring and idempotence | planned |
| Theorem 12.3, three-colour saturation | `N5.threeColour_saturation`, `N5/ThreeColour.lean` | `e+s<=3`, first-order envelope | interface fixed |
| Theorem 13.2, no twelve-gate circuit | `N5.no_twelve_gate_circuit`, `N5/Main.lean` | capacity and suffix regimes | planned |
| Theorem 13.2, exact value 13 | `N5.mc_mul_five`, `N5/Main.lean` | lower theorem and explicit upper circuit | planned |
| Proposition 13.1 upper-circuit expansion | `n5/verification/five_upper_formula_check.py` | displayed thirteen products | regression only; Lean checked independently |
| 15,728,640-presentation `W_*` check | `n5/verification/` | standalone C++20 | regression only |
| 166,199,235 projection run and 43-fiber scan | not yet released | discovery programs and exact inputs | regression only; absent artifact must not be claimed |

The paper's theorem numbering may move under later edits.  Lean docstrings
should therefore record both the descriptive result name and the manuscript
label current at implementation time.
