# Verification artifact: exact bilinear rank of binary `P_6`

This artifact supports the theorem

```text
R_F2(P_6) = 17,
```

where `P_6` is full multiplication of two six-coefficient polynomials over
`F_2`.  The upper bound is an explicit 17-term decomposition.  The lower
bound is an exhaustive computational proof after an algebraic substitution
reduction.

The artifact intentionally contains only publication-critical sources,
complete archived logs, the explicit upper witness, and independent audit
checks.  Exploratory saturation, bounded-width, symmetric-capacity, SAT, and
missing-functional programs are not premises of the theorem and are excluded.

## Proof dependency map

| Paper component | Logically required files | Independent audit |
| --- | --- | --- |
| 15 first-input hyperplane orbits | `n6_constraint_orbits.py`, `verify_n6_orbits.py` | `n6_orbit_independent_audit.py`, `audit_canonicalization/n6_orbit_independent_audit.txt` |
| 14 eleven-output restrictions | `n6_constrained_capacity.cpp`, `n6_constraint_mask_*.txt` | `audit_canonicalization/n6_mask_*_lexaudit.txt`, `audit_n6_canonicalization.py` |
| Endpoint, nonzero local increment | `rect56_capacity_probe.cpp`, `rect56_capacity_effective_exact_results.txt` | `audit_canonicalization/rect56_capacity_lowaudit.txt`, `audit_n6_canonicalization.py` |
| Endpoint, zero-local relation sector | `rect56_zero_local_blocking.cpp`, `rect56_zero_local_relation_exact_results.txt` | `audit_canonicalization/rect56_zero_local_lowaudit.txt`, `audit_n6_canonicalization.py` |
| Rank-17 upper bound | `n6_bilinear_rank17_solution.json` | `verify_n6_bilinear_rank17.py` checks all 396 coefficients |
| Canonical-key regression | none; audit support only | `gf2_canonical_key_property_test.py` and archived output |

`CANONICALIZATION_AUDIT.md` records why the publication-critical searches are
unaffected by the insertion-order bug found in separate exploratory code.

## Toolchain

The archived runs used standalone C++20 and Python 3 programs.  A compatible
replay environment is:

- Python 3.10 or later;
- a C++20 compiler with `unsigned __int128` support;
- POSIX threads;
- GNU Make for the convenience targets below.

No third-party Python package or solver is required.  Assertions are enabled
in the independent rebuild commands; do not add `-DNDEBUG`.

## Quick verification

Run:

```sh
make quick
```

This performs the following dependency-light checks:

1. reconstructs all 15 orbits and verifies both tensor symmetries on all 4096
   input pairs;
2. reconstructs the orbit calculation a second way without importing the
   production orbit code;
3. verifies the explicit 17-term decomposition on all 396 tensor entries;
4. checks the publication boundary lines in all 16 archived exhaustive logs;
5. compares every concise search and both endpoint searches across independent
   canonical forms;
6. exhausts all 262,144 ordered triples in `F_2^6` to regression-test the
   canonical keys, followed by 20,000 randomized width-55 trials;
7. verifies `SHA256SUMS`.

Expected final markers are:

```text
N6_CONSTRAINT_ORBITS_AND_SYMMETRIES_PASS
N6_INDEPENDENT_ORBIT_AUDIT_PASS
N6_BILINEAR_RANK17_DECOMPOSITION_PASS
N6_EXHAUSTIVE_CAPACITY_LOGS_PASS
N6_CANONICALIZATION_CROSSCHECK_PASS
GF2_CANONICAL_KEY_PROPERTY_TEST_PASS
```

The quick checks verify the witness, orbit layer, archived boundaries, and
independent recanonicalization.  They do not replay the billion-occurrence
endpoint enumerations.

## Rebuild the enumerators

Run:

```sh
make build
```

This creates six executables under `build/`:

- production high-pivot and audit point-set versions of the concise search;
- production high-pivot and audit low-pivot versions of each endpoint search.

## Full exhaustive replay

The complete searches are long-running and should be launched explicitly.
The commands are:

```sh
make replay-concise-audit
make replay-endpoint-local-audit
make replay-endpoint-zero-audit
```

The first command runs all fourteen masks

```text
2 4 5 6 9 10 11 18 19 27 30 31 35 39
```

with the point-set canonical key.  The endpoint commands use low-pivot RREF,
opposite to the archived production implementation.  New logs are written to
`replay/`; existing archived logs are never overwritten.  After all commands
finish, compare each new log with its corresponding file under
`audit_canonicalization/`, ignoring only progress-line ordering and the
representation-dependent displayed best basis, as implemented by
`audit_n6_canonicalization.py`.

## Exact publication boundaries

The fourteen concise maxima, in representative order, are:

```text
masks: 2 4 5 6 9 10 11 18 19 27 30 31 35 39
rho:  10 8 9 10 8  7  9 10  9 10  8  7  9  9
```

The endpoint local-sector maximum is capacity 9.  The endpoint zero-local
maximum relation rank is 4.  Hence every first-input hyperplane restriction
has tensor rank at least 16.  Substitution gives `R_F2(P_6) >= 17`, and the
explicit witness gives equality.

## Certification status

This is an exhaustive computational proof with independent canonicalization,
not a proof-assistant formalization or a succinct negative certificate.  The
rank-17 upper witness is directly checkable.  The lower-bound searches can be
replayed from source, and the complete archived boundaries are cross-checked
under independent canonical forms.

## License

The source and verification material are released under the MIT License; see
`LICENSE`.
