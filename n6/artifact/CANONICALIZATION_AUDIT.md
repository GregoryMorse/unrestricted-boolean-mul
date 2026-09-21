# Canonicalization audit for the exact rank of binary length-six multiplication

## Decision

The canonicalization bug does **not** invalidate the exhaustive lower bound for

\[
R_{\mathbf F_2}(P_6)=17.
\]

Every publication-critical enumeration has now been regenerated from rebuilt
source with assertions enabled and with a second canonical representation.
The fourteen output-concise hyperplane cases and both endpoint sectors agree
with their archived searches exactly, after suppressing only traversal-order
progress lines and the representation-dependent choice of a displayed basis.

The mathematical publication hold caused by the bug can therefore be lifted.
The artifact package itself should still be rebuilt before submission, because
the corrected sources and new audit logs have new checksums.

This audit does **not** advance the open endpoint non-addition lemma for the
general-\(n\) programme. It certifies the separate exhaustive proof of the
finite \(n=6\) rank statement.

## 1. The bug and the check that catches it

The faulty routine maintained an insertion-echelon basis and cleared a newly
chosen pivot from the old rows, but it installed the new row before reducing
that row against existing lower pivots. The returned rows spanned the correct
subspace, but the packed row list depended on the generating order. The same
subspace could therefore have several hash keys.

This failure mode normally causes duplicate states rather than omissions: a
valid spanning basis remains valid, and downstream capacity computations are
subspace-invariant. It can nevertheless corrupt exact counts, histograms,
beam tie-breaking, and any claim that a set contains one entry per subspace.

The permanent regression test `gf2_canonical_key_property_test.py` uses three
independent keys:

1. high-pivot reduced row echelon form;
2. low-pivot reduced row echelon form;
3. the lexicographically first greedy basis of the complete point set.

It exhausts all \(64^3=262{,}144\) ordered triples in \(\mathbf F_2^6\) and
runs 20,000 randomized tests in width 55. The corrected keys agree. The old
routine produces multiple keys on 2,046 of the 2,110 subspaces appearing in
the exhaustive triple test. Thus generator-permutation invariance, or a
bijection check against either independent key, would have caught the bug
immediately.

Future exhaustive programs should make this a build-time test and should log
the source hash, compiler flags, assertion status, and canonical-key mode.

## 2. Publication-critical \(n=6\) audit

### 2.1 Hyperplane orbits

The fifteen hyperplane orbits never used the faulty subspace key. The original
code generated literal sets of six-bit masks. A new verifier importing none of
that code independently reconstructs polynomial translation and reversal,
derives their dual actions by testing the coefficient pairing, and checks the
multiplication identities on all \(2^{12}=4096\) input pairs.

The result is:

- 63 nonzero constraints;
- 15 disjoint orbits;
- representatives
  \(1,2,4,5,6,9,10,11,18,19,27,30,31,35,39\);
- one orbit with output rank 10 and fourteen with output rank 11.

### 2.2 Fourteen output-concise cases

Each of the fourteen searches was rebuilt with assertions enabled and with the
point-set lexicographic key, not RREF. For every mask, the following data match
the archived run exactly:

- fibre and effective-fibre catalogues;
- number and profile of affine-plane anchors;
- number of candidate four-spaces;
- every pruning count;
- every upper-bound and exact-capacity histogram entry;
- the final maximum.

The maxima remain:

| masks | maximum capacity |
|:---|:---|
| \(2,4,5,6,9,10,11\) | \(10,8,9,10,8,7,9\) |
| \(18,19,27,30,31,35,39\) | \(10,9,10,8,7,9,9\) |

All are below the target dimension 11.

### 2.3 Endpoint local sector

The endpoint enumerator was rebuilt with the opposite, low-pivot RREF. The
following publication boundaries match exactly:

| quantity | independently regenerated value |
|:---|---:|
| affine-plane anchors | 1,367,651 |
| dense four-spaces | 22,009,456 |
| tight hidden three-spaces | 210 |
| hidden lines | 3,346,190 |
| dense exact evaluations | 1,386,179,181 |
| dense upper-bound prunes | 1,527,963,150 |
| generated five-spaces | 133,880,246 |
| distinct retained candidates | 1,301,345 |
| maximum capacity | 9 |

The complete plane profile, sparse-sector histogram, and every final count
also agree term for term.

### 2.4 Endpoint zero-local sector

The zero-local enumerator was likewise rebuilt with low-pivot RREF. It gives:

| quantity | independently regenerated value |
|:---|---:|
| affine-plane anchors | 1,310,312 |
| anchors evaluated | 1,250,825 |
| dense occurrences | 1,809,558,200 |
| maximum relation rank | 4 |
| capacity-ten witness | none |
| distinguished-block occurrences | 124,416 |
| support violations | 0 |

### 2.5 Upper bound

The explicit seventeen-term decomposition still passes the independent
entrywise verifier, which checks all 396 tensor coefficients.

Consequently the substitution proof remains valid: every first-input
hyperplane restriction has rank at least 16, so a decomposition of \(P_6\)
has at least 17 terms, while the displayed decomposition has 17 terms.

## 3. Reach of the faulty routine outside the paper proof

The source inventory found the incomplete-reduction pattern in four live
exploratory files:

- `n6_saturation_probe.cpp`;
- `verify_n6_saturation_witness.py`;
- `n6_symmetric_capacity.cpp`;
- `rect56_missing_functionals.py`.

They have been repaired. None is a premise of the exhaustive \(R(P_6)\)
lower bound.

The corrected saturation rerun proves that the old exploratory counts were
not all benign. Its one-replacement census changes as follows:

| quantity | old | corrected |
|:---|---:|---:|
| distinct states tested | 634,988 | 591,959 |
| rank-10 states | 8 | 1 |

The six-dimensional saturation witness, its 63 hyperplane capacities, the
full-neighbour scan of 85,771,843 cosets, and all final maxima are unchanged.
The corrected witness verifier regenerates byte-for-byte the same witness JSON.

The fixed-seed missing-functional sample also changes slightly in its sampled
counts, while retaining the structural observations used only for discovery:
25 rank-four cases, all with factor support \((4,4)\), and the same rank-three
projected maximum. Its old log must not be cited.

Among the live \(n=5\) sources in this branch, the coloured Pareto search and
the constrained-capacity implementation already perform complete reduction
before packing a key. More importantly, the \(n=5\) paper's final proof is
algebraic/formal rather than premised on these enumerations. Recovered
exploratory backups have not been promoted to certified artifacts.

## 4. Publication gate

The theorem is green; the package is yellow until rebuilt.

Before submission:

1. package the rebuilt sources rather than the pre-audit binaries;
2. include the fourteen lexicographic logs and two low-pivot endpoint logs;
3. include the independent orbit verifier and canonical-key property test;
4. include `audit_n6_canonicalization.py`, which compares the complete final
   boundaries and histograms;
5. replace the old checksum manifest with
   `n6_canonicalization_audit_SHA256SUMS.txt`;
6. label the corrected saturation and missing-functional outputs as
   exploratory, not premises of the rank theorem.

The endpoint non-addition problem for the general case remains exactly where
it was: the local normal form and rank-nine block are established, but the
minimal six-, seven-, and eight-dimensional coloured boundary configurations
still require quartic-recurrence compatibility. The present audit neither
weakens nor solves that lemma.
