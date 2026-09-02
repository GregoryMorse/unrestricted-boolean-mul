# Recovered `n = 5` exploration programs

These programs are the computational scratchwork that led to the algebraic
envelope and suffix arguments in the manuscript.  They are preserved as a
research record and as implementation guidance for the Lean formalization.
They are **not proof premises** and their printed summaries must not be cited
as substitutes for the manuscript's lemmas.

Run commands from the repository root.  All scripts are deterministic except
`e1_nested_probe.py`, which uses a fixed seed and is a diagnostic sampler.

| Program | Role in discovery | Dependencies | Replay status |
| --- | --- | --- | --- |
| `w_pq_analysis.py` | Coordinate engine and scans for the `W_{PQ}` envelope: dependent and quartic cases, target matching, and zero-high tests. | Python standard library | Syntax checked; long full scan not part of handoff audit. |
| `w_3p_analysis.py` | `W_{3P}` wedge kernel, dependent/quartic scans, and independent matching. | `w_pq_analysis.py` | Syntax checked; long full scan not part of handoff audit. |
| `w3_quartic_numpy.py` | NumPy-accelerated quartic matching scan for `W_{3P}`. | NumPy, the two `W` modules | Syntax checked; long full scan not part of handoff audit. |
| `e1_pstar_analysis.py` | The `P_*`/Karatsuba-plane coordinate model, target-line extensions, annihilator scans, and matching profiles used in the defect-at-most-one work. | `w_pq_analysis.py` | Syntax checked; long full scan not part of handoff audit. |
| `e1_extended_high.py` | Checks the seven hard quotient planes against dependent, quartic, and zero-high behavior. | `e1_pstar_analysis.py`, `w_pq_analysis.py` | Syntax checked; long full scan not part of handoff audit. |
| `e1_g_reuse.py` | Searches possible reuse of a selected high gate and nested high seeds. | `e1_pstar_analysis.py`, `w_pq_analysis.py` | Syntax checked; long full scan not part of handoff audit. |
| `e1_independent_numpy.py` | NumPy-accelerated independent/dependent shadow-overlap and affine-span profiles. | NumPy, `e1_pstar_analysis.py`, `w_pq_analysis.py` | Syntax checked; long full scan not part of handoff audit. |
| `e1_nested_probe.py` | Fixed-seed sampling of nested high gates; useful for finding dangerous forms, not an exhaustive test. | the `e1` modules | Syntax checked; diagnostic only. |
| `local_pstar_orbits.py` | Local Klein-quadric fiber sizes, stabilizer, and orbit transitivity for the degree-two place. | Python standard library | Fully replayed; transcript recorded. |
| `first_order_cubic_rigidity_probe.py` | Lightweight discovery audit for the cubic-syzygy rank of all projective planes in the exact first-order envelope basis.  It detects the rational-direction family and the unique non-rational degree-two translate, preventing an over-broad rigidity statement. | `w_pq_analysis.py` | Quick deterministic scan; regression/discovery only. |

The syntax check used for this snapshot is:

```bash
python3 -m py_compile n5/verification/exploration/*.py
```

The quick deterministic orbit replay is:

```bash
python3 n5/verification/exploration/local_pstar_orbits.py \
  > /tmp/local_pstar_orbits_actual.txt
diff -u \
  n5/verification/exploration/local_pstar_orbits_results.txt \
  /tmp/local_pstar_orbits_actual.txt
```

The audit environment used Python 3.12.13 and NumPy 2.3.5.  The programs use
plain integer bitsets and are intentionally kept close to the forms used during
discovery rather than refactored into a shared production library.

The historical 166,199,235-presentation projection program and the original
43-fiber census source are not present.  Their former outputs are not premises
of the paper.
