Four-term binary polynomial multiplication: verification artifact

Paper
-----

The manuscript is distributed separately.  In the arXiv source package this
directory appears as anc/verification/; in the public reusable artifact it
appears as n4/verification/.  Section 10, "Verification status", identifies the
checks below.  They are regression checks around the handwritten proof; no
program output is a premise of Theorem 9.1.

Toolchain used for the audited 2026-08-29 run
---------------------------------------------

- Python 3.12.13; standard library only.
- g++ 13.3.0 with C++17.
- Linux x86-64.  No network access, solver, dataset, or third-party package is
  required by the checks.

File-to-claim map
-----------------

- n4_annihilator_rank_verifier.py
  Checks the seven-column target-annihilator ranks for rational-place weights.
  Expected stdout: n4_annihilator_rank_results.txt.
- n4_quartic_seed_exclusion_verifier.py
  Checks the rank-at-most-two target taxonomy, quartic-support separation, and
  the two quartic g-using slice orbits.
  Expected stdout: n4_quartic_seed_exclusion_results.txt.
- n4_feedback_quadratic_repair.py
  Checks the quadratic and linear three-slice equations (6)--(7).
  Expected stdout: n4_feedback_quadratic_repair_results.txt.
- n4_first_low_low_normal_form_verifier.py
  Checks the low--low first-feedback normal form and first-Hasse-jet target.
  Expected stdout: n4_first_low_low_normal_form_results.txt.
- n4_first_jet_js_repair.py
  Checks the first-jet skip obstruction and corrected jet-separation
  coefficients.
  Expected stdout: n4_first_jet_js_repair_results.txt.
- n4_second_suffix_saturation_verifier.py
  Checks the E2 annihilator, zero-wedge structure in the seed span, and
  second-jet injectivity.
  Expected stdout: n4_second_suffix_saturation_results.txt.
- n4_first_child_scan.cpp
  Exhaustively scans the 57,906 canonical seed-orbit representatives at seed
  position 4.  The audited full run found exactly 14 representatives with a
  useful first child and maximum child count one.
  Reference consolidated record: n4_first_child_scan_results.txt.  That file
  preserves six historical chunk transcripts and elapsed times, so a one-shot
  replay is compared by invariant records and counts rather than byte-for-byte.
- n4_first_child_ann_check.py
  Independently parses n4_first_child_scan_results.txt and checks that the 14
  reported high parts all have target-annihilator dimension three.
  Expected stdout: n4_first_child_ann_check_results.txt.
- n4_14seed_second_child_check.cpp
  Replays the 14 completion-capable canonical seeds and checks that they have
  one first useful child and zero second useful children.
  Expected stdout: n4_14seed_second_child_results.txt.

Reproduction commands
---------------------

Run from this directory.  A silent diff means byte-for-byte agreement.

  python3 n4_annihilator_rank_verifier.py > /tmp/n4_annihilator_rank.txt
  diff -u n4_annihilator_rank_results.txt /tmp/n4_annihilator_rank.txt

  python3 n4_quartic_seed_exclusion_verifier.py > /tmp/n4_quartic_seed.txt
  diff -u n4_quartic_seed_exclusion_results.txt /tmp/n4_quartic_seed.txt

  python3 n4_feedback_quadratic_repair.py > /tmp/n4_feedback.txt
  diff -u n4_feedback_quadratic_repair_results.txt /tmp/n4_feedback.txt

  python3 n4_first_low_low_normal_form_verifier.py > /tmp/n4_first_low_low.txt
  diff -u n4_first_low_low_normal_form_results.txt /tmp/n4_first_low_low.txt

  python3 n4_first_jet_js_repair.py > /tmp/n4_first_jet.txt
  diff -u n4_first_jet_js_repair_results.txt /tmp/n4_first_jet.txt

  python3 n4_second_suffix_saturation_verifier.py > /tmp/n4_second_suffix.txt
  diff -u n4_second_suffix_saturation_results.txt /tmp/n4_second_suffix.txt

  g++ -std=c++17 -O3 -Wall -Wextra -pedantic n4_first_child_scan.cpp -o /tmp/n4_first_child_scan
  /tmp/n4_first_child_scan 4 > /tmp/n4_first_child_summary.txt 2> /tmp/n4_first_child_records.txt
  grep '^HIGH_CHILD' n4_first_child_scan_results.txt | sort -u > /tmp/n4_first_child_expected.txt
  grep '^HIGH_CHILD' /tmp/n4_first_child_records.txt | sort -u > /tmp/n4_first_child_actual.txt
  diff -u /tmp/n4_first_child_expected.txt /tmp/n4_first_child_actual.txt
  grep -E '^IMMEDIATE seedpos=4 orbit_reps=57906 range=\[0,57906\) withchild=14 maxch=1 ' /tmp/n4_first_child_summary.txt

  python3 n4_first_child_ann_check.py > /tmp/n4_first_child_ann.txt
  diff -u n4_first_child_ann_check_results.txt /tmp/n4_first_child_ann.txt

  g++ -std=c++17 -O3 -Wall -Wextra -pedantic n4_14seed_second_child_check.cpp -o /tmp/n4_14seed_second_child_check
  /tmp/n4_14seed_second_child_check > /tmp/n4_14seed_second_child.txt
  diff -u n4_14seed_second_child_results.txt /tmp/n4_14seed_second_child.txt

The full first-child scan is the longest check and its elapsed-time field is
machine-dependent.  The other checks are short deterministic replays.
Temporary filenames above are deliberately outside the artifact directory so
reproduction does not modify the snapshot.

Public pin
----------

Intended repository:
https://github.com/GregoryMorse/unrestricted-boolean-mul

Repository subdirectory: n4/verification/

Intended release tag: n4-arxiv-v1

The verification software is released under the MIT License; this directory
includes a copy in LICENSE, and the repository root carries the same license.
The public repository, tag, and full commit hash are pending.  This artifact
must not be represented as publicly pinned until all three exist and the URL
resolves without authentication.
