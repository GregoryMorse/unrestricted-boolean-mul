#!/usr/bin/env python3
"""Verify that every exhaustive n=6 capacity run is present and closed."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent
EXPECTED = {
    2: 10,
    4: 8,
    5: 9,
    6: 10,
    9: 8,
    10: 7,
    11: 9,
    18: 10,
    19: 9,
    27: 10,
    30: 8,
    31: 7,
    35: 9,
    39: 9,
}


def main() -> None:
    for mask, expected_best in EXPECTED.items():
        text = (ROOT / f"n6_constraint_mask_{mask}.txt").read_text(encoding="utf-8")
        assert f"mask={mask} " in text
        assert "q4_candidates=" in text
        assert "generated_q4=" in text
        assert "exact_evaluated=" in text
        matches = re.findall(r"\bbest=(\d+)", text)
        assert matches and int(matches[-1]) == expected_best, (mask, matches[-1:])
        assert expected_best < 11

    effective = (ROOT / "rect56_capacity_effective_exact_results.txt").read_text(
        encoding="utf-8"
    )
    assert "exact dense_q4=22009456" in effective
    assert "exact dense_evaluated=1386179181" in effective
    assert "exact generated_q5=133880246" in effective
    assert re.search(r"rho_hist .* best=9 best_basis=", effective)

    zero_local = (ROOT / "rect56_zero_local_relation_exact_results.txt").read_text(
        encoding="utf-8"
    )
    assert "planes=1310312" in zero_local
    assert "completed=1250825" in zero_local
    assert "best_relation=4" in zero_local
    assert "dense_occurrences=1809558200" in zero_local

    print("N6_EXHAUSTIVE_CAPACITY_LOGS_PASS")
    print("concise_orbits=14 endpoint_sectors=2")


if __name__ == "__main__":
    main()
