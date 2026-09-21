#!/usr/bin/env python3
"""Compare publication-critical n=6 searches across canonical forms."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent
MASKS = (2, 4, 5, 6, 9, 10, 11, 18, 19, 27, 30, 31, 35, 39)


def normalized_concise(path: Path) -> list[str]:
    answer = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("q3_progress="):
            continue
        line = re.sub(r" best_basis=.*$", " best_basis=<representation-dependent>", line)
        answer.append(line)
    return answer


def normalized_endpoint(path: Path) -> list[str]:
    answer = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("exact q3_progress=") or line.startswith("exact q4_progress="):
            continue
        line = re.sub(r" best_basis=.*$", " best_basis=<representation-dependent>", line)
        answer.append(line)
    return answer


def key_values(line: str) -> dict[str, int]:
    return {name: int(value) for name, value in re.findall(r"([a-z_]+)=(\d+)", line)}


def main() -> None:
    for mask in MASKS:
        archived = normalized_concise(ROOT / f"n6_constraint_mask_{mask}.txt")
        audited = normalized_concise(
            ROOT / "audit_canonicalization" / f"n6_mask_{mask}_lexaudit.txt"
        )
        assert audited == archived, (mask, archived, audited)
        assert int(re.search(r"\bbest=(\d+)", audited[-1]).group(1)) < 11

    endpoint_audit = ROOT / "audit_canonicalization" / "rect56_capacity_lowaudit.txt"
    if endpoint_audit.exists():
        assert normalized_endpoint(endpoint_audit) == normalized_endpoint(
            ROOT / "rect56_capacity_effective_exact_results.txt"
        )

    zero_audit = ROOT / "audit_canonicalization" / "rect56_zero_local_lowaudit.txt"
    if zero_audit.exists():
        archived_lines = (
            ROOT / "rect56_zero_local_relation_exact_results.txt"
        ).read_text(encoding="utf-8").splitlines()
        audited_lines = zero_audit.read_text(encoding="utf-8").splitlines()
        assert archived_lines[0] == audited_lines[0]
        archived = key_values(archived_lines[-1])
        audited = key_values(audited_lines[-1])
        for key in (
            "completed",
            "best",
            "best_relation",
            "dense_occurrences",
            "found_twelve",
        ):
            assert audited[key] == archived[key], (key, archived[key], audited[key])

    print("N6_CANONICALIZATION_CROSSCHECK_PASS")
    print("concise_orbits=14 canonical_key=lexicographic_point_set")
    print(
        "endpoint_local="
        + ("pass" if endpoint_audit.exists() else "pending")
        + " endpoint_zero_local="
        + ("pass" if zero_audit.exists() else "pending")
    )


if __name__ == "__main__":
    main()
