#!/usr/bin/env python3
"""Dependency-free verification of the explicit rank-17 decomposition of P_6."""

from __future__ import annotations

import json
from pathlib import Path


N = 6
M = 2 * N - 1


def main() -> None:
    path = Path(__file__).with_name("n6_bilinear_rank17_solution.json")
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["rank"] == 17
    gates = data["gates"]
    outputs = data["outputs"]
    assert len(gates) == 17
    assert len(outputs) == M
    assert all(0 < a < (1 << N) and 0 < b < (1 << N) for a, b in gates)
    assert all(len(set(indices)) == len(indices) for indices in outputs)
    assert all(0 <= k < len(gates) for indices in outputs for k in indices)

    # For every output coefficient s and input monomial a_i b_j, verify that
    # the XOR of the selected rank-one terms is one exactly when i+j=s.
    for s, indices in enumerate(outputs):
        for i in range(N):
            for j in range(N):
                coefficient = 0
                for k in indices:
                    a, b = gates[k]
                    coefficient ^= ((a >> i) & 1) & ((b >> j) & 1)
                assert coefficient == int(i + j == s), (s, i, j, coefficient)

    print("N6_BILINEAR_RANK17_DECOMPOSITION_PASS")
    print("rank=17 tensor_entries_checked=396")


if __name__ == "__main__":
    main()
