"""Independent scalar replay of the fixed bilinear n6 upper-bound witness.

This does not generalize or alter the n5 unrestricted-circuit checker.
It accepts only the handoff's explicit 17-term, six-by-six bilinear format.
"""
from __future__ import annotations

import json
from pathlib import Path


WITNESS = Path(__file__).resolve().parent / "artifact/n6_bilinear_rank17_solution.json"


def validate(data: dict) -> None:
    if not isinstance(data, dict) or type(data.get("rank")) is not int or data["rank"] != 17:
        raise ValueError("expected the rank-17 bilinear witness format")
    gates, outputs = data.get("gates"), data.get("outputs")
    if not isinstance(gates, list) or len(gates) != 17:
        raise ValueError("exactly seventeen explicit gates required")
    for pair in gates:
        if not isinstance(pair, list) or len(pair) != 2:
            raise ValueError("a gate has exactly two input selectors")
        if any(type(mask) is not int or not 0 < mask < 64 for mask in pair):
            raise ValueError("selectors must be nonzero six-bit integers")
    if not isinstance(outputs, list) or len(outputs) != 11:
        raise ValueError("eleven output coefficient lists required")
    for indices in outputs:
        if not isinstance(indices, list) or any(type(k) is not int or not 0 <= k < 17 for k in indices):
            raise ValueError("invalid output selector")
        if len(set(indices)) != len(indices):
            raise ValueError("duplicate gate in output list")


def polynomial_product(left: int, right: int) -> int:
    result = 0
    for i in range(6):
        if left & (1 << i):
            result ^= right << i
    return result


def evaluate(gates: list, outputs: list, left: int, right: int) -> int:
    wires = [((a & left).bit_count() % 2) * ((b & right).bit_count() % 2)
             for a, b in gates]
    return sum((sum(wires[k] for k in indices) % 2) << s
               for s, indices in enumerate(outputs))


def verify(data: dict) -> dict:
    validate(data)
    gates, outputs = data["gates"], data["outputs"]
    for left in range(64):
        for right in range(64):
            if evaluate(gates, outputs, left, right) != polynomial_product(left, right):
                raise ValueError(f"incorrect polynomial product at {left}, {right}")

    # a_0=0 means a=x*A with five coefficients in A. Remove the zero gate,
    # rewrite all surviving selectors, and remove the zero output coefficient.
    retained = [k for k, (a, _) in enumerate(gates) if a >> 1]
    if len(retained) != 16:
        raise ValueError("the supplied endpoint restriction should have sixteen gates")
    index = {k: j for j, k in enumerate(retained)}
    rectangular_gates = [[gates[k][0] >> 1, gates[k][1]] for k in retained]
    rectangular_outputs = [[index[k] for k in indices if k in index]
                           for indices in outputs[1:]]
    for left in range(32):
        for right in range(64):
            if evaluate(rectangular_gates, rectangular_outputs, left, right) != polynomial_product(left, right):
                raise ValueError("incorrect rewritten five-by-six upper circuit")
    return {"square_gates": 17, "square_inputs": 4096,
            "rectangular_gates": 16, "rectangular_inputs": 2048}


if __name__ == "__main__":
    result = verify(json.loads(WITNESS.read_text(encoding="utf-8")))
    print("N6_SCALAR_UPPER_REPLAY_PASS")
    print(json.dumps(result, sort_keys=True))
