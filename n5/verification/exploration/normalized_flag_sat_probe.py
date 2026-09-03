#!/usr/bin/env python3
"""Exact SAT probe in target/defect flag normal form.

For a nonredundant circuit computing an ``m``-dimensional target, each gate
raises either target rank or defect rank.  At a target gate, replace the new
wire-space generator by the target vector obtained from the product after an
old-wire correction.  Future factors can use that generator because XOR is
free.  Consequently an ``r``-gate minimum has exactly ``m`` symbolic target
generators and only ``r-m`` genuinely nonlinear defect generators.

This encoding is equisatisfiable with the nonredundant circuit problem, but it
is still only a falsification/search tool.  UNSAT is not promoted to a theorem
without a separately checkable certificate or algebraic proof.
"""

from __future__ import annotations

import argparse
import json
import time

import z3

from unrestricted_sat_probe import (
    _subsets_as_masks,
    multiplication_targets,
    symbolic_bool_xor,
    symbolic_xor_selection,
    truth_tables,
)


def parity(bits: list[z3.BoolRef]) -> z3.BoolRef:
    return symbolic_bool_xor(bits)


def encode(
    n: int,
    gate_count: int,
    timeout_ms: int,
    memory_mb: int,
    defect_positions: set[int] | None = None,
):
    variable_count = 2 * n
    width = 1 << variable_count
    target_count = 2 * n - 1
    defect_count = gate_count - target_count
    if defect_count < 0:
        raise ValueError("gate count is below the target dimension")

    variables = truth_tables(variable_count)
    one = (1 << width) - 1
    targets = multiplication_targets(n, variables)
    base = [z3.BitVecVal(one, width), *[
        z3.BitVecVal(value, width) for value in variables
    ]]
    target_bv = [z3.BitVecVal(value, width) for value in targets]

    solver = z3.SolverFor("QF_BV")
    solver.set(timeout=timeout_ms)
    solver.set(max_memory=memory_mb)

    wires = list(base)
    gate_is_target: list[z3.BoolRef] = []
    target_coefficients: list[list[z3.BoolRef]] = []
    left_selectors: list[list[z3.BoolRef]] = []
    right_selectors: list[list[z3.BoolRef]] = []
    correction_selectors: list[list[z3.BoolRef]] = []
    products: list[z3.BitVecRef] = []

    for gate_index in range(gate_count):
        old_wires = list(wires)
        is_target = z3.Bool(f"is_target_{gate_index}")
        coefficients = [
            z3.Bool(f"tc_{gate_index}_{coordinate}")
            for coordinate in range(target_count)
        ]
        left_bits = [
            z3.Bool(f"l_{gate_index}_{wire_index}")
            for wire_index in range(len(old_wires))
        ]
        right_bits = [
            z3.Bool(f"r_{gate_index}_{wire_index}")
            for wire_index in range(len(old_wires))
        ]
        correction_bits = [
            z3.Bool(f"c_{gate_index}_{wire_index}")
            for wire_index in range(len(old_wires))
        ]

        # Toggle either factor's explicit constant without changing the wire
        # extension: the difference is an old wire.
        solver.add(z3.Not(left_bits[0]), z3.Not(right_bits[0]))
        left = symbolic_xor_selection(left_bits, old_wires, width)
        right = symbolic_xor_selection(right_bits, old_wires, width)
        solver.add(z3.ULE(left, right))
        product = left & right

        target_function = symbolic_xor_selection(
            coefficients, target_bv, width
        )
        correction = symbolic_xor_selection(
            correction_bits, old_wires, width
        )
        solver.add(z3.Implies(is_target, product == target_function ^ correction))

        # Coefficients on defect rows are semantically unused; zeroing them
        # removes a large irrelevant Boolean cube.
        for coefficient in coefficients:
            solver.add(z3.Implies(z3.Not(is_target), z3.Not(coefficient)))

        wire = z3.If(is_target, target_function, product)
        wires.append(wire)
        gate_is_target.append(is_target)
        target_coefficients.append(coefficients)
        left_selectors.append(left_bits)
        right_selectors.append(right_bits)
        correction_selectors.append(correction_bits)
        products.append(product)

    solver.add(z3.PbEq([(flag, 1) for flag in gate_is_target], target_count))
    if defect_positions is not None:
        if len(defect_positions) != defect_count:
            raise ValueError("fixed defect-position count does not match r-target")
        for gate_index, flag in enumerate(gate_is_target):
            solver.add(flag == (gate_index not in defect_positions))

    # The selected target rows span F_2^m iff no nonzero dual vector is
    # orthogonal to all of them.  Since exactly m rows are selected, they then
    # form a basis and each target gate is nonredundant in the target flag.
    for dual_mask in range(1, 1 << target_count):
        detects_dual = []
        for gate_index in range(gate_count):
            dot = parity([
                target_coefficients[gate_index][coordinate]
                for coordinate in range(target_count)
                if (dual_mask >> coordinate) & 1
            ])
            detects_dual.append(z3.And(gate_is_target[gate_index], dot))
        solver.add(z3.Or(*detects_dual))

    return {
        "solver": solver,
        "gate_is_target": gate_is_target,
        "target_coefficients": target_coefficients,
        "left_selectors": left_selectors,
        "right_selectors": right_selectors,
        "correction_selectors": correction_selectors,
        "products": products,
        "concrete_base": [one, *variables],
        "targets": targets,
        "target_count": target_count,
        "defect_count": defect_count,
    }


def selected(model: z3.ModelRef, bits: list[z3.BoolRef]) -> list[int]:
    return [
        i for i, bit in enumerate(bits)
        if z3.is_true(model.eval(bit, model_completion=True))
    ]


def xor_selected(wires: list[int], indices: list[int]) -> int:
    result = 0
    for index in indices:
        result ^= wires[index]
    return result


def replay(encoded, model: z3.ModelRef) -> dict:
    wires = list(encoded["concrete_base"])
    target_rows = []
    gates = []

    for gate_index, flag in enumerate(encoded["gate_is_target"]):
        is_target = z3.is_true(model.eval(flag, model_completion=True))
        left_indices = selected(model, encoded["left_selectors"][gate_index])
        right_indices = selected(model, encoded["right_selectors"][gate_index])
        correction_indices = selected(
            model, encoded["correction_selectors"][gate_index]
        )
        left = xor_selected(wires, left_indices)
        right = xor_selected(wires, right_indices)
        product = left & right

        if is_target:
            row = selected(model, encoded["target_coefficients"][gate_index])
            target = 0
            row_mask = 0
            for coordinate in row:
                row_mask |= 1 << coordinate
                target ^= encoded["targets"][coordinate]
            correction = xor_selected(wires, correction_indices)
            if product != target ^ correction:
                raise AssertionError("target-gate equation failed replay")
            wires.append(target)
            target_rows.append(row_mask)
        else:
            wires.append(product)
            row_mask = 0

        gates.append({
            "kind": "target" if is_target else "defect",
            "target_row": row_mask,
            "left": left_indices,
            "right": right_indices,
            "correction": correction_indices if is_target else [],
        })

    # Independent integer rank check on target coefficient rows.
    pivots: dict[int, int] = {}
    for row in target_rows:
        value = row
        while value:
            pivot = value.bit_length() - 1
            if pivot in pivots:
                value ^= pivots[pivot]
            else:
                pivots[pivot] = value
                break
    if len(pivots) != encoded["target_count"]:
        raise AssertionError("target rows failed independent rank replay")

    return {"gates": gates, "target_rank": len(pivots), "replay": "passed"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("gates", type=int)
    parser.add_argument("--timeout-seconds", type=int, default=60)
    parser.add_argument("--memory-mb", type=int, default=1536)
    parser.add_argument("--model-json")
    parser.add_argument(
        "--defect-positions",
        help="comma-separated zero-based gate positions; fixes the flag chronology",
    )
    args = parser.parse_args()

    defect_positions = None
    if args.defect_positions is not None:
        defect_positions = {
            int(value) for value in args.defect_positions.split(",") if value != ""
        }

    started = time.monotonic()
    encoded = encode(
        args.n,
        args.gates,
        timeout_ms=1000 * args.timeout_seconds,
        memory_mb=args.memory_mb,
        defect_positions=defect_positions,
    )
    result = encoded["solver"].check()
    elapsed = time.monotonic() - started
    report = {
        "n": args.n,
        "gates": args.gates,
        "target_gates": encoded["target_count"],
        "defect_gates": encoded["defect_count"],
        "defect_positions": (
            sorted(defect_positions) if defect_positions is not None else None
        ),
        "result": str(result),
        "elapsed_seconds": round(elapsed, 3),
        "reason_unknown": (
            encoded["solver"].reason_unknown() if result == z3.unknown else None
        ),
    }
    print(json.dumps(report, sort_keys=True))
    if result == z3.sat:
        witness = replay(encoded, encoded["solver"].model())
        print(json.dumps(witness, sort_keys=True))
        if args.model_json:
            with open(args.model_json, "w", encoding="utf-8") as output:
                json.dump(witness, output, indent=2, sort_keys=True)
                output.write("\n")


if __name__ == "__main__":
    main()
