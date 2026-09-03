#!/usr/bin/env python3
"""Bounded falsification probe for unrestricted XOR--AND multiplication.

This is deliberately an exploration tool, not a proof premise.  It encodes an
arbitrary straight-line XOR--AND circuit using complete truth tables packed in
Z3 bit-vectors.  A SAT answer is independently replayed with Python integers
and is therefore a genuine counterexample/witness.  An UNSAT answer is useful
diagnostically, but is not accepted as a theorem without a checkable
certificate or a separate algebraic proof.

The Z3 package is kept outside the repository.  Point PYTHONPATH at the pinned
temporary installation when running this script.
"""

from __future__ import annotations

import argparse
import itertools
import json
import time
from dataclasses import dataclass

import z3


def truth_tables(variable_count: int) -> list[int]:
    """Truth tables with assignment ``a`` stored in bit ``a``."""
    width = 1 << variable_count
    return [
        sum(((assignment >> variable) & 1) << assignment
            for assignment in range(width))
        for variable in range(variable_count)
    ]


def multiplication_targets(n: int, variables: list[int]) -> list[int]:
    left = variables[:n]
    right = variables[n:]
    return [
        sum(0 for _ in ()) ^ _xor_all(
            left[i] & right[degree - i]
            for i in range(n)
            if 0 <= degree - i < n
        )
        for degree in range(2 * n - 1)
    ]


def _xor_all(values) -> int:
    result = 0
    for value in values:
        result ^= value
    return result


def symbolic_xor_selection(
    selectors: list[z3.BoolRef], wires: list[z3.BitVecRef], width: int
) -> z3.BitVecRef:
    zero = z3.BitVecVal(0, width)
    result = zero
    for selector, wire in zip(selectors, wires, strict=True):
        result = result ^ z3.If(selector, wire, zero)
    return result


def symbolic_bool_xor(values: list[z3.BoolRef]) -> z3.BoolRef:
    result = z3.BoolVal(False)
    for value in values:
        result = z3.Xor(result, value)
    return result


@dataclass
class EncodedCircuit:
    solver: z3.Solver
    left_selectors: list[list[z3.BoolRef]]
    right_selectors: list[list[z3.BoolRef]]
    output_selectors: list[list[z3.BoolRef]]
    gates: list[z3.BitVecRef]
    concrete_base: list[int]
    targets: list[int]
    width: int


def encode(
    n: int,
    gate_count: int,
    timeout_ms: int,
    memory_mb: int,
    concrete_base_override: list[int] | None = None,
    first_high_tail_target: bool = False,
) -> EncodedCircuit:
    variable_count = 2 * n
    width = 1 << variable_count
    variables = truth_tables(variable_count)
    all_ones = (1 << width) - 1
    concrete_base = concrete_base_override or [all_ones, *variables]
    target_values = multiplication_targets(n, variables)

    solver = z3.SolverFor("QF_BV")
    solver.set(timeout=timeout_ms)
    solver.set(max_memory=memory_mb)

    base = [z3.BitVecVal(value, width) for value in concrete_base]
    gates: list[z3.BitVecRef] = []
    left_selectors: list[list[z3.BoolRef]] = []
    right_selectors: list[list[z3.BoolRef]] = []

    for gate_index in range(gate_count):
        available = [*base, *gates]
        left_bits = [
            z3.Bool(f"l_{gate_index}_{wire_index}")
            for wire_index in range(len(available))
        ]
        right_bits = [
            z3.Bool(f"r_{gate_index}_{wire_index}")
            for wire_index in range(len(available))
        ]

        # Adding 1 to either factor changes the product only by an old wire.
        # Hence every circuit state has a representative with these bits zero.
        solver.add(z3.Not(left_bits[0]), z3.Not(right_bits[0]))

        left = symbolic_xor_selection(left_bits, available, width)
        right = symbolic_xor_selection(right_bits, available, width)
        gate = left & right

        # Multiplication is commutative.  This removes the factor-swap orbit.
        solver.add(z3.ULE(left, right))

        left_selectors.append(left_bits)
        right_selectors.append(right_bits)
        gates.append(gate)

        if first_high_tail_target:
            if gate_index == 0:
                high_coefficients = []
                for degree in (3, 4):
                    for support in itertools.combinations(range(variable_count), degree):
                        assignment_bits = [
                            z3.Extract(assignment, assignment, gate) == 1
                            for assignment in _subsets_as_masks(support)
                        ]
                        high_coefficients.append(symbolic_bool_xor(assignment_bits))
                solver.add(z3.Or(*high_coefficients))
            else:
                target_membership_wires = [
                    *available,
                    *[z3.BitVecVal(target, width) for target in target_values],
                ]
                membership_bits = [
                    z3.Bool(f"target_{gate_index}_{wire_index}")
                    for wire_index in range(len(target_membership_wires))
                ]
                solver.add(
                    gate
                    == symbolic_xor_selection(
                        membership_bits, target_membership_wires, width
                    )
                )

    final_wires = [*base, *gates]
    output_selectors: list[list[z3.BoolRef]] = []
    for output_index, target in enumerate(target_values):
        bits = [
            z3.Bool(f"o_{output_index}_{wire_index}")
            for wire_index in range(len(final_wires))
        ]
        output_selectors.append(bits)
        solver.add(
            symbolic_xor_selection(bits, final_wires, width)
            == z3.BitVecVal(target, width)
        )

    return EncodedCircuit(
        solver=solver,
        left_selectors=left_selectors,
        right_selectors=right_selectors,
        output_selectors=output_selectors,
        gates=gates,
        concrete_base=concrete_base,
        targets=target_values,
        width=width,
    )


def selected(model: z3.ModelRef, bits: list[z3.BoolRef]) -> list[int]:
    return [
        index
        for index, bit in enumerate(bits)
        if z3.is_true(model.eval(bit, model_completion=True))
    ]


def replay(encoded: EncodedCircuit, model: z3.ModelRef) -> dict:
    wires = list(encoded.concrete_base)
    gates = []
    gate_description = []

    for left_bits, right_bits in zip(
        encoded.left_selectors, encoded.right_selectors, strict=True
    ):
        left_indices = selected(model, left_bits)
        right_indices = selected(model, right_bits)
        left = _xor_all(wires[index] for index in left_indices)
        right = _xor_all(wires[index] for index in right_indices)
        gate = left & right
        gates.append(gate)
        wires.append(gate)
        gate_description.append({"left": left_indices, "right": right_indices})

    outputs = []
    output_description = []
    for bits in encoded.output_selectors:
        indices = selected(model, bits)
        outputs.append(_xor_all(wires[index] for index in indices))
        output_description.append(indices)

    if outputs != encoded.targets:
        raise AssertionError("Z3 model failed independent integer replay")

    return {
        "gates": gate_description,
        "outputs": output_description,
        "replay": "passed",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("gates", type=int)
    parser.add_argument("--timeout-seconds", type=int, default=60)
    parser.add_argument("--memory-mb", type=int, default=1536)
    parser.add_argument("--model-json")
    parser.add_argument(
        "--base",
        choices=("affine", "rational", "wstar", "wpq", "w3p", "wstar0"),
        default="affine",
    )
    parser.add_argument("--first-high-tail-target", action="store_true")
    args = parser.parse_args()

    started = time.monotonic()
    concrete_base = fixed_base(args.n, args.base)
    encoded = encode(
        args.n,
        args.gates,
        timeout_ms=1000 * args.timeout_seconds,
        memory_mb=args.memory_mb,
        concrete_base_override=concrete_base,
        first_high_tail_target=args.first_high_tail_target,
    )
    result = encoded.solver.check()
    elapsed = time.monotonic() - started
    print(json.dumps({
        "n": args.n,
        "gates": args.gates,
        "result": str(result),
        "base": args.base,
        "first_high_tail_target": args.first_high_tail_target,
        "elapsed_seconds": round(elapsed, 3),
        "reason_unknown": (
            encoded.solver.reason_unknown() if result == z3.unknown else None
        ),
    }, sort_keys=True))

    if result == z3.sat:
        witness = replay(encoded, encoded.solver.model())
        print(json.dumps(witness, sort_keys=True))
        if args.model_json:
            with open(args.model_json, "w", encoding="utf-8") as output:
                json.dump(witness, output, indent=2, sort_keys=True)
                output.write("\n")


def independent_basis_with_one(vectors: list[int]) -> list[int]:
    """Small high-pivot elimination, retaining a literal constant first."""
    chosen = [vectors[0]]
    pivots: dict[int, int] = {}

    def insert(value: int) -> bool:
        for pivot in sorted(pivots, reverse=True):
            if (value >> pivot) & 1:
                value ^= pivots[pivot]
        if not value:
            return False
        pivot = value.bit_length() - 1
        for old_pivot, row in list(pivots.items()):
            if (row >> pivot) & 1:
                pivots[old_pivot] = row ^ value
        pivots[pivot] = value
        return True

    insert(vectors[0])
    for value in vectors[1:]:
        if insert(value):
            chosen.append(value)
    return chosen


def _subsets_as_masks(support: tuple[int, ...]) -> list[int]:
    masks = [0]
    for variable in support:
        masks += [mask | (1 << variable) for mask in masks]
    return masks


def fixed_base(n: int, name: str) -> list[int] | None:
    if name == "affine":
        return None

    variables = truth_tables(2 * n)
    width = 1 << (2 * n)
    one = (1 << width) - 1
    left = variables[:n]
    right = variables[n:]
    targets = multiplication_targets(n, variables)
    r0 = targets[0]
    r1 = _xor_all(targets)
    rinf = targets[-1]

    if name == "rational":
        return independent_basis_with_one([one, *variables, r0, r1, rinf])
    if n != 5:
        raise ValueError(f"base {name!r} is defined only for n=5")

    if name in ("wstar", "wstar0"):
        a0 = left[0] ^ left[2] ^ left[3]
        a1 = left[1] ^ left[2] ^ left[4]
        b0 = right[0] ^ right[2] ^ right[3]
        b1 = right[1] ^ right[2] ^ right[4]
        quadratics = [a0 & b0, a0 & b1, a1 & b0, a1 & b1, r0, r1, rinf]
        if name == "wstar0":
            quadratics.append(targets[1])
    elif name == "wpq":
        quadratics = [
            r0,
            targets[1],
            left[1] & right[1],
            rinf,
            targets[7],
            left[3] & right[3],
            r1,
        ]
    elif name == "w3p":
        quadratics = [
            r0,
            targets[1],
            targets[2],
            left[1] & right[1],
            left[2] & right[2],
            r1,
            rinf,
        ]
    else:
        raise AssertionError(name)

    return independent_basis_with_one([one, *variables, *quadratics])


if __name__ == "__main__":
    main()
