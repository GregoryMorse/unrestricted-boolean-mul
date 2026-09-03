#!/usr/bin/env python3
"""Exact bounded circuit probe using CryptoMiniSat's native XOR clauses.

This is a falsification tool, not a proof premise.  It uses the target/defect
flag normal form from ``normalized_flag_sat_probe.py`` but expands circuit
evaluation one Boolean assignment at a time.  Native XOR clauses express all
free linear recombinations; ordinary Tseitin clauses express the selected-wire
and AND-gate products.

The defect chronology is fixed on each invocation.  A SAT model is replayed
independently with Python integers before it is reported.  An UNSAT answer is
diagnostic until accompanied by a separately checked certificate or an
algebraic proof.
"""

from __future__ import annotations

import argparse
import json
import time

import pycryptosat


def truth_tables(variable_count: int) -> list[int]:
    """Truth tables with assignment ``a`` stored in bit ``a``."""
    width = 1 << variable_count
    return [
        sum(
            ((assignment >> variable) & 1) << assignment
            for assignment in range(width)
        )
        for variable in range(variable_count)
    ]


def multiplication_targets(n: int, variables: list[int]) -> list[int]:
    left = variables[:n]
    right = variables[n:]
    targets: list[int] = []
    for degree in range(2 * n - 1):
        value = 0
        for i in range(n):
            j = degree - i
            if 0 <= j < n:
                value ^= left[i] & right[j]
        targets.append(value)
    return targets


def canonical_basis(vectors: list[int]) -> dict[int, int]:
    basis: dict[int, int] = {}
    for original in vectors:
        value = original
        for pivot in sorted(basis, reverse=True):
            if (value >> pivot) & 1:
                value ^= basis[pivot]
        if not value:
            continue
        pivot = value.bit_length() - 1
        for old_pivot, row in list(basis.items()):
            if (row >> pivot) & 1:
                basis[old_pivot] = row ^ value
        basis[pivot] = value
    return dict(sorted(basis.items(), reverse=True))


def independent_basis_with_one(vectors: list[int]) -> list[int]:
    chosen: list[int] = []
    span: dict[int, int] = {}
    for value in vectors:
        if len(canonical_basis([*span.values(), value])) != len(span):
            chosen.append(value)
            span = canonical_basis([*span.values(), value])
    return chosen


def reduce_vector(value: int, basis: dict[int, int]) -> int:
    for pivot in sorted(basis, reverse=True):
        if (value >> pivot) & 1:
            value ^= basis[pivot]
    return value


def target_rows_in_basis(basis: list[int], targets: list[int]) -> list[int]:
    span = canonical_basis(basis)
    rows = [
        mask
        for mask in range(1, 1 << len(targets))
        if reduce_vector(
            xor_selected(targets, [
                i for i in range(len(targets)) if (mask >> i) & 1
            ]),
            span,
        ) == 0
    ]
    return list(canonical_basis(rows).values())


def xor_selected(values: list[int], indices: list[int]) -> int:
    result = 0
    for index in indices:
        result ^= values[index]
    return result


def concrete_base(n: int, name: str) -> tuple[list[int], list[int]]:
    inputs = truth_tables(2 * n)
    width = 1 << (2 * n)
    one = (1 << width) - 1
    targets = multiplication_targets(n, inputs)
    if name == "affine":
        basis = [one, *inputs]
        return basis, []
    if n != 5:
        raise ValueError("non-affine fixed bases are defined only for n=5")

    a = inputs[:5]
    b = inputs[5:]
    r0, r1, rinf = targets[0], xor_selected(targets, list(range(9))), targets[8]
    u = a[0] ^ a[2] ^ a[3]
    v = a[1] ^ a[2] ^ a[4]
    U = b[0] ^ b[2] ^ b[3]
    V = b[1] ^ b[2] ^ b[4]
    x00, x01, x10, x11 = u & U, u & V, v & U, v & V
    xsum = x00 ^ x01 ^ x10 ^ x11

    if name == "pstar":
        quadratics = [x00, x11, xsum, r0, r1, rinf]
    elif name == "e1r0":
        quadratics = [r0, targets[1], a[1] & b[1], r1, rinf]
    elif name == "qreturnce":
        # Exact unpopulated quadratic-return witness discovered by
        # quadratic_return_population_probe.py.  Both products have the same
        # nonzero high part; together they add one high and one quadratic
        # defect direction above Aff + <r0,r1,rinf>.
        first = (a[2] ^ b[2]) & (a[2] ^ r0)
        second = (a[2] ^ b[2] ^ b[0]) & (a[2] ^ a[0] ^ r0)
        quadratics = [r0, r1, rinf, first, second]
    elif name in ("wstar", "wstar0"):
        quadratics = [x00, x01, x10, x11, r0, r1, rinf]
        if name == "wstar0":
            quadratics.append(targets[1])
    elif name == "wpq":
        quadratics = [
            r0,
            targets[1],
            a[1] & b[1],
            rinf,
            targets[7],
            a[3] & b[3],
            r1,
        ]
    elif name == "w3p":
        quadratics = [
            r0,
            targets[1],
            targets[2],
            a[1] & b[1],
            a[2] & b[2],
            r1,
            rinf,
        ]
    else:
        raise ValueError(f"unknown fixed base {name!r}")
    basis = independent_basis_with_one([one, *inputs, *quadratics])
    return basis, target_rows_in_basis(basis, targets)


class Encoding:
    def __init__(
        self,
        n: int,
        gates: int,
        defect_positions: set[int],
        timeout_seconds: float,
        base_name: str,
        fixed_target_rows: list[int] | None,
        high_defect_positions: set[int],
    ) -> None:
        self.n = n
        self.gates = gates
        self.defect_positions = defect_positions
        self.width = 1 << (2 * n)
        self.target_count = 2 * n - 1
        self.solver = pycryptosat.Solver(
            threads=1, time_limit=timeout_seconds
        )
        self.next_variable = 1
        self.clauses = 0
        self.xors = 0

        self.inputs = truth_tables(2 * n)
        self.targets = multiplication_targets(n, self.inputs)
        base_with_one, self.base_target_rows = concrete_base(n, base_name)
        if base_with_one[0] != (1 << self.width) - 1:
            raise AssertionError("fixed basis must retain the constant first")
        self.concrete_basis = base_with_one[1:]
        target_span = canonical_basis(self.base_target_rows)
        self.missing_target_rows: list[int] = []
        for coordinate in range(self.target_count):
            row = 1 << coordinate
            if reduce_vector(row, target_span):
                self.missing_target_rows.append(row)
                target_span = canonical_basis([*target_span.values(), row])
        if len(target_span) != self.target_count:
            raise AssertionError("failed to complement the fixed target base")
        self.missing_targets = [
            xor_selected(self.targets, [
                coordinate
                for coordinate in range(self.target_count)
                if (row >> coordinate) & 1
            ])
            for row in self.missing_target_rows
        ]
        self.fixed_target_rows = fixed_target_rows
        self.high_defect_positions = high_defect_positions

        self.left_selectors: list[list[int]] = []
        self.right_selectors: list[list[int]] = []
        self.correction_selectors: list[list[int]] = []
        self.target_coefficients: list[list[int] | None] = []
        self.basis_values: list[list[int]] = []

    def var(self) -> int:
        result = self.next_variable
        self.next_variable += 1
        return result

    def add_clause(self, literals: list[int]) -> None:
        self.solver.add_clause(literals)
        self.clauses += 1

    def add_xor(self, variables: list[int], rhs: bool = False) -> None:
        # CryptoMiniSat accepts positive variable identifiers here.  Repeated
        # variables cancel, so normalize them before calling the binding.
        parity: dict[int, bool] = {}
        for variable in variables:
            parity[variable] = not parity.get(variable, False)
        normalized = [variable for variable, odd in parity.items() if odd]
        if normalized:
            self.solver.add_xor_clause(normalized, rhs)
            self.xors += 1
        elif rhs:
            self.add_clause([])

    def and_var(self, left: int, right: int) -> int:
        result = self.var()
        # result <-> left & right
        self.add_clause([-result, left])
        self.add_clause([-result, right])
        self.add_clause([result, -left, -right])
        return result

    def add_binary_le(self, left: list[int], right: list[int]) -> None:
        """Constrain the little-endian selector word ``left <= right``.

        Swapping the two factors does not change an AND gate.  The prefix
        variables record equality of all more-significant coordinates.
        """
        if len(left) != len(right):
            raise ValueError("binary comparator widths differ")
        prefix_equal: int | None = None
        for left_bit, right_bit in zip(reversed(left), reversed(right), strict=True):
            if prefix_equal is None:
                self.add_clause([-left_bit, right_bit])
            else:
                self.add_clause([-prefix_equal, -left_bit, right_bit])

            equal_here = self.var()
            # equal_here <-> (left_bit <-> right_bit)
            self.add_clause([-equal_here, -left_bit, right_bit])
            self.add_clause([-equal_here, left_bit, -right_bit])
            self.add_clause([equal_here, left_bit, right_bit])
            self.add_clause([equal_here, -left_bit, -right_bit])
            if prefix_equal is None:
                prefix_equal = equal_here
            else:
                next_prefix = self.and_var(prefix_equal, equal_here)
                prefix_equal = next_prefix

    def selected_value(
        self,
        selectors: list[int],
        assignment: int,
        old_gate_values: list[list[int]],
    ) -> list[int]:
        terms: list[int] = []
        # The explicit constant selector is normalized to zero and therefore
        # omitted.  Initial fixed-base coordinates are concrete.
        for coordinate, table in enumerate(self.concrete_basis):
            if (table >> assignment) & 1:
                terms.append(selectors[coordinate])
        for selector, values in zip(
            selectors[len(self.concrete_basis) :], old_gate_values, strict=True
        ):
            terms.append(self.and_var(selector, values[assignment]))
        return terms

    def build(self) -> None:
        base_target_rank = len(self.base_target_rows)
        quotient_dimension = len(self.missing_target_rows)
        target_gate_count = self.gates - len(self.defect_positions)
        if target_gate_count > quotient_dimension:
            raise ValueError("target-gate count exceeds the missing target dimension")

        target_gate_indices: list[int] = []
        target_gate_ordinal = 0
        for gate_index in range(self.gates):
            old_gate_values = list(self.basis_values)
            wire_count = len(self.concrete_basis) + gate_index
            left_selectors = [self.var() for _ in range(wire_count)]
            right_selectors = [self.var() for _ in range(wire_count)]
            self.add_binary_le(left_selectors, right_selectors)
            is_target = gate_index not in self.defect_positions

            coefficients = (
                [self.var() for _ in range(quotient_dimension)]
                if is_target
                else None
            )
            if coefficients is not None and self.fixed_target_rows is not None:
                if len(self.fixed_target_rows) != target_gate_count:
                    raise ValueError("fixed target-row count does not match target gates")
                row = self.fixed_target_rows[target_gate_ordinal]
                if row < 0 or row >= 1 << quotient_dimension:
                    raise ValueError("fixed target row is outside quotient coordinates")
                if row:
                    for coordinate, variable in enumerate(coefficients):
                        self.add_clause([
                            variable if (row >> coordinate) & 1 else -variable
                        ])
            correction_selectors = (
                [self.var() for _ in range(wire_count)] if is_target else []
            )

            target_values: list[int] = []
            product_values: list[int] = []
            for assignment in range(self.width):
                left_value = self.var()
                right_value = self.var()
                self.add_xor(
                    [left_value, *self.selected_value(
                        left_selectors, assignment, old_gate_values
                    )]
                )
                self.add_xor(
                    [right_value, *self.selected_value(
                        right_selectors, assignment, old_gate_values
                    )]
                )
                product = self.and_var(left_value, right_value)
                product_values.append(product)

                if is_target:
                    assert coefficients is not None
                    target_value = self.var()
                    target_terms = [
                        coefficients[coordinate]
                        for coordinate, table in enumerate(self.missing_targets)
                        if (table >> assignment) & 1
                    ]
                    self.add_xor([target_value, *target_terms])
                    correction_terms = self.selected_value(
                        correction_selectors, assignment, old_gate_values
                    )
                    self.add_xor([product, target_value, *correction_terms])
                    target_values.append(target_value)

            if gate_index in self.high_defect_positions:
                if is_target:
                    raise ValueError("a forced-high position must be a defect gate")
                high_coefficients: list[int] = []
                for monomial in range(self.width):
                    if monomial.bit_count() < 3:
                        continue
                    coefficient = self.var()
                    subassignments: list[int] = []
                    assignment = monomial
                    while True:
                        subassignments.append(product_values[assignment])
                        if assignment == 0:
                            break
                        assignment = (assignment - 1) & monomial
                    self.add_xor([coefficient, *subassignments])
                    high_coefficients.append(coefficient)
                self.add_clause(high_coefficients)

            self.left_selectors.append(left_selectors)
            self.right_selectors.append(right_selectors)
            self.correction_selectors.append(correction_selectors)
            self.target_coefficients.append(coefficients)
            self.basis_values.append(
                target_values if is_target else product_values
            )
            if is_target:
                target_gate_indices.append(gate_index)
                target_gate_ordinal += 1

        # The target coefficients are taken only in a fixed complement to the
        # initial target space: components in the initial target space can be
        # moved into the old-wire correction.  Demand that the new rows are
        # independent.  This also supports partial-gain probes, where fewer
        # target gates than missing target coordinates are requested.
        for row_mask in range(1, 1 << target_gate_count):
            nonzero_coordinates: list[int] = []
            for coordinate in range(quotient_dimension):
                value = self.var()
                terms = []
                for ordinal, gate_index in enumerate(target_gate_indices):
                    if (row_mask >> ordinal) & 1:
                        coefficients = self.target_coefficients[gate_index]
                        assert coefficients is not None
                        terms.append(coefficients[coordinate])
                self.add_xor([value, *terms])
                nonzero_coordinates.append(value)
            self.add_clause(nonzero_coordinates)

    @staticmethod
    def selected(model: tuple[bool | None, ...], variables: list[int]) -> list[int]:
        return [index for index, variable in enumerate(variables) if model[variable]]

    @staticmethod
    def xor_selected(values: list[int], indices: list[int]) -> int:
        result = 0
        for index in indices:
            result ^= values[index]
        return result

    def quotient_rows(self, model: tuple[bool | None, ...]) -> list[int]:
        rows: list[int] = []
        for coefficients in self.target_coefficients:
            if coefficients is None:
                continue
            rows.append(sum(
                1 << coordinate
                for coordinate, variable in enumerate(coefficients)
                if model[variable]
            ))
        return rows

    @staticmethod
    def canonical_flag(rows: list[int]) -> tuple[int, ...]:
        """Canonical ordered flag under additions of preceding rows."""
        canonical: list[int] = []
        preceding = [0]
        for row in rows:
            representative = min(row ^ value for value in preceding)
            canonical.append(representative)
            preceding += [value ^ representative for value in preceding]
        return tuple(canonical)

    def block_flag(self, flag: tuple[int, ...]) -> None:
        """Block every lower-unitriangular basis of one ordered flag."""
        target_rows = [
            coefficients for coefficients in self.target_coefficients
            if coefficients is not None
        ]
        if len(flag) != len(target_rows):
            raise ValueError("flag length does not match target-gate count")

        variants: list[tuple[int, ...]] = [()]
        preceding = [0]
        for row in flag:
            choices = [row ^ value for value in preceding]
            variants = [prefix + (choice,) for prefix in variants for choice in choices]
            preceding += [value ^ row for value in preceding]

        for matrix in variants:
            differs: list[int] = []
            for row, variables in zip(matrix, target_rows, strict=True):
                for coordinate, variable in enumerate(variables):
                    differs.append(
                        -variable if (row >> coordinate) & 1 else variable
                    )
            self.add_clause(differs)

    def replay(self, model: tuple[bool | None, ...]) -> dict[str, object]:
        # Selectors omit the constant coordinate.  Concrete normalized basis
        # starts with the ten input variables only.
        basis = list(self.concrete_basis)
        target_rows: list[int] = list(self.base_target_rows)
        trace: list[dict[str, object]] = []

        for gate_index in range(self.gates):
            left_indices = self.selected(model, self.left_selectors[gate_index])
            right_indices = self.selected(model, self.right_selectors[gate_index])
            left = self.xor_selected(basis, left_indices)
            right = self.xor_selected(basis, right_indices)
            product = left & right
            coefficients = self.target_coefficients[gate_index]

            if coefficients is None:
                basis.append(product)
                trace.append({
                    "kind": "defect",
                    "left": left_indices,
                    "right": right_indices,
                })
                continue

            coefficient_indices = self.selected(model, coefficients)
            quotient_row = sum(1 << index for index in coefficient_indices)
            target = self.xor_selected(self.missing_targets, coefficient_indices)
            correction_indices = self.selected(
                model, self.correction_selectors[gate_index]
            )
            correction = self.xor_selected(basis, correction_indices)
            if product != target ^ correction:
                raise AssertionError(f"target equation failed at gate {gate_index}")
            row = self.xor_selected(self.missing_target_rows, coefficient_indices)
            target_rows.append(row)
            basis.append(target)
            trace.append({
                "kind": "target",
                "quotient_row": quotient_row,
                "target_row": row,
                "left": left_indices,
                "right": right_indices,
                "correction": correction_indices,
            })

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
        expected_rank = len(self.base_target_rows) + (
            self.gates - len(self.defect_positions)
        )
        if len(pivots) != expected_rank:
            raise AssertionError("target coefficient rows are dependent")
        return {"replay": "passed", "target_rank": len(pivots), "gates": trace}


def parse_positions(text: str) -> set[int]:
    return {int(value) for value in text.split(",") if value}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("gates", type=int)
    parser.add_argument("--defect-positions", required=True)
    parser.add_argument("--timeout-seconds", type=float, default=60.0)
    parser.add_argument("--model-json")
    parser.add_argument(
        "--high-defect-positions",
        default="",
        help="comma-separated defect positions required to have ANF degree at least three",
    )
    parser.add_argument(
        "--enumerate-flags",
        action="store_true",
        help="enumerate reachable ordered target flags, quotienting row additions",
    )
    parser.add_argument(
        "--base",
        choices=("affine", "pstar", "e1r0", "qreturnce", "wstar", "wpq", "w3p", "wstar0"),
        default="affine",
    )
    parser.add_argument(
        "--target-rows",
        help="comma-separated quotient-coordinate row masks in target-gate order",
    )
    args = parser.parse_args()

    positions = parse_positions(args.defect_positions)
    high_defect_positions = parse_positions(args.high_defect_positions)
    if not high_defect_positions <= positions:
        raise ValueError("forced-high positions must be defect positions")
    fixed_target_rows = (
        [int(value, 0) for value in args.target_rows.split(",")]
        if args.target_rows
        else None
    )
    started = time.monotonic()
    encoding = Encoding(
        args.n,
        args.gates,
        positions,
        args.timeout_seconds,
        args.base,
        fixed_target_rows,
        high_defect_positions,
    )
    encoding.build()
    built = time.monotonic()
    result, model = encoding.solver.solve()
    finished = time.monotonic()

    report = {
        "n": args.n,
        "gates": args.gates,
        "defect_positions": sorted(positions),
        "base": args.base,
        "base_dimension": len(encoding.concrete_basis) + 1,
        "base_target_rank": len(encoding.base_target_rows),
        "target_rows": fixed_target_rows,
        "variables": encoding.next_variable - 1,
        "clauses": encoding.clauses,
        "xor_clauses": encoding.xors,
        "result": result,
        "build_seconds": round(built - started, 3),
        "solve_seconds": round(finished - built, 3),
    }
    print(json.dumps(report, sort_keys=True), flush=True)
    if args.enumerate_flags:
        flags: list[tuple[int, ...]] = []
        while result is True:
            assert model is not None
            flag = encoding.canonical_flag(encoding.quotient_rows(model))
            if flag in flags:
                raise AssertionError("flag blocker admitted a duplicate")
            flags.append(flag)
            print(json.dumps({
                "flag": flag,
                "witness": encoding.replay(model),
            }, sort_keys=True), flush=True)
            encoding.block_flag(flag)
            result, model = encoding.solver.solve()
        print(json.dumps({
            "enumeration_result": result,
            "flags": flags,
            "reachable_flag_count": len(flags),
        }, sort_keys=True), flush=True)
        return
    if result is True:
        assert model is not None
        witness = encoding.replay(model)
        print(json.dumps(witness, sort_keys=True), flush=True)
        if args.model_json:
            with open(args.model_json, "w", encoding="utf-8") as output:
                json.dump(witness, output, indent=2, sort_keys=True)
                output.write("\n")


if __name__ == "__main__":
    main()
