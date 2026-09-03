#!/usr/bin/env python3
"""Scan every ordered target flag for one fixed-block suffix.

The underlying CryptoMiniSat encoding is the exact truth-table model from
``cryptominisat_flag_probe.py``.  A target generator may be changed by any
linear combination of earlier target generators without changing the wire
state, so one lower-unitriangular canonical basis represents each ordered
target flag.  This script enumerates those representatives and checks them
as assumptions against one shared solver, retaining learned clauses between
flags.

This remains a theorem-discovery/falsification tool.  A SAT model is replayed
independently and is a genuine witness.  An exhaustive UNSAT scan is useful
evidence for the fixed block, but is not imported by Lean and is not by itself
the final proof.
"""

from __future__ import annotations

import argparse
import itertools
import json
import time

from cryptominisat_flag_probe import Encoding, parse_positions


def canonical_complete_flags(dimension: int) -> list[tuple[int, ...]]:
    """One lower-unitriangular representative of every complete flag."""
    flags: set[tuple[int, ...]] = set()
    rows = range(1, 1 << dimension)
    for candidate in itertools.permutations(rows, dimension):
        span = [0]
        canonical: list[int] = []
        for row in candidate:
            representative = min(row ^ old for old in span)
            if representative == 0:
                break
            canonical.append(representative)
            span += [old ^ representative for old in span]
        else:
            flags.add(tuple(canonical))
    return sorted(flags)


def canonical_extensions(
    dimension: int, prefixes: list[tuple[int, ...]]
) -> list[tuple[int, ...]]:
    """Canonical one-row extensions of independent ordered prefixes."""
    result: set[tuple[int, ...]] = set()
    for prefix in prefixes:
        span = [0]
        for row in prefix:
            representative = min(row ^ old for old in span)
            if representative == 0:
                raise ValueError(f"dependent prefix {prefix}")
            if representative != row:
                raise ValueError(f"noncanonical prefix {prefix}")
            span += [old ^ row for old in span]
        representatives = {
            min(row ^ old for old in span)
            for row in range(1, 1 << dimension)
            if row not in span
        }
        result.update(prefix + (row,) for row in representatives)
    return sorted(result)


def row_assumptions(encoding: Encoding, rows: tuple[int, ...]) -> list[int]:
    target_variables = [
        coefficients
        for coefficients in encoding.target_coefficients
        if coefficients is not None
    ]
    if len(rows) != len(target_variables):
        raise ValueError("flag length does not match target-gate count")
    assumptions: list[int] = []
    for row, variables in zip(rows, target_variables, strict=True):
        for coordinate, variable in enumerate(variables):
            assumptions.append(variable if (row >> coordinate) & 1 else -variable)
    return assumptions


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", required=True,
        choices=("rational", "pstar", "e1r0", "qreturnce", "qreturn01",
                 "qreturn11", "qreturn12", "qreturn13", "wstar", "wpq",
                 "w3p", "wstar0", "qreturnpstar", "qreturne1r0"))
    parser.add_argument("--gates", type=int, required=True)
    parser.add_argument("--defect-positions", required=True)
    parser.add_argument("--high-defect-positions", default="")
    parser.add_argument("--flag-timeout-seconds", type=float, default=30.0)
    parser.add_argument(
        "--prefix",
        action="append",
        default=[],
        help="canonical comma-separated target flag to extend by one row",
    )
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int)
    parser.add_argument("--continue-after-sat", action="store_true")
    args = parser.parse_args()

    defect_positions = parse_positions(args.defect_positions)
    high_positions = parse_positions(args.high_defect_positions)
    started = time.monotonic()
    encoding = Encoding(
        5,
        args.gates,
        defect_positions,
        24 * 60 * 60,
        args.base,
        None,
        high_positions,
        set(),
    )
    encoding.build()
    built = time.monotonic()

    target_gate_count = args.gates - len(defect_positions)
    quotient_dimension = len(encoding.missing_target_rows)
    prefixes = [
        tuple(int(value, 0) for value in text.split(",") if value)
        for text in args.prefix
    ]
    if prefixes:
        if any(len(prefix) + 1 != target_gate_count for prefix in prefixes):
            raise ValueError("each prefix must be one row shorter than the target gate count")
        flags = canonical_extensions(quotient_dimension, prefixes)
    else:
        if target_gate_count != quotient_dimension:
            raise ValueError(
                "a partial scan requires --prefix; otherwise all missing targets are required"
            )
        flags = canonical_complete_flags(quotient_dimension)
    stop = len(flags) if args.stop is None else min(args.stop, len(flags))
    print(json.dumps({
        "base": args.base,
        "build_seconds": round(built - started, 3),
        "defect_positions": sorted(defect_positions),
        "flags": len(flags),
        "high_defect_positions": sorted(high_positions),
        "range": [args.start, stop],
        "variables": encoding.next_variable - 1,
    }, sort_keys=True), flush=True)

    unsat = 0
    unknown: list[int] = []
    sat: list[tuple[int, tuple[int, ...]]] = []
    for index in range(args.start, stop):
        flag = flags[index]
        solve_started = time.monotonic()
        result, model = encoding.solver.solve(
            assumptions=row_assumptions(encoding, flag),
            time_limit=args.flag_timeout_seconds,
        )
        elapsed = time.monotonic() - solve_started
        if result is True:
            assert model is not None
            sat.append((index, flag))
            print(json.dumps({
                "elapsed_seconds": round(elapsed, 3),
                "flag": flag,
                "index": index,
                "result": "sat",
                "witness": encoding.replay(model),
            }, sort_keys=True), flush=True)
            if not args.continue_after_sat:
                return
            continue
        if result is False:
            unsat += 1
        else:
            unknown.append(index)
        if (index - args.start + 1) % 10 == 0 or result is None:
            print(json.dumps({
                "checked": index - args.start + 1,
                "elapsed_seconds": round(time.monotonic() - built, 3),
                "last_flag": flag,
                "last_flag_seconds": round(elapsed, 3),
                "unknown": len(unknown),
                "unsat": unsat,
            }, sort_keys=True), flush=True)

    print(json.dumps({
        "checked": stop - args.start,
        "result": (
            "sat_found" if sat else ("unsat" if not unknown else "incomplete")
        ),
        "sat_flags": sat,
        "unknown_indices": unknown,
        "unsat": unsat,
    }, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
