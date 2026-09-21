#!/usr/bin/env python3
"""Regression tests for binary-subspace canonical keys.

The exhaustive width-six triple test catches the historical bug: insertion
echelon rows were used as a set key after clearing only their pivot columns,
so one subspace could retain several keys.  The corrected high-pivot RREF,
independent low-pivot RREF, and point-set greedy key must each be constant on
every tested generating family.
"""

from __future__ import annotations

import itertools
import random
from collections import defaultdict


def insertion_basis(values: tuple[int, ...], width: int, high: bool = True) -> tuple[int, ...]:
    rows = [0] * width
    pivots = range(width - 1, -1, -1) if high else range(width)
    for value in values:
        for pivot in pivots:
            if not ((value >> pivot) & 1):
                continue
            if rows[pivot]:
                value ^= rows[pivot]
            else:
                rows[pivot] = value
                break
    order = range(width - 1, -1, -1) if high else range(width)
    return tuple(rows[pivot] for pivot in order if rows[pivot])


def high_rref(values: tuple[int, ...], width: int) -> tuple[int, ...]:
    rows = [0] * width
    for value in values:
        for pivot in range(width - 1, -1, -1):
            if not ((value >> pivot) & 1):
                continue
            if rows[pivot]:
                value ^= rows[pivot]
                continue
            for lower in range(pivot - 1, -1, -1):
                if rows[lower] and ((value >> lower) & 1):
                    value ^= rows[lower]
            rows[pivot] = value
            for other in range(width):
                if other != pivot and rows[other] and ((rows[other] >> pivot) & 1):
                    rows[other] ^= value
            break
    return tuple(rows[pivot] for pivot in range(width - 1, -1, -1) if rows[pivot])


def low_rref(values: tuple[int, ...], width: int) -> tuple[int, ...]:
    rows = [0] * width
    for value in values:
        for pivot in range(width):
            if not ((value >> pivot) & 1):
                continue
            if rows[pivot]:
                value ^= rows[pivot]
                continue
            for higher in range(pivot + 1, width):
                if rows[higher] and ((value >> higher) & 1):
                    value ^= rows[higher]
            rows[pivot] = value
            for other in range(width):
                if other != pivot and rows[other] and ((rows[other] >> pivot) & 1):
                    rows[other] ^= value
            break
    return tuple(rows[pivot] for pivot in range(width) if rows[pivot])


def old_noncanonical(values: tuple[int, ...], width: int) -> tuple[int, ...]:
    rows = [0] * width
    for value in values:
        for pivot in range(width - 1, -1, -1):
            if not ((value >> pivot) & 1):
                continue
            if rows[pivot]:
                value ^= rows[pivot]
            else:
                rows[pivot] = value
                for other in range(width):
                    if other != pivot and rows[other] and ((rows[other] >> pivot) & 1):
                        rows[other] ^= value
                break
    return tuple(rows[pivot] for pivot in range(width - 1, -1, -1) if rows[pivot])


def point_set(values: tuple[int, ...], width: int) -> tuple[int, ...]:
    basis = insertion_basis(values, width)
    points = [0]
    for row in basis:
        points += [point ^ row for point in points]
    return tuple(sorted(points))


def lexicographic_point_basis(values: tuple[int, ...], width: int) -> tuple[int, ...]:
    selected: list[int] = []
    for point in point_set(values, width):
        if len(insertion_basis((*selected, point), width)) > len(selected):
            selected.append(point)
    return tuple(selected)


def main() -> None:
    width = 6
    correct_keys: dict[tuple[int, ...], tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]] = {}
    old_keys: defaultdict[tuple[int, ...], set[tuple[int, ...]]] = defaultdict(set)
    triples = 0
    for values in itertools.product(range(1 << width), repeat=3):
        triples += 1
        points = point_set(values, width)
        keys = (
            high_rref(values, width),
            low_rref(values, width),
            lexicographic_point_basis(values, width),
        )
        assert all(point_set(key, width) == points for key in keys)
        if points in correct_keys:
            assert correct_keys[points] == keys
        else:
            correct_keys[points] = keys
        old_keys[points].add(old_noncanonical(values, width))

    duplicate_old_spaces = sum(len(keys) > 1 for keys in old_keys.values())
    assert duplicate_old_spaces > 0

    rng = random.Random(20260901)
    random_trials = 20_000
    for _ in range(random_trials):
        width = 55
        values = tuple(rng.getrandbits(width) for _ in range(rng.randrange(1, 7)))
        permuted = tuple(rng.sample(values, len(values)))
        assert high_rref(values, width) == high_rref(permuted, width)
        assert low_rref(values, width) == low_rref(permuted, width)
        assert point_set(high_rref(values, width), width) == point_set(
            low_rref(values, width), width
        )

    print("GF2_CANONICAL_KEY_PROPERTY_TEST_PASS")
    print(f"exhaustive_ordered_triples={triples} distinct_subspaces={len(correct_keys)}")
    print(f"old_noncanonical_duplicate_spaces={duplicate_old_spaces}")
    print(f"random_width55_trials={random_trials}")


if __name__ == "__main__":
    main()
