#!/usr/bin/env python3
"""Test decomposable representability of same-plane quadratic returns.

For a fixed pair ``q,c`` in the zero-defect rational quadratic base, two
products

    (ell + q)(m + c),  (ell + x + q)(m + y + c)

have equal high part exactly when the cubic part of ``q*y + x*c`` vanishes.
Their difference is then quadratic.  This program enumerates that cubic
kernel algebraically and tests every resulting quadratic quotient class for
a decomposable representative modulo the Hankel target.

The scan is exact for the same quadratic plane.  It is a discovery tool, not
a proof premise; cross-plane collisions require a separate classification.
"""

from __future__ import annotations

import argparse
import itertools
import json

from w_pq_analysis import (
    A,
    B,
    COMBS,
    T,
    anf_degree_part,
    anf_multiply,
    basis,
    decomposable_2,
    form_to_anf,
    iterbits,
    nullspace_columns,
    r0,
    r1,
    rinf,
    span_vector,
)


RATIONAL_BASIS = [r0, r1, rinf]
LINEAR_BASIS = [*A, *B]


def permute_three_mask(mask: int, permutation: tuple[int, ...]) -> int:
    result = 0
    for source, target in enumerate(permutation):
        if (mask >> source) & 1:
            result |= 1 << target
    return result


def plane_orbit_key(q_mask: int, c_mask: int) -> tuple[int, int]:
    """Canonical unordered pair under the rational-place S3 action."""
    representatives = []
    for permutation in itertools.permutations(range(3)):
        q_image = permute_three_mask(q_mask, permutation)
        c_image = permute_three_mask(c_mask, permutation)
        representatives.append(tuple(sorted((q_image, c_image))))
    return min(representatives)


def reducer(generators: list[int]):
    pivots: dict[int, int] = {}
    for value in generators:
        for pivot in sorted(pivots, reverse=True):
            if (value >> pivot) & 1:
                value ^= pivots[pivot]
        if not value:
            continue
        pivot = value.bit_length() - 1
        for old_pivot, row in list(pivots.items()):
            if (row >> pivot) & 1:
                pivots[old_pivot] = row ^ value
        pivots[pivot] = value

    def reduce(value: int) -> int:
        for pivot in sorted(pivots, reverse=True):
            if (value >> pivot) & 1:
                value ^= pivots[pivot]
        return value

    return reduce


REDUCE_TARGET = reducer(T)


def twoform_rank(form: int) -> int:
    rows = [0] * 10
    for index in iterbits(form):
        support = COMBS[2][index]
        left = (support & -support).bit_length() - 1
        right = (support ^ (1 << left)).bit_length() - 1
        rows[left] ^= 1 << right
        rows[right] ^= 1 << left
    return len(basis(rows))


def minimum_target_coset_rank(form: int) -> int:
    return min(
        twoform_rank(form ^ span_vector(T, coefficients))
        for coefficients in range(1 << len(T))
    )


def populated_quotient_classes() -> set[int]:
    result: set[int] = set()
    for left in range(1 << 10):
        for right in range(left, 1 << 10):
            result.add(REDUCE_TARGET(decomposable_2(left, right)))
    return result


def cubic_part(poly: int) -> int:
    return anf_degree_part(poly, 3)


def quadratic_return(q: int, c: int, x: int, y: int) -> int:
    """Quadratic part of q*y + x*c + x*y."""
    q_anf = form_to_anf(q, 2)
    c_anf = form_to_anf(c, 2)
    x_anf = form_to_anf(x, 1)
    y_anf = form_to_anf(y, 1)
    value = (
        anf_multiply(q_anf, y_anf)
        ^ anf_multiply(x_anf, c_anf)
        ^ anf_multiply(x_anf, y_anf)
    )
    return anf_degree_part(value, 2)


def cubic_kernel(q: int, c: int) -> list[int]:
    columns: list[int] = []
    q_anf = form_to_anf(q, 2)
    c_anf = form_to_anf(c, 2)
    for unit in LINEAR_BASIS:
        columns.append(
            cubic_part(anf_multiply(form_to_anf(unit, 1), c_anf))
        )
    for unit in LINEAR_BASIS:
        columns.append(
            cubic_part(anf_multiply(q_anf, form_to_anf(unit, 1)))
        )
    return nullspace_columns(columns)


def reduced_span_with_tags(generators: list[int]) -> list[tuple[int, int]]:
    pivots: dict[int, tuple[int, int]] = {}
    for index, generator in enumerate(generators):
        value = REDUCE_TARGET(generator)
        tag = 1 << index
        for pivot in sorted(pivots, reverse=True):
            if (value >> pivot) & 1:
                row, old_tag = pivots[pivot]
                value ^= row
                tag ^= old_tag
        if value:
            pivots[value.bit_length() - 1] = (value, tag)
    return list(pivots.values())


def scan_plane(q: int, c: int, populated: set[int]) -> dict[str, object] | None:
    kernel = cubic_kernel(q, c)
    for delta_mask in range(1, 1 << len(kernel)):
        delta = span_vector(kernel, delta_mask)
        x = span_vector(LINEAR_BASIS, delta & ((1 << 10) - 1))
        y = span_vector(LINEAR_BASIS, delta >> 10)
        base = REDUCE_TARGET(quadratic_return(q, c, x, y))
        tagged_directions = reduced_span_with_tags(
            [decomposable_2(unit, y) for unit in LINEAR_BASIS]
            + [decomposable_2(x, unit) for unit in LINEAR_BASIS]
        )
        directions = [row for row, _tag in tagged_directions]
        tags = [tag for _row, tag in tagged_directions]
        for coefficients in range(1 << len(directions)):
            quotient = base ^ span_vector(directions, coefficients)
            if quotient not in populated:
                factor_tag = span_vector(tags, coefficients)
                ell = span_vector(LINEAR_BASIS, factor_tag & ((1 << 10) - 1))
                m = span_vector(LINEAR_BASIS, factor_tag >> 10)
                left = form_to_anf(ell, 1) ^ form_to_anf(q, 2)
                right = form_to_anf(m, 1) ^ form_to_anf(c, 2)
                left_shifted = left ^ form_to_anf(x, 1)
                right_shifted = right ^ form_to_anf(y, 1)
                product = anf_multiply(left, right)
                shifted_product = anf_multiply(left_shifted, right_shifted)
                difference = product ^ shifted_product
                difference_two = anf_degree_part(difference, 2)
                difference_three = anf_degree_part(difference, 3)
                difference_four = anf_degree_part(difference, 4)
                first_three = anf_degree_part(product, 3)
                first_four = anf_degree_part(product, 4)
                second_three = anf_degree_part(shifted_product, 3)
                second_four = anf_degree_part(shifted_product, 4)
                minimum_rank = minimum_target_coset_rank(quotient)
                assert difference_three == 0
                assert difference_four == 0
                assert REDUCE_TARGET(difference_two) == quotient
                assert first_three == second_three
                assert first_four == second_four
                assert first_three != 0 or first_four != 0
                assert minimum_rank > 2
                return {
                    "c": c,
                    "coefficients": coefficients,
                    "direction_dimension": len(directions),
                    "difference_degree_three": difference_three,
                    "difference_degree_four": difference_four,
                    "ell": ell,
                    "first_high_degree_four": first_four,
                    "first_high_degree_three": first_three,
                    "kernel_dimension": len(kernel),
                    "m": m,
                    "minimum_target_coset_rank": minimum_rank,
                    "q": q,
                    "quotient": quotient,
                    "second_high_degree_four": second_four,
                    "second_high_degree_three": second_three,
                    "x": x,
                    "y": y,
                }
    return None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--all-planes", action="store_true")
    args = parser.parse_args()
    populated = populated_quotient_classes()
    print(json.dumps({"populated_classes": len(populated)}), flush=True)
    checked = 0
    counterexamples: list[dict[str, object]] = []
    for q_mask in range(1 << len(RATIONAL_BASIS)):
        q = span_vector(RATIONAL_BASIS, q_mask)
        for c_mask in range(q_mask, 1 << len(RATIONAL_BASIS)):
            c = span_vector(RATIONAL_BASIS, c_mask)
            # The zero plane has no genuinely high product.
            if q == 0 and c == 0:
                continue
            counterexample = scan_plane(q, c, populated)
            checked += 1
            if counterexample is not None:
                orbit_key = plane_orbit_key(q_mask, c_mask)
                report = {
                    "c_mask": c_mask,
                    "checked_planes": checked,
                    "counterexample": counterexample,
                    "plane_orbit_key": orbit_key,
                    "q_mask": q_mask,
                    "result": "unpopulated_return",
                }
                counterexamples.append(report)
                print(json.dumps(report, sort_keys=True), flush=True)
                if not args.all_planes:
                    return
    print(json.dumps({
        "checked_planes": checked,
        "counterexample_planes": len(counterexamples),
        "counterexample_plane_orbits": sorted({
            tuple(report["plane_orbit_key"])
            for report in counterexamples
        }),
        "result": (
            "some_unpopulated_returns" if counterexamples
            else "all_same_plane_returns_populated"
        ),
    }, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
