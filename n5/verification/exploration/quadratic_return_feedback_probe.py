#!/usr/bin/env python3
"""Probe full historical feedback for quadratic-return counterexamples.

This is a small linear solve for each of the 2,048 lower feedback factors
whose quadratic part is the rational direction ``r0``.  It asks whether the
already-born high product, corrected by an arbitrary quadratic wire in the
returned section, can multiply by that factor to produce the missing target
coset.  It is a discovery aid, never a proof premise.
"""

import argparse

from quadratic_return_class_sample import FIRST_ORDER_MASKS, target_from_mask
from quadratic_return_kernel_counterexample import low_product
from quadratic_return_population_probe import (
    LINEAR_BASIS,
    REDUCE_TARGET,
    cubic_kernel,
    populated_quotient_classes,
    quadratic_return,
    reduced_span_with_tags,
)
from w_pq_analysis import (
    A,
    B,
    COMBS,
    anf_degree_part,
    anf_multiply,
    decomposable_2,
    form_to_anf,
    iterbits,
    r0,
    r1,
    rinf,
    span_vector,
)


def target_missing_functional(form: int) -> int:
    def cross(i: int, j: int) -> int:
        basis = decomposable_2(A[i], B[j])
        return int(bool(form & basis))

    return cross(0, 2) ^ cross(0, 3) ^ cross(1, 4) ^ cross(2, 4)


def signature(poly: int) -> int:
    # Raw ANF bits are indexed by their ten-variable monomial masks, hence
    # the degree-at-least-three part already fits below bit 1024.  In
    # contrast, ``anf_degree_part`` returns the packed exterior-form
    # coordinates used by the rest of these probes.
    high = sum(
        1 << monomial
        for monomial in iterbits(poly)
        if monomial.bit_count() >= 3
    )
    quadratic = anf_degree_part(poly, 2)
    return (
        high
        ^ (REDUCE_TARGET(quadratic) << 1024)
        ^ (target_missing_functional(quadratic) << 1070)
    )


def solve_columns(columns: list[int], rhs: int) -> int | None:
    pivots: dict[int, tuple[int, int]] = {}
    for index, column in enumerate(columns):
        value = column
        tag = 1 << index
        for pivot in sorted(pivots, reverse=True):
            if (value >> pivot) & 1:
                row, old_tag = pivots[pivot]
                value ^= row
                tag ^= old_tag
        if not value:
            continue
        pivot = value.bit_length() - 1
        for old_pivot, (row, old_tag) in list(pivots.items()):
            if (row >> pivot) & 1:
                pivots[old_pivot] = (row ^ value, old_tag ^ tag)
        pivots[pivot] = (value, tag)

    tag = 0
    for pivot in sorted(pivots, reverse=True):
        if (rhs >> pivot) & 1:
            row, old_tag = pivots[pivot]
            rhs ^= row
            tag ^= old_tag
    return tag if rhs == 0 else None


def historical_escape_solutions(
    g: int, return_two: int, factor_two: int, sample_limit: int = 16
) -> tuple[int, list[dict[str, int | bool]]]:
    quadratic_basis = (
        [1]
        + [form_to_anf(1 << i, 1) for i in range(10)]
        + [form_to_anf(target_from_mask(mask), 2)
           for mask in FIRST_ORDER_MASKS]
        + [form_to_anf(return_two, 2)]
    )
    desired = (
        REDUCE_TARGET(return_two) << 1024
        ^ ((1 ^ target_missing_functional(return_two)) << 1070)
    )

    result_count = 0
    result_samples: list[dict[str, int | bool]] = []
    for constant in range(2):
        for linear_mask in range(1 << 10):
            factor = (
                constant
                ^ form_to_anf(linear_mask, 1)
                ^ form_to_anf(factor_two, 2)
            )
            base = anf_multiply(g, factor)
            columns = [signature(anf_multiply(w, factor))
                       for w in quadratic_basis]
            solution = solve_columns(columns, signature(base) ^ desired)
            if solution is None:
                continue
            correction = 0
            for index, wire in enumerate(quadratic_basis):
                if (solution >> index) & 1:
                    correction ^= wire
            product = anf_multiply(g ^ correction, factor)
            result_count += 1
            if len(result_samples) < sample_limit:
                result_samples.append({
                    "constant": constant,
                    "linear_mask": linear_mask,
                    "correction_mask": solution,
                    "product_signature_ok": signature(product) == desired,
                })

    return result_count, result_samples


def exact_counterexample_report() -> dict[str, object]:
    ell = A[0] ^ A[1] ^ B[0]
    x = A[0] ^ B[0]
    y = A[0] ^ B[1]
    m = A[1] ^ A[3] ^ A[4] ^ B[0] ^ B[1] ^ B[2] ^ B[3]
    g = low_product(ell, m, 0, r0)
    shifted = low_product(ell ^ x, m ^ y, 0, r0)
    return_two = anf_degree_part(g ^ shifted, 2)
    result_count, result_samples = historical_escape_solutions(
        g, return_two, r0
    )
    return {
        "feedback_factors": 2 * (1 << 10),
        "historical_escape_solution_count": result_count,
        "historical_escape_solution_samples": result_samples,
        "result": "historical_escape_found" if result_count else
            "retained_high_rep_blocks_this_witness",
    }


def biased_return_sample_report(
    limit: int, selected_case: str | None = None
) -> dict[str, object]:
    """Test the first distinct unpopulated classes in each factor-pair type.

    The ordering is deliberately the same biased ordering as
    ``quadratic_return_class_sample.py``.  This is falsification pressure for
    a history-sensitive theorem, never a completeness claim.
    """
    populated = populated_quotient_classes()
    cases = [
        ("zero_one", 0, r0),
        ("one_one", r0, r0),
        ("one_two", r0, r1),
        ("one_three", r0, r0 ^ r1),
    ]
    if selected_case is not None:
        cases = [case for case in cases if case[0] == selected_case]
    tested = 0
    reports: list[dict[str, object]] = []
    for name, q, c in cases:
        cubic_basis = cubic_kernel(q, c)
        seen: set[int] = set()
        case_tested = 0
        for delta_mask in range(1, 1 << len(cubic_basis)):
            delta = span_vector(cubic_basis, delta_mask)
            x = span_vector(LINEAR_BASIS, delta & ((1 << 10) - 1))
            y = span_vector(LINEAR_BASIS, delta >> 10)
            base = REDUCE_TARGET(quadratic_return(q, c, x, y))
            tagged = reduced_span_with_tags(
                [decomposable_2(unit, y) for unit in LINEAR_BASIS]
                + [decomposable_2(x, unit) for unit in LINEAR_BASIS]
            )
            directions = [row for row, _ in tagged]
            tags = [tag for _, tag in tagged]
            for coefficients in range(1 << len(directions)):
                quotient = base ^ span_vector(directions, coefficients)
                if quotient in populated or quotient in seen:
                    continue
                factor_tag = span_vector(tags, coefficients)
                ell = span_vector(
                    LINEAR_BASIS, factor_tag & ((1 << 10) - 1)
                )
                m = span_vector(LINEAR_BASIS, factor_tag >> 10)
                g = low_product(ell, m, q, c)
                if not (
                    anf_degree_part(g, 3) or anf_degree_part(g, 4)
                ):
                    continue
                shifted = low_product(ell ^ x, m ^ y, q, c)
                return_two = anf_degree_part(g ^ shifted, 2)
                seen.add(quotient)
                for direction_name, direction in (
                    ("r0", r0), ("r1", r1), ("rinf", rinf)
                ):
                    count, samples = historical_escape_solutions(
                        g, return_two, direction, sample_limit=4
                    )
                    tested += 1
                    case_tested += 1
                    if count:
                        return {
                            "case": name,
                            "direction": direction_name,
                            "historical_escape_solution_count": count,
                            "historical_escape_solution_samples": samples,
                            "quotient": quotient,
                            "result": "historical_escape_found",
                            "tested_section_direction_pairs": tested,
                        }
                if len(seen) >= limit:
                    break
            if len(seen) >= limit:
                break
        reports.append({
            "case": name,
            "distinct_unpopulated_sections": len(seen),
            "section_direction_pairs": case_tested,
        })
    return {
        "reports": reports,
        "result": "no_historical_escape_in_biased_sample",
        "tested_section_direction_pairs": tested,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--sample-per-case", type=int, default=0,
        help="also scan this many biased unpopulated sections per factor-pair type",
    )
    parser.add_argument(
        "--sample-case",
        choices=("zero_one", "one_one", "one_two", "one_three"),
        help="restrict the optional biased scan to one factor-pair type",
    )
    args = parser.parse_args()
    print(exact_counterexample_report())
    if args.sample_per_case:
        print(biased_return_sample_report(
            args.sample_per_case, args.sample_case
        ))


if __name__ == "__main__":
    main()
