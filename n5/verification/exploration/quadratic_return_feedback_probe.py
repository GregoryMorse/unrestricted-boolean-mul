#!/usr/bin/env python3
"""Probe full historical feedback for the explicit return counterexample.

This is a small linear solve for each of the 2,048 lower feedback factors
whose quadratic part is the rational direction ``r0``.  It asks whether the
already-born high product, corrected by an arbitrary quadratic wire in the
returned section, can multiply by that factor to produce the missing target
coset.  It is a discovery aid, never a proof premise.
"""

from quadratic_return_class_sample import FIRST_ORDER_MASKS, target_from_mask
from quadratic_return_kernel_counterexample import low_product
from quadratic_return_population_probe import REDUCE_TARGET
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


def main() -> None:
    ell = A[0] ^ A[1] ^ B[0]
    x = A[0] ^ B[0]
    y = A[0] ^ B[1]
    m = A[1] ^ A[3] ^ A[4] ^ B[0] ^ B[1] ^ B[2] ^ B[3]
    g = low_product(ell, m, 0, r0)
    shifted = low_product(ell ^ x, m ^ y, 0, r0)
    return_two = anf_degree_part(g ^ shifted, 2)

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
    result_samples = []
    for constant in range(2):
        for linear_mask in range(1 << 10):
            factor = (
                constant
                ^ form_to_anf(linear_mask, 1)
                ^ form_to_anf(r0, 2)
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
            if len(result_samples) < 16:
                result_samples.append({
                    "constant": constant,
                    "linear_mask": linear_mask,
                    "correction_mask": solution,
                    "product_signature_ok": signature(product) == desired,
                })

    print({
        "feedback_factors": 2 * (1 << 10),
        "historical_escape_solution_count": result_count,
        "historical_escape_solution_samples": result_samples,
        "result": "historical_escape_found" if result_count else
            "retained_high_rep_blocks_this_witness",
    })


if __name__ == "__main__":
    main()
