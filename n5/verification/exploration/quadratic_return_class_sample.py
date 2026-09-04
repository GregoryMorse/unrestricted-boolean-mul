#!/usr/bin/env python3
"""Bounded diagnostic for rational quadratic-return quotient classes.

This does not enumerate circuits.  It samples the linear cubic-kernel model
already used by ``quadratic_return_population_probe.py`` and checks at most
64 distinct unpopulated quotient classes for each of the four rational
factor-pair types.  Finding more than 24 classes in one type refutes the
proposed classification by four fixed sections and six rational-place words.
The additional exterior-kernel loop only reports what happens in the first
64 classes encountered by this ordering.  It is not evidence for a uniform
kernel theorem: ``quadratic_return_kernel_counterexample.py`` gives an exact
counterexample outside that biased initial sample.
"""

from quadratic_return_population_probe import (
    LINEAR_BASIS,
    REDUCE_TARGET,
    cubic_kernel,
    cubic_part,
    populated_quotient_classes,
    quadratic_return,
    reduced_span_with_tags,
    target_wedge_kernel,
)
from w_pq_analysis import (
    anf_degree_part,
    anf_multiply,
    decomposable_2,
    form_to_anf,
    r0,
    r1,
    span_vector,
    T,
)


FIRST_ORDER_MASKS = [
    1 << 0,
    (1 << 9) - 1,
    1 << 8,
    1 << 1,
    (1 << 1) | (1 << 3) | (1 << 5) | (1 << 7),
    1 << 7,
    (1 << 2) | (1 << 5),
    (1 << 3) | (1 << 6),
]


def target_from_mask(mask: int) -> int:
    return span_vector(T, mask)


def main() -> None:
    populated = populated_quotient_classes()
    first_order_targets = [target_from_mask(mask) for mask in FIRST_ORDER_MASKS]
    cases = [
        ("zero_one", 0, r0),
        ("one_one", r0, r0),
        ("one_two", r0, r1),
        ("one_three", r0, r0 ^ r1),
    ]
    reports = []
    for name, q, c in cases:
        cubic_basis = cubic_kernel(q, c)
        unpopulated: dict[int, tuple[int, int, int]] = {}
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
                if quotient in populated or quotient in unpopulated:
                    continue
                factor_tag = span_vector(tags, coefficients)
                ell = span_vector(
                    LINEAR_BASIS, factor_tag & ((1 << 10) - 1)
                )
                m = span_vector(LINEAR_BASIS, factor_tag >> 10)
                left = form_to_anf(ell, 1) ^ form_to_anf(q, 2)
                right = form_to_anf(m, 1) ^ form_to_anf(c, 2)
                product = anf_multiply(left, right)
                high = cubic_part(product) | anf_degree_part(product, 4)
                if high == 0:
                    continue
                shifted = form_to_anf(ell ^ x, 1) ^ form_to_anf(q, 2)
                shifted_right = (
                    form_to_anf(m ^ y, 1) ^ form_to_anf(c, 2)
                )
                difference_two = anf_degree_part(
                    product ^ anf_multiply(shifted, shifted_right), 2
                )
                assert REDUCE_TARGET(difference_two) == quotient
                unpopulated[quotient] = (
                    delta_mask, coefficients, difference_two
                )
                for u_mask in range(1 << len(FIRST_ORDER_MASKS)):
                    u = span_vector(first_order_targets, u_mask)
                    affine_missing = difference_two ^ T[2] ^ u
                    wedge_kernel = target_wedge_kernel(affine_missing)
                    if wedge_kernel:
                        print({
                            "case": name,
                            "distinct_unpopulated_classes": len(unpopulated),
                            "kernel_basis": wedge_kernel,
                            "quotient": quotient,
                            "result": "generic_kernel_certificate_false",
                            "u_mask": u_mask,
                        })
                        return
                if len(unpopulated) >= 64:
                    break
            if len(unpopulated) >= 64:
                break
        reports.append({
            "case": name,
            "cubic_kernel_dimension": len(cubic_basis),
            "distinct_unpopulated_classes_checked": len(unpopulated),
            "first_classes": sorted(unpopulated)[:8],
        })
    print({
        "reports": reports,
        "result": "no_kernel_seen_in_first_64_ordered_samples",
    })


if __name__ == "__main__":
    main()
