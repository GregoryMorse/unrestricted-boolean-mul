#!/usr/bin/env python3
"""Exact counterexample to uniform exterior-kernel sterility of returns.

The calculation is finite coordinate algebra, not a circuit search.  Two
products on the rational factor pair ``(0, r0)`` have the same nonzero high
part.  Their quadratic return is unpopulated modulo the Hankel target, but
the missing-target translate has the nonzero rational annihilator ``r0``.
Consequently unpopulatedness plus the equal-high cubic syzygy cannot by
itself discharge the rational branch of the feedback argument.
"""

from quadratic_return_population_probe import (
    REDUCE_TARGET,
    cubic_part,
    minimum_target_coset_rank,
    quadratic_return,
)
from w_pq_analysis import (
    A,
    B,
    T,
    anf_degree_part,
    anf_multiply,
    decomposable_2,
    form_to_anf,
    r0,
    wedge,
)


def low_product(ell: int, m: int, q: int, c: int) -> int:
    return anf_multiply(
        form_to_anf(ell, 1) ^ form_to_anf(q, 2),
        form_to_anf(m, 1) ^ form_to_anf(c, 2),
    )


def main() -> None:
    # ell = a0 + a1 + b0, x = a0 + b0, y = a0 + b1,
    # m = a1 + a3 + a4 + b0 + b1 + b2 + b3.
    ell = A[0] ^ A[1] ^ B[0]
    x = A[0] ^ B[0]
    y = A[0] ^ B[1]
    m = A[1] ^ A[3] ^ A[4] ^ B[0] ^ B[1] ^ B[2] ^ B[3]

    first = low_product(ell, m, 0, r0)
    second = low_product(ell ^ x, m ^ y, 0, r0)
    first_high = cubic_part(first) | anf_degree_part(first, 4)
    second_high = cubic_part(second) | anf_degree_part(second, 4)
    return_two = anf_degree_part(first ^ second, 2)

    assert first_high == second_high
    assert first_high != 0
    assert return_two == (
        quadratic_return(0, r0, x, y)
        ^ decomposable_2(ell, y)
        ^ decomposable_2(x, m)
    )
    assert minimum_target_coset_rank(return_two) == 4
    assert wedge(return_two ^ T[2], 2, r0, 2) == 0

    print({
        "factor_pair": "(0,r0)",
        "same_nonzero_high_part": True,
        "return_quotient": REDUCE_TARGET(return_two),
        "minimum_target_coset_rank": 4,
        "nonzero_rational_annihilator": "r0",
        "result": "uniform_return_kernel_certificate_false",
    })


if __name__ == "__main__":
    main()
