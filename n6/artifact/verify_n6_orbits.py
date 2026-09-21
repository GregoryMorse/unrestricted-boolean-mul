#!/usr/bin/env python3
"""Verify the PGL(2,F_2) constraint orbits and tensor symmetries for P_6."""

from __future__ import annotations

from n6_constraint_orbits import N, REPRESENTATIVES, orbit, reverse, translate_dual


def translate(mask: int, degree: int) -> int:
    result = 0
    for j in range(degree + 1):
        bit = 0
        for i in range(j, degree + 1):
            if (i & j) == j:  # Lucas: binomial(i,j) is odd.
                bit ^= (mask >> i) & 1
        result |= bit << j
    return result


def reverse_degree(mask: int, degree: int) -> int:
    return sum(((mask >> i) & 1) << (degree - i) for i in range(degree + 1))


def multiply(a: int, b: int) -> int:
    result = 0
    for i in range(N):
        if (a >> i) & 1:
            result ^= b << i
    return result


def dot(a: int, b: int) -> int:
    return (a & b).bit_count() & 1


def main() -> None:
    assert N == 6
    orbits = {orbit(mask) for mask in range(1, 1 << N)}
    assert len(orbits) == 15
    assert {min(current) for current in orbits} == set(REPRESENTATIVES)
    assert set().union(*orbits) == set(range(1, 1 << N))
    assert sum(map(len, orbits)) == (1 << N) - 1

    # Translation x -> x+1 and coefficient reversal are multiplication-tensor
    # automorphisms.  The displayed dual actions preserve the constraint pairing.
    for a in range(1 << N):
        assert translate(translate(a, N - 1), N - 1) == a
        assert reverse_degree(reverse_degree(a, N - 1), N - 1) == a
        for h in range(1 << N):
            assert dot(translate_dual(h), translate(a, N - 1)) == dot(h, a)
            assert dot(reverse(h), reverse_degree(a, N - 1)) == dot(h, a)
        for b in range(1 << N):
            product = multiply(a, b)
            assert translate(product, 2 * N - 2) == multiply(
                translate(a, N - 1), translate(b, N - 1)
            )
            assert reverse_degree(product, 2 * N - 2) == multiply(
                reverse_degree(a, N - 1), reverse_degree(b, N - 1)
            )

    print("N6_CONSTRAINT_ORBITS_AND_SYMMETRIES_PASS")
    print("constraints=63 orbits=15 input_pairs_checked=4096")


if __name__ == "__main__":
    main()
