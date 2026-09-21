#!/usr/bin/env python3
"""Independent audit of the 15 first-input hyperplane orbits for P_6.

This deliberately imports none of the production orbit or capacity code.  It
constructs the two polynomial substitutions coefficient by coefficient,
derives their dual actions from the pairing, enumerates literal set orbits,
and checks the multiplication identities on every input pair.
"""

from __future__ import annotations

from collections import Counter


N = 6
EXPECTED_REPRESENTATIVES = (1, 2, 4, 5, 6, 9, 10, 11, 18, 19, 27, 30, 31, 35, 39)


def parity(value: int) -> int:
    return value.bit_count() & 1


def dot(left: int, right: int) -> int:
    return parity(left & right)


def multiply(left: int, right: int) -> int:
    answer = 0
    for index in range(N):
        if (left >> index) & 1:
            answer ^= right << index
    return answer


def translate_polynomial(mask: int, degree: int) -> int:
    """Coefficient vector of f(x+1), computed from Lucas parity."""
    answer = 0
    for source in range(degree + 1):
        if not ((mask >> source) & 1):
            continue
        for target in range(source + 1):
            if (source & target) == target:
                answer ^= 1 << target
    return answer


def reverse_polynomial(mask: int, degree: int) -> int:
    return sum(
        ((mask >> source) & 1) << (degree - source)
        for source in range(degree + 1)
    )


def dual_action(primal, functional: int) -> int:
    """Solve <dual(functional), primal(v)> = <functional,v> by columns."""
    answer = 0
    for output_coordinate in range(N):
        coefficient = 0
        for input_coordinate in range(N):
            image = primal(1 << input_coordinate)
            coefficient ^= ((image >> output_coordinate) & 1) * (
                (functional >> input_coordinate) & 1
            )
        answer |= coefficient << output_coordinate
    return answer


def translate_dual(functional: int) -> int:
    # Translation is an involution over F_2, so the inverse-transpose equals
    # the transpose derived above.
    primal = lambda value: translate_polynomial(value, N - 1)
    # Directly determine the unique functional by testing all 2^N candidates;
    # this is intentionally independent of the closed-form production code.
    for candidate in range(1 << N):
        if all(
            dot(candidate, primal(vector)) == dot(functional, vector)
            for vector in range(1 << N)
        ):
            return candidate
    raise AssertionError("dual translation does not exist")


def reverse_dual(functional: int) -> int:
    primal = lambda value: reverse_polynomial(value, N - 1)
    for candidate in range(1 << N):
        if all(
            dot(candidate, primal(vector)) == dot(functional, vector)
            for vector in range(1 << N)
        ):
            return candidate
    raise AssertionError("dual reversal does not exist")


def orbit(seed: int) -> frozenset[int]:
    seen = {seed}
    pending = [seed]
    while pending:
        current = pending.pop()
        for image in (translate_dual(current), reverse_dual(current)):
            if image not in seen:
                seen.add(image)
                pending.append(image)
    return frozenset(seen)


def gf2_rank(values: list[int]) -> int:
    rows: dict[int, int] = {}
    for value in values:
        while value:
            pivot = value.bit_length() - 1
            if pivot in rows:
                value ^= rows[pivot]
            else:
                rows[pivot] = value
                break
    return len(rows)


def restriction_target_rank(functional: int) -> int:
    pivot = functional.bit_length() - 1
    kernel_basis = []
    for index in range(N):
        if index == pivot:
            continue
        value = 1 << index
        if (functional >> index) & 1:
            value ^= 1 << pivot
        assert dot(functional, value) == 0
        kernel_basis.append(value)
    outputs = [multiply(left, 1 << right) for left in kernel_basis for right in range(N)]
    return gf2_rank(outputs)


def main() -> None:
    translation = lambda value: translate_polynomial(value, N - 1)
    reversal = lambda value: reverse_polynomial(value, N - 1)
    for value in range(1 << N):
        assert translation(translation(value)) == value
        assert reversal(reversal(value)) == value

    # Check the two tensor automorphisms on all 4096 pairs.
    for left in range(1 << N):
        for right in range(1 << N):
            product = multiply(left, right)
            assert translate_polynomial(product, 2 * N - 2) == multiply(
                translation(left), translation(right)
            )
            assert reverse_polynomial(product, 2 * N - 2) == multiply(
                reversal(left), reversal(right)
            )

    remaining = set(range(1, 1 << N))
    orbits: list[frozenset[int]] = []
    while remaining:
        current = orbit(min(remaining))
        assert current <= remaining
        remaining -= current
        orbits.append(current)

    representatives = tuple(min(current) for current in orbits)
    assert representatives == EXPECTED_REPRESENTATIVES
    assert len(orbits) == 15
    assert sum(map(len, orbits)) == 63
    assert Counter(map(len, orbits)) == {6: 7, 3: 6, 2: 1, 1: 1}

    target_profiles = []
    for current in orbits:
        ranks = {restriction_target_rank(functional) for functional in current}
        assert len(ranks) == 1
        target_profiles.append(next(iter(ranks)))
    assert Counter(target_profiles) == {11: 14, 10: 1}
    assert target_profiles[0] == 10

    print("N6_INDEPENDENT_ORBIT_AUDIT_PASS")
    print("constraints=63 orbits=15 input_pairs=4096")
    print("representatives=" + ",".join(map(str, representatives)))
    print("orbit_sizes=" + ",".join(map(str, map(len, orbits))))
    print("target_profiles=10:1,11:14")


if __name__ == "__main__":
    main()
