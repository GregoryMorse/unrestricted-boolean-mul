#!/usr/bin/env python3
"""Exact symbolic check of the displayed thirteen-product upper circuit."""

LINEAR_SUPPORTS = [
    {0}, {1}, {0, 1}, {2}, {0, 2}, {3}, {0, 2, 3},
    {4}, {2, 4}, {1, 2, 4}, {3, 4}, {0, 1, 3, 4},
    {0, 1, 2, 3, 4},
]

OUTPUT_SUPPORTS = [
    {0},
    {0, 1, 2},
    {0, 1, 3, 4},
    {0, 3, 5, 6, 7, 8, 11, 12},
    {0, 1, 2, 5, 6, 7, 9, 10, 12},
    {0, 1, 3, 4, 7, 9, 11, 12},
    {3, 5, 7, 8},
    {5, 7, 10},
    {7},
]


def gate_monomials(index: int) -> set[tuple[int, int]]:
    support = LINEAR_SUPPORTS[index]
    return {(i, j) for i in support for j in support}


def xor_sets(sets: list[set[tuple[int, int]]]) -> set[tuple[int, int]]:
    result: set[tuple[int, int]] = set()
    for terms in sets:
        result.symmetric_difference_update(terms)
    return result


def main() -> None:
    gates = [gate_monomials(i) for i in range(13)]
    for degree, support in enumerate(OUTPUT_SUPPORTS):
        actual = xor_sets([gates[i] for i in support])
        expected = {(i, j) for i in range(5) for j in range(5) if i + j == degree}
        if actual != expected:
            raise SystemExit(
                f"FAIL c{degree}: missing={sorted(expected - actual)} "
                f"extra={sorted(actual - expected)}"
            )
    print("PASS gates=13 outputs=9 bilinear_monomials=25")


if __name__ == "__main__":
    main()
