#!/usr/bin/env python3
"""Exact target-tight continuation probe for a fixed Boolean wire state.

Functions are represented by their full 10-variable truth tables in Python
integers.  The search never enumerates pairs of functions.  For each first
factor ``p`` it row-reduces the linear map ``q |-> p*q (mod V)`` and intersects
its image with the missing target quotient.  Thus every reported transition
is exhaustive for the supplied state.

This file is an exploratory theorem-discovery aid.  Its output is not imported
by Lean and an exhaustive run for one state is not a proof of a universal
suffix theorem.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass


VARIABLE_COUNT = 10
WIDTH = 1 << VARIABLE_COUNT
ALL_ONES = (1 << WIDTH) - 1


def variable_truth_table(variable: int) -> int:
    return sum(
        ((assignment >> variable) & 1) << assignment
        for assignment in range(WIDTH)
    )


X = [variable_truth_table(i) for i in range(VARIABLE_COUNT)]
A = X[:5]
B = X[5:]


def xor_all(values) -> int:
    result = 0
    for value in values:
        result ^= value
    return result


TARGETS = [
    xor_all(A[i] & B[degree - i]
            for i in range(5) if 0 <= degree - i < 5)
    for degree in range(9)
]

# Exact eight target directions spanning the first-order envelope used by
# TargetCleanMatrix.lean.  These are coefficient masks in the TARGETS basis.
FIRST_ORDER_TARGET_MASKS = [
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
    return xor_all(
        target for index, target in enumerate(TARGETS)
        if (mask >> index) & 1
    )


FIRST_ORDER_TARGETS = [
    target_from_mask(mask) for mask in FIRST_ORDER_TARGET_MASKS
]


def reduce_vector(vector: int, basis: dict[int, int]) -> int:
    for pivot in sorted(basis, reverse=True):
        if (vector >> pivot) & 1:
            vector ^= basis[pivot]
    return vector


def canonical_basis(vectors) -> dict[int, int]:
    basis: dict[int, int] = {}
    for original in vectors:
        vector = reduce_vector(original, basis)
        if not vector:
            continue
        pivot = vector.bit_length() - 1
        for old_pivot, row in list(basis.items()):
            if (row >> pivot) & 1:
                basis[old_pivot] = row ^ vector
        basis[pivot] = vector
    return dict(sorted(basis.items(), reverse=True))


def basis_key(vectors) -> tuple[int, ...]:
    return tuple(canonical_basis(vectors).values())


def complement_with_one(state_key: tuple[int, ...]) -> list[int]:
    chosen = [ALL_ONES]
    span = canonical_basis(chosen)
    for row in state_key:
        if reduce_vector(row, span):
            chosen.append(row)
            span = canonical_basis(chosen)
    assert len(chosen) == len(state_key)
    return chosen


def quotient_target_basis(state: dict[int, int]) -> dict[int, int]:
    return canonical_basis(reduce_vector(target, state) for target in TARGETS)


def span_vectors(basis: dict[int, int]) -> list[int]:
    rows = list(basis.values())
    values = [0]
    for row in rows:
        values += [value ^ row for value in values]
    return values


def image_basis_with_preimages(
    p: int, q_basis: list[int], state: dict[int, int]
) -> dict[int, tuple[int, int]]:
    """Basis for p*V/V; tags encode the selected q-basis vectors."""
    image: dict[int, tuple[int, int]] = {}
    for index, q in enumerate(q_basis):
        vector = reduce_vector(p & q, state)
        tag = 1 << index
        for pivot in sorted(image, reverse=True):
            row = image[pivot]
            if (vector >> pivot) & 1:
                vector ^= row[0]
                tag ^= row[1]
        if not vector:
            continue
        pivot = vector.bit_length() - 1
        for old_pivot, (old_vector, old_tag) in list(image.items()):
            if (old_vector >> pivot) & 1:
                image[old_pivot] = (old_vector ^ vector, old_tag ^ tag)
        image[pivot] = (vector, tag)
    return image


def image_preimage(
    target_coset: int, image: dict[int, tuple[int, int]]
) -> int | None:
    vector = target_coset
    tag = 0
    for pivot in sorted(image, reverse=True):
        row = image[pivot]
        if (vector >> pivot) & 1:
            vector ^= row[0]
            tag ^= row[1]
    return tag if vector == 0 else None


@dataclass(frozen=True)
class Transition:
    target_coset: int
    p: int
    q: int


def target_tight_transitions(state_key: tuple[int, ...]) -> list[Transition]:
    state = canonical_basis(state_key)
    factors = complement_with_one(state_key)[1:]
    target_quotient = quotient_target_basis(state)
    missing_cosets = set(span_vectors(target_quotient))
    missing_cosets.discard(0)
    found: dict[int, Transition] = {}

    # Gray-code enumeration updates the first factor with one XOR each.
    p = 0
    previous_gray = 0
    for counter in range(1 << len(factors)):
        gray = counter ^ (counter >> 1)
        if counter:
            changed = gray ^ previous_gray
            index = changed.bit_length() - 1
            p ^= factors[index]
        previous_gray = gray

        image = image_basis_with_preimages(p, factors, state)
        for target_coset in missing_cosets - found.keys():
            q_tag = image_preimage(target_coset, image)
            if q_tag is None:
                continue
            q = xor_all(
                factors[index]
                for index in range(len(factors))
                if (q_tag >> index) & 1
            )
            assert reduce_vector((p & q) ^ target_coset, state) == 0
            found[target_coset] = Transition(target_coset, p, q)
        if len(found) == len(missing_cosets):
            break

    return [found[key] for key in sorted(found)]


def target_rank(state_key: tuple[int, ...]) -> int:
    state = canonical_basis(state_key)
    return 9 - len(quotient_target_basis(state))


def ce_prefix_after_first_high() -> tuple[int, ...]:
    r0 = A[0] & B[0]
    anchor = (A[0] ^ B[1]) & (A[1] ^ B[0])
    right_first = ALL_ONES ^ B[0]
    right_second = A[0] ^ A[1] ^ A[2] ^ B[0] ^ B[1] ^ B[2] ^ r0
    first_high = right_first & right_second
    return basis_key([ALL_ONES, *X, r0, anchor, first_high])


def ce_capacity_after_first_high() -> tuple[int, ...]:
    """Intrinsic decomposable capacity of the displayed defect line, then birth."""
    affine_target = canonical_basis([ALL_ONES, *X, *TARGETS])
    anchor = (A[0] ^ B[1]) & (A[1] ^ B[0])
    anchor_quotient = reduce_vector(anchor, affine_target)

    linear_forms = [0]
    for variable in X:
        linear_forms += [value ^ variable for value in linear_forms]

    products = []
    for left_index, left in enumerate(linear_forms):
        for right in linear_forms[left_index:]:
            product = left & right
            quotient = reduce_vector(product, affine_target)
            if quotient == 0 or quotient == anchor_quotient:
                products.append(product)

    capacity = basis_key([ALL_ONES, *X, *products])
    print(
        f"capacity_products={len(products)} capacity_dimension={len(capacity)} "
        f"capacity_target_rank={target_rank(capacity)}"
    )

    r0 = A[0] & B[0]
    right_first = ALL_ONES ^ B[0]
    right_second = A[0] ^ A[1] ^ A[2] ^ B[0] ^ B[1] ^ B[2] ^ r0
    first_high = right_first & right_second
    return basis_key([*capacity, first_high])


def quadratic_return_state(
    q: int, c: int, ell: int, m: int, x: int, y: int
) -> tuple[int, ...]:
    """Rational capacity plus two equal-high low products."""
    r0 = TARGETS[0]
    r1 = xor_all(TARGETS)
    rinf = TARGETS[-1]
    first = (ell ^ q) & (m ^ c)
    second = (ell ^ x ^ q) & (m ^ y ^ c)
    return basis_key([ALL_ONES, *X, r0, r1, rinf, first, second])


def unpopulated_quadratic_return_state(orbit: str = "01") -> tuple[int, ...]:
    """One exact rank-four return for each rational-plane S3 orbit."""
    r0 = TARGETS[0]
    r1 = xor_all(TARGETS)
    if orbit == "01":
        return quadratic_return_state(
            0, r0, A[2] ^ B[2], A[2], B[0], A[0]
        )
    if orbit == "11":
        return quadratic_return_state(
            r0, r0, A[2] ^ B[2], A[2], B[0], A[0]
        )
    if orbit == "12":
        return quadratic_return_state(
            r0, r1, A[1] ^ A[2], A[1], xor_all(A), A[0]
        )
    if orbit == "13":
        return quadratic_return_state(
            r0, r0 ^ r1, A[1] ^ A[2], A[1], xor_all(A),
            A[1] ^ A[2] ^ A[3] ^ A[4]
        )
    raise ValueError(f"unknown return orbit {orbit}")


def saturated_first_order_return_state(orbit: str = "01") -> tuple[int, ...]:
    """The same return block after granting the full first-order target base."""
    return basis_key([
        *unpopulated_quadratic_return_state(orbit), *FIRST_ORDER_TARGETS,
    ])


def one_defect_quadratic_return_state(kind: str) -> tuple[int, ...]:
    """Canonical doubly-unpopulated return over a one-defect capacity base."""
    r0 = TARGETS[0]
    r1 = xor_all(TARGETS)
    rinf = TARGETS[-1]
    if kind == "pstar":
        u = A[0] ^ A[2] ^ A[3]
        v = A[1] ^ A[2] ^ A[4]
        upper_u = B[0] ^ B[2] ^ B[3]
        upper_v = B[1] ^ B[2] ^ B[4]
        x00 = u & upper_u
        x11 = v & upper_v
        xsum = (u ^ v) & (upper_u ^ upper_v)
        ell, m, x, y = A[1] ^ A[2], A[1], u, A[0]
        first = ell & (m ^ x00)
        second = (ell ^ x) & (m ^ y ^ x00)
        return basis_key([
            ALL_ONES, *X, x00, x11, xsum, r0, r1, rinf, first, second,
        ])
    if kind == "rational":
        j0 = TARGETS[1]
        d0 = A[1] & B[1]
        ell, m, x, y = B[3], A[3], B[0], A[0]
        first = ell & (m ^ r0)
        second = (ell ^ x) & (m ^ y ^ r0)
        return basis_key([
            ALL_ONES, *X, r0, j0, d0, r1, rinf, first, second,
        ])
    raise ValueError(f"unknown one-defect return block {kind}")


def run_frontier(
    initial: tuple[int, ...], label: str, max_levels: int = 8
) -> None:
    frontier = {initial}
    seen = set(frontier)
    print(f"state={label} level=0 states=1 target_rank={target_rank(initial)}")

    for level in range(1, max_levels + 1):
        next_frontier: set[tuple[int, ...]] = set()
        transition_count = 0
        ranks = set()
        for state_key in frontier:
            transitions = target_tight_transitions(state_key)
            transition_count += len(transitions)
            for transition in transitions:
                child = basis_key([*state_key, transition.target_coset])
                assert len(child) == len(state_key) + 1
                ranks.add(target_rank(child))
                if child not in seen:
                    seen.add(child)
                    next_frontier.add(child)
        print(
            f"level={level} parents={len(frontier)} "
            f"transitions={transition_count} new_states={len(next_frontier)} "
            f"target_ranks={sorted(ranks)}"
        )
        if not next_frontier:
            break
        frontier = next_frontier


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--state",
        choices=(
            "literal", "capacity", "unpopulated-return", "return-01",
            "return-11", "return-12", "return-13", "all",
            "return-pstar", "return-e1r0", "return-u01", "return-u11",
            "return-u12", "return-u13",
        ),
        default="all",
    )
    parser.add_argument("--max-levels", type=int, default=8)
    args = parser.parse_args()
    if args.state in ("literal", "all"):
        run_frontier(
            ce_prefix_after_first_high(), "literal-prefix-after-birth",
            args.max_levels,
        )
    if args.state in ("capacity", "all"):
        run_frontier(
            ce_capacity_after_first_high(), "capacity-after-birth",
            args.max_levels,
        )
    if args.state == "unpopulated-return":
        run_frontier(
            unpopulated_quadratic_return_state(),
            "unpopulated-quadratic-return",
            args.max_levels,
        )
    for orbit in ("01", "11", "12", "13"):
        if args.state in (f"return-{orbit}", "all"):
            run_frontier(
                unpopulated_quadratic_return_state(orbit),
                f"unpopulated-return-orbit-{orbit}",
                args.max_levels,
            )
        if args.state == f"return-u{orbit}":
            run_frontier(
                saturated_first_order_return_state(orbit),
                f"first-order-saturated-return-orbit-{orbit}",
                args.max_levels,
            )
    if args.state == "return-pstar":
        run_frontier(
            one_defect_quadratic_return_state("pstar"),
            "one-defect-degree-two-return", args.max_levels,
        )
    if args.state == "return-e1r0":
        run_frontier(
            one_defect_quadratic_return_state("rational"),
            "one-defect-rational-return", args.max_levels,
        )
