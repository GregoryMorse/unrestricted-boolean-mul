from __future__ import annotations

import w_pq_analysis as e


# Discovery-only audit of the cubic syzygy map on the projective planes in
# the exact eight-direction basis from TargetCleanMatrix.lean.  This script is
# not a proof premise; it guards the statement of the subsequent algebraic
# Lean classification.

COEFFS = [
    1 << 0,
    (1 << 9) - 1,
    1 << 8,
    1 << 1,
    (1 << 1) | (1 << 3) | (1 << 5) | (1 << 7),
    1 << 7,
    (1 << 2) | (1 << 5),
    (1 << 3) | (1 << 6),
]
UBASIS = [e.span_vector(e.T, c) for c in COEFFS]
LINEARS = [e.linear_form([i]) for i in range(10)]


def form(c: int) -> int:
    return e.span_vector(UBASIS, c)


def plane(a: int, b: int) -> tuple[int, int, int]:
    return tuple(sorted((a, b, a ^ b)))


MANUSCRIPT_LOCAL = {
    plane(1 << 0, 1 << 3),
    plane(1 << 1, 1 << 4),
    plane(1 << 2, 1 << 5),
    plane(1 << 0, 1 << 1),
    plane(1 << 0, 1 << 2),
    plane(1 << 1, 1 << 2),
    plane(1 << 6, 1 << 7),
}

# The only non-rigid plane without a rational value direction.  In exact
# first-order coordinates its nonzero points are 0x46, 0x83, and 0xc5.  The
# first two are D_* directions adjusted by rational values.
DEGREE_TWO_TRANSLATE = plane(0x46, 0x83)


def main() -> None:
    seen: set[tuple[int, int, int]] = set()
    nonrigid: list[tuple[tuple[int, int, int], int]] = []
    for a in range(1, 1 << 8):
        for b in range(a + 1, 1 << 8):
            key = plane(a, b)
            if key in seen:
                continue
            seen.add(key)
            q, c = form(a), form(b)
            columns = [e.wedge(l, 1, c, 2) for l in LINEARS]
            columns += [e.wedge(l, 1, q, 2) for l in LINEARS]
            r = e.rank(columns)
            if r < 20:
                nonrigid.append((key, r))
    print("planes", len(seen), "nonrigid", len(nonrigid))
    print("rank counts", {r: sum(s == r for _, s in nonrigid)
                           for r in sorted({s for _, s in nonrigid})})
    nonrigid_planes = {p for p, _ in nonrigid}
    print("manuscript local nonrigid", len(MANUSCRIPT_LOCAL & nonrigid_planes))
    print("manuscript local rigid", len(MANUSCRIPT_LOCAL - nonrigid_planes))
    rational_points = {1 << 0, 1 << 1, 1 << 2}
    without_rational = [(p, r) for p, r in nonrigid
                        if not (set(p) & rational_points)]
    print("without rational point", len(without_rational))
    print("rational-or-degree-two-translate",
          all(set(p) & rational_points or p == DEGREE_TWO_TRANSLATE
              for p, _ in nonrigid))
    for p, r in without_rational:
        print("non-rational", r, tuple(f"{x:08b}" for x in p),
              "degree-two-translate", p == DEGREE_TWO_TRANSLATE)


if __name__ == "__main__":
    main()
