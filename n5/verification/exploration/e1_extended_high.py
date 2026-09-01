from __future__ import annotations

from collections import Counter

import e1_pstar_analysis as w
import w_pq_analysis as e


HARD_PLANES = [
    (0b0001, 0b0010),  # qstr <1000,0100>
    (0b0101, 0b1110),  # qstr <1010,0111>
    (0b0100, 0b1001),  # qstr <0010,1001>
    (0b0110, 0b1100),  # qstr <0110,0011>
    (0b0001, 0b1111),  # qstr <1000,1111>
    (0b0001, 0b1001),  # qstr <1000,1001>
    (0b0111, 0b1110),  # qstr <1110,0111>
]


def qbasis_mod_J(labels, J):
    full = e.basis(list(J) + list(labels))
    # Return only a dimension; exact quotient representatives are not needed.
    return len(full) - e.rank(list(J))


def ann_dim_mod_J(high, degree, J):
    cols = [e.wedge(w.T[s], 2, high, degree) for s in range(9)]
    ker = e.nullspace_columns(cols)
    labels = []
    for kc in ker:
        tf = e.span_vector(w.T, kc)
        residue, label = w.REDUCE(tf)
        if residue:
            raise AssertionError("bad target reduction")
        labels.append(label)
    return qbasis_mod_J(labels, J)


def analyze_plane(J):
    Xbasis = w.Mbasis + [w.target_rep(q) for q in J]
    forms = [e.span_vector(Xbasis, c) for c in range(1 << len(Xbasis))]
    lins = [e.linear_form([i]) for i in range(10)]

    dep_cache = {}
    dep_counts = Counter()
    dep_examples = []
    for gc in range(1, len(forms)):
        G = forms[gc]
        for nc in range(1, 1 << 10):
            h = e.wedge(e.span_vector(lins, nc), 1, G, 2)
            if not h:
                continue
            if h not in dep_cache:
                dep_cache[h] = ann_dim_mod_J(h, 3, J)
            d = dep_cache[h]
            dep_counts[d] += 1
            if d == 2 and len(dep_examples) < 6:
                dep_examples.append((gc, nc))

    seen = set()
    quart_cache = {}
    quart_counts = Counter()
    quart_examples = []
    zero_planes = []
    for a in range(1, len(forms)):
        Q = forms[a]
        for b in range(a + 1, len(forms)):
            key = tuple(sorted((a, b, a ^ b)))
            if key in seen:
                continue
            seen.add(key)
            C = forms[b]
            q4 = e.wedge(Q, 2, C, 2)
            if not q4:
                zero_planes.append((key[0], key[1]))
                continue
            if q4 not in quart_cache:
                quart_cache[q4] = ann_dim_mod_J(q4, 4, J)
            d = quart_cache[q4]
            quart_counts[d] += 1
            if d == 2 and len(quart_examples) < 6:
                quart_examples.append((key[0], key[1]))

    return {
        "dep_counts": dep_counts,
        "dep_distinct": Counter(dep_cache.values()),
        "dep_examples": dep_examples,
        "quart_counts": quart_counts,
        "quart_distinct": Counter(quart_cache.values()),
        "quart_examples": quart_examples,
        "zero_planes": zero_planes,
    }


def main():
    for i, J in enumerate(HARD_PLANES, 1):
        print("PLANE", i, w.fmtspace(J), flush=True)
        r = analyze_plane(J)
        print(" dep distinct", sorted(r["dep_distinct"].items()),
              "occ", sorted(r["dep_counts"].items()),
              "full examples", r["dep_examples"])
        print(" quart distinct", sorted(r["quart_distinct"].items()),
              "planes", sorted(r["quart_counts"].items()),
              "full examples", r["quart_examples"])
        print(" zero planes", len(r["zero_planes"]), flush=True)


if __name__ == "__main__":
    main()
