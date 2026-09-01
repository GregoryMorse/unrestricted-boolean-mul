from __future__ import annotations

import itertools
from collections import Counter, defaultdict

import w_pq_analysis as e


N = e.N
A = e.A
B = e.B
T = e.T

u = A[0] ^ A[2] ^ A[3]
v = A[1] ^ A[2] ^ A[4]
p0 = A[0]
p1 = A[0] ^ A[1] ^ A[2] ^ A[3] ^ A[4]
pinf = A[4]
U = B[0] ^ B[2] ^ B[3]
V = B[1] ^ B[2] ^ B[4]
q0 = B[0]
q1 = B[0] ^ B[1] ^ B[2] ^ B[3] ^ B[4]
qinf = B[4]

x00 = e.outer(u, U)
x01 = e.outer(u, V)
x10 = e.outer(v, U)
x11 = e.outer(v, V)
xsum = x00 ^ x01 ^ x10 ^ x11
r0 = e.outer(p0, q0)
r1 = e.outer(p1, q1)
rinf = e.outer(pinf, qinf)

# Standard three-point P_* fiber / Karatsuba plane.
Mbasis = [x00, x11, xsum, r0, r1, rinf]
Mnames = ["x00", "x11", "xsum", "r0", "r1", "rinf"]
Sbasis = [r0, r1, rinf, x00 ^ x11, x00 ^ xsum]


def cross_matrix(f: int) -> list[list[int]]:
    return [[(f >> e.INDEX[2][(1 << i) | (1 << (5 + j))]) & 1
             for j in range(5)] for i in range(5)]


def cross_rank(f: int) -> int:
    return e.rank([sum(a << j for j, a in enumerate(row))
                   for row in cross_matrix(f)])


def quotient_reducer():
    labelled = e.labelled_reducer(
        [(s, 0) for s in Sbasis]
        + [(T[i], 1 << (i - 1)) for i in range(1, 5)]
    )
    return labelled


REDUCE = quotient_reducer()
REDUCE_MT = e.labelled_reducer(
    [(m, 0) for m in Mbasis]
    + [(T[i], REDUCE(T[i])[1]) for i in range(9)]
)
REDUCED_QUAD_BASIS = [REDUCE_MT(1 << i) for i in range(len(e.COMBS[2]))]


def reduce_quadratic_fast(q: int) -> tuple[int, int]:
    residue = 0
    label = 0
    for i in e.iterbits(q):
        r, l = REDUCED_QUAD_BASIS[i]
        residue ^= r
        label ^= l
    return residue, label


def target_rep(q: int) -> int:
    return e.span_vector([T[1], T[2], T[3], T[4]], q)


def qstr(q: int) -> str:
    return "".join(str(q >> i & 1) for i in range(4))


def target_rank_table():
    low = []
    for q in range(1, 16):
        vals = [(cross_rank(target_rep(q) ^ e.span_vector(Mbasis, c)), c)
                for c in range(64)]
        mr = min(r for r, _ in vals)
        witnesses = [c for r, c in vals if r == mr]
        if mr <= 2:
            low.append(q)
        print(qstr(q), mr,
              ["".join(str(c >> i & 1) for i in range(6)) for c in witnesses])
    print("LOW", [qstr(q) for q in low])


def wedge_kernel():
    cols = [e.wedge(Mbasis[i], 2, Mbasis[j], 2)
            for i in range(6) for j in range(i + 1, 6)]
    kb = e.nullspace_columns(cols)
    pairs = [(i, j) for i in range(6) for j in range(i + 1, 6)]
    print("WEDGE KERNEL", len(kb))
    for k in kb:
        print(" + ".join(f"{Mnames[i]}^{Mnames[j]}"
                         for z, (i, j) in enumerate(pairs) if k >> z & 1))

    planes = {}
    forms = [e.span_vector(Mbasis, c) for c in range(64)]
    for a in range(1, 64):
        for b in range(a + 1, 64):
            key = tuple(sorted((a, b, a ^ b)))
            if key in planes:
                continue
            if not e.wedge(forms[a], 2, forms[b], 2):
                planes[key] = (a, b)
    print("ZERO PLANES", len(planes))
    for a, b in planes.values():
        print(" ", "+".join(Mnames[i] for i in range(6) if a >> i & 1), "/",
              "+".join(Mnames[i] for i in range(6) if b >> i & 1))


def target_line_extensions():
    for q in range(1, 16):
        xb = Mbasis + [target_rep(q)]
        forms = [e.span_vector(xb, c) for c in range(128)]
        seen = set()
        pats = Counter()
        examples = []
        for a in range(1, 128):
            for b in range(a + 1, 128):
                key = tuple(sorted((a, b, a ^ b)))
                if key in seen:
                    continue
                seen.add(key)
                if not e.wedge(forms[a], 2, forms[b], 2):
                    pr = e.rank([a >> 6, b >> 6])
                    pats[pr] += 1
                    if pr and len(examples) < 8:
                        examples.append((a, b))
        print("LINE", qstr(q), sorted(pats.items()), examples)


def projected_annihilator(high: int, dhigh: int) -> tuple[int, tuple[int, ...]]:
    cols = [e.wedge(T[s], 2, high, dhigh) for s in range(9)]
    ker = e.nullspace_columns(cols)
    labels = []
    for kc in ker:
        tf = e.span_vector(T, kc)
        residue, label = REDUCE(tf)
        if residue:
            raise AssertionError("target did not reduce through S plus quotient basis")
        labels.append(label)
    qb = tuple(sorted(e.basis(labels)))
    return len(qb), qb


def fmtspace(qb: tuple[int, ...]) -> str:
    return "<" + ",".join(qstr(q) for q in qb) + ">"


def high_annihilator_scans():
    lins = [e.linear_form([i]) for i in range(N)]
    dep = Counter()
    dep_hard = defaultdict(set)
    for gc in range(1, 64):
        G = e.span_vector(Mbasis, gc)
        for nc in range(1, 1 << N):
            h = e.wedge(e.span_vector(lins, nc), 1, G, 2)
            if not h:
                continue
            d, J = projected_annihilator(h, 3)
            dep[d] += 1
            if d >= 2:
                dep_hard[gc].add(J)
    print("DEPENDENT ANN", sorted(dep.items()), "max", max(dep))
    for gc, spaces in dep_hard.items():
        print(" DEP HARD", "+".join(Mnames[i] for i in range(6) if gc >> i & 1),
              [fmtspace(x) for x in sorted(spaces)])

    forms = [e.span_vector(Mbasis, c) for c in range(64)]
    seen = set()
    planes = []
    for a in range(1, 64):
        for b in range(a + 1, 64):
            key = tuple(sorted((a, b, a ^ b)))
            if key in seen:
                continue
            seen.add(key)
            if not e.wedge(forms[a], 2, forms[b], 2):
                planes.append((key, key[0], key[1]))
    ind = Counter()
    ind_hard = defaultdict(set)
    for key, a, b in planes:
        Q, C = forms[a], forms[b]
        cols = [e.wedge(l, 1, C, 2) for l in lins]
        cols += [e.wedge(l, 1, Q, 2) for l in lins]
        ib = e.basis(cols)
        for coeff in range(1, 1 << len(ib)):
            h = e.span_vector(ib, coeff)
            d, J = projected_annihilator(h, 3)
            ind[d] += 1
            if d >= 1:
                ind_hard[key].add(J)
    print("INDEPENDENT ANN", sorted(ind.items()), "max", max(ind))
    for key, spaces in ind_hard.items():
        print(" IND NONZERO", ["+".join(Mnames[i] for i in range(6) if c >> i & 1)
                               for c in key[:2]], [fmtspace(x) for x in sorted(spaces)])

    tops = {}
    for a in range(1, 64):
        for b in range(a + 1, 64):
            q4 = e.wedge(forms[a], 2, forms[b], 2)
            if not q4:
                continue
            d, J = projected_annihilator(q4, 4)
            rec = tops.setdefault(q4, {"d": d, "J": J, "pairs": []})
            rec["pairs"].append((a, b))
    qc = Counter(x["d"] for x in tops.values())
    print("QUARTIC ANN", sorted(qc.items()), "max", max(qc), "tops", len(tops))
    for rec in tops.values():
        if rec["d"] >= 2:
            a, b = rec["pairs"][0]
            print(" Q HARD", "+".join(Mnames[i] for i in range(6) if a >> i & 1), "/",
                  "+".join(Mnames[i] for i in range(6) if b >> i & 1),
                  fmtspace(rec["J"]), "pairs", len(rec["pairs"]))


def dependent_matching_scan():
    lins = [e.linear_form([i]) for i in range(N)]
    by_high = defaultdict(list)
    ann = {}
    for gc in range(1, 64):
        G = e.span_vector(Mbasis, gc)
        for nc in range(1, 1 << N):
            nlin = e.span_vector(lins, nc)
            h = e.wedge(nlin, 1, G, 2)
            if not h:
                continue
            if h not in ann:
                ann[h] = projected_annihilator(h, 3)
            if ann[h][0]:
                by_high[h].append((gc, nc))
    summary = Counter()
    global_total = 0
    for hi, (h, pairs) in enumerate(by_high.items(), 1):
        groups = defaultdict(set)
        for gc, nc in pairs:
            G = e.span_vector(Mbasis, gc)
            nlin = e.span_vector(lins, nc)
            for lc in range(1 << N):
                ell = e.span_vector(lins, lc)
                shadow = e.dependent_quadratic_shadow(G, ell, nlin)
                residue, label = reduce_quadratic_fast(shadow)
                groups[residue].add(label)
        J = list(ann[h][1])
        md = td = 0
        for labels in groups.values():
            base = next(iter(labels))
            diffs = [x ^ base for x in labels]
            md = max(md, e.rank(diffs))
            td = max(td, e.rank(J + diffs))
        summary[(len(J), md, td, len(pairs))] += 1
        global_total = max(global_total, td)
        if hi % 100 == 0:
            print("DEP MATCH progress", hi, "/", len(by_high), flush=True)
    print("DEP MATCH highs", len(by_high), "summary")
    for key, n in sorted(summary.items()):
        print(" ", n, key)
    print("DEP MATCH global", global_total)


def independent_matching_all_scan():
    lins = [e.linear_form([i]) for i in range(N)]
    lanfs = [e.form_to_anf(l, 1) for l in lins]
    forms = [e.span_vector(Mbasis, c) for c in range(64)]
    seen = set()
    planes = []
    for a in range(1, 64):
        for b in range(a + 1, 64):
            key = tuple(sorted((a, b, a ^ b)))
            if key in seen:
                continue
            seen.add(key)
            if not e.wedge(forms[a], 2, forms[b], 2):
                planes.append((key, key[0], key[1]))
    groups = defaultdict(lambda: defaultdict(set))
    highs = set()
    for key, a, b in planes:
        Q, C = forms[a], forms[b]
        qanf, canf = e.form_to_anf(Q, 2), e.form_to_anf(C, 2)
        qc = e.anf_multiply(qanf, canf)
        q3 = e.anf_degree_part(qc, 3)
        cols = [e.anf_degree_part(e.anf_multiply(canf, la), 3) for la in lanfs]
        cols += [e.anf_degree_part(e.anf_multiply(qanf, la), 3) for la in lanfs]
        ib = e.basis(cols)
        for coeff in range(1, 1 << len(ib)):
            highs.add(q3 ^ e.span_vector(ib, coeff))
        for lc in range(1 << N):
            ellanf = lanfs[0] if False else e.form_to_anf(e.span_vector(lins, lc), 1)
            for mc in range(1 << N):
                manf = e.form_to_anf(e.span_vector(lins, mc), 1)
                prod = e.anf_multiply(qanf ^ ellanf, canf ^ manf)
                h = e.anf_degree_part(prod, 3)
                if not h:
                    continue
                shadow = e.anf_degree_part(prod, 2)
                residue, label = reduce_quadratic_fast(shadow)
                groups[h][residue].add(label)
    # Add dependent overlaps only for highs admitting an independent representation.
    for gc in range(1, 64):
        G = e.span_vector(Mbasis, gc)
        for nc in range(1, 1 << N):
            nlin = e.span_vector(lins, nc)
            h = e.wedge(nlin, 1, G, 2)
            if h not in groups:
                continue
            for lc in range(1 << N):
                ell = e.span_vector(lins, lc)
                shadow = e.dependent_quadratic_shadow(G, ell, nlin)
                residue, label = reduce_quadratic_fast(shadow)
                groups[h][residue].add(label)
    summary = Counter()
    gm = 0
    for h, rgs in groups.items():
        md = 0
        for labels in rgs.values():
            base = next(iter(labels))
            md = max(md, e.rank([x ^ base for x in labels]))
        summary[md] += 1
        gm = max(gm, md)
    print("IND MATCH all", len(groups), "summary", sorted(summary.items()), "global", gm)


if __name__ == "__main__":
    print("dims", e.rank(Mbasis), e.rank(Sbasis))
    target_rank_table()
    wedge_kernel()
    target_line_extensions()
    high_annihilator_scans()
