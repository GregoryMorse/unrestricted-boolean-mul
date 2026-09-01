from __future__ import annotations

import itertools
from collections import Counter, defaultdict


N = 10
COMBS = {
    d: [sum(1 << i for i in c) for c in itertools.combinations(range(N), d)]
    for d in range(N + 1)
}
INDEX = {d: {m: i for i, m in enumerate(COMBS[d])} for d in COMBS}


def iterbits(x: int):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b


def wedge(x: int, dx: int, y: int, dy: int) -> int:
    out = 0
    ix = COMBS[dx]
    iy = COMBS[dy]
    oi = INDEX[dx + dy]
    for i in iterbits(x):
        a = ix[i]
        for j in iterbits(y):
            b = iy[j]
            if not (a & b):
                out ^= 1 << oi[a | b]
    return out


def linear_form(indices: list[int]) -> int:
    return sum(1 << INDEX[1][1 << i] for i in indices)


def decomposable_2(x: int, y: int) -> int:
    return wedge(x, 1, y, 1)


def span_vector(basis: list[int], coeff: int) -> int:
    out = 0
    for i, b in enumerate(basis):
        if coeff >> i & 1:
            out ^= b
    return out


def rank(vectors: list[int]) -> int:
    pivots: dict[int, int] = {}
    for v in vectors:
        while v:
            p = v.bit_length() - 1
            if p in pivots:
                v ^= pivots[p]
            else:
                pivots[p] = v
                break
    return len(pivots)


def basis(vectors: list[int]) -> list[int]:
    pivots: dict[int, int] = {}
    for v in vectors:
        while v:
            p = v.bit_length() - 1
            if p in pivots:
                v ^= pivots[p]
            else:
                pivots[p] = v
                break
    return list(pivots.values())


def nullspace_columns(columns: list[int]) -> list[int]:
    """Kernel basis for coeff -> xor of selected arbitrary-width columns."""
    pivots: dict[int, tuple[int, int]] = {}
    kernels: list[int] = []
    for i, col in enumerate(columns):
        coeff = 1 << i
        while col:
            p = col.bit_length() - 1
            if p in pivots:
                old_col, old_coeff = pivots[p]
                col ^= old_col
                coeff ^= old_coeff
            else:
                pivots[p] = (col, coeff)
                break
        if not col:
            kernels.append(coeff)
    return basis(kernels)


def solve_columns(columns: list[int], target: int) -> tuple[int, list[int]] | None:
    """One coefficient solution and a kernel basis, or None."""
    pivots: dict[int, tuple[int, int]] = {}
    kernels: list[int] = []
    for i, col0 in enumerate(columns):
        col = col0
        coeff = 1 << i
        while col:
            p = col.bit_length() - 1
            if p in pivots:
                old_col, old_coeff = pivots[p]
                col ^= old_col
                coeff ^= old_coeff
            else:
                pivots[p] = (col, coeff)
                break
        if not col:
            kernels.append(coeff)
    coeff = 0
    while target:
        p = target.bit_length() - 1
        if p not in pivots:
            return None
        old_col, old_coeff = pivots[p]
        target ^= old_col
        coeff ^= old_coeff
    return coeff, basis(kernels)


def quotient_T_mod_S(tcoeff: int) -> int:
    # Quotient basis E2,E3,E4,E5.  Since sum(E0,...,E8) is in S,
    # E6 = E2+E3+E4+E5 modulo S; E0,E1,E7,E8 vanish.
    q6 = tcoeff >> 6 & 1
    out = 0
    for outbit, s in enumerate((2, 3, 4, 5)):
        if ((tcoeff >> s) & 1) ^ q6:
            out |= 1 << outbit
    return out


def form_to_anf(form: int, degree: int) -> int:
    out = 0
    for i in iterbits(form):
        out ^= 1 << COMBS[degree][i]
    return out


def anf_degree_part(poly: int, degree: int) -> int:
    out = 0
    for monomial in iterbits(poly):
        if monomial.bit_count() == degree:
            out ^= 1 << INDEX[degree][monomial]
    return out


def anf_multiply(f: int, g: int) -> int:
    out = 0
    for xmon in iterbits(f):
        for ymon in iterbits(g):
            out ^= 1 << (xmon | ymon)
    return out


def dependent_quadratic_shadow(G: int, ell: int, nlin: int) -> int:
    f = form_to_anf(G, 2) ^ form_to_anf(ell, 1)
    g = form_to_anf(nlin, 1)
    return anf_degree_part(anf_multiply(f, g), 2)


def labelled_reducer(generators: list[tuple[int, int]]):
    """Return reduce(v)=(residue,label), preserving quotient labels."""
    pivots: dict[int, tuple[int, int]] = {}
    for vec, label in generators:
        while vec:
            p = vec.bit_length() - 1
            if p in pivots:
                old_vec, old_label = pivots[p]
                vec ^= old_vec
                label ^= old_label
            else:
                pivots[p] = (vec, label)
                break

    def reduce(vec: int) -> tuple[int, int]:
        label = 0
        while vec:
            p = vec.bit_length() - 1
            if p not in pivots:
                # Skip a non-pivot coordinate while retaining it in residue.
                lower = vec & ((1 << p) - 1)
                residue_top = 1 << p
                sub_residue, sub_label = reduce(lower)
                return residue_top ^ sub_residue, label ^ sub_label
            old_vec, old_label = pivots[p]
            vec ^= old_vec
            label ^= old_label
        return 0, label

    # The recursive routine above cannot continue reduction below a free bit
    # after returning it.  Use an explicit descending pass instead.
    def reduce_full(vec: int) -> tuple[int, int]:
        label = 0
        residue = 0
        for p in range(len(COMBS[2]) - 1, -1, -1):
            if not (vec >> p & 1):
                continue
            if p in pivots:
                old_vec, old_label = pivots[p]
                vec ^= old_vec
                label ^= old_label
            else:
                residue ^= 1 << p
                vec ^= 1 << p
        return residue, label

    return reduce_full


def projected_annihilator(high: int, dhigh: int) -> tuple[int, tuple[int, ...]]:
    cols = [wedge(T[s], 2, high, dhigh) for s in range(9)]
    ker = nullspace_columns(cols)
    qb = tuple(sorted(basis([quotient_T_mod_S(k) for k in ker])))
    return len(qb), qb


# Original coefficient variables a0,...,a4,b0,...,b4.
A = [linear_form([i]) for i in range(5)]
B = [linear_form([5 + i]) for i in range(5)]


def outer(x: int, y: int) -> int:
    return decomposable_2(x, y)


# Exact Hermite decomposition 2P0 + 2Pinf + P1.
x, xp = A[0], A[1]
y, yp = A[4], A[3]
z = A[0] ^ A[1] ^ A[2] ^ A[3] ^ A[4]
X, Xp = B[0], B[1]
Y, Yp = B[4], B[3]
Z = B[0] ^ B[1] ^ B[2] ^ B[3] ^ B[4]

r0 = outer(x, X)
j0 = outer(x, Xp) ^ outer(xp, X)
d0 = outer(xp, Xp)
rinf = outer(y, Y)
jinf = outer(y, Yp) ^ outer(yp, Y)
dinf = outer(yp, Yp)
r1 = outer(z, Z)

Wbasis = [r0, j0, d0, rinf, jinf, dinf, r1]
Wnames = ["r0", "j0", "d0", "rinf", "jinf", "dinf", "r1"]

T = []
for s in range(9):
    q = 0
    for i in range(5):
        j = s - i
        if 0 <= j < 5:
            q ^= outer(A[i], B[j])
    T.append(q)


REDUCE_WT = labelled_reducer(
    [(w, 0) for w in Wbasis]
    + [(T[s], quotient_T_mod_S(1 << s)) for s in range(9)]
)

REDUCED_QUAD_BASIS = [REDUCE_WT(1 << i) for i in range(len(COMBS[2]))]


def reduce_quadratic_fast(q: int) -> tuple[int, int]:
    residue = 0
    label = 0
    for i in iterbits(q):
        r, l = REDUCED_QUAD_BASIS[i]
        residue ^= r
        label ^= l
    return residue, label


def format_qspace(qb: tuple[int, ...]) -> str:
    return "<" + ",".join(f"{q:04b}" for q in qb) + ">"


def dependent_scan():
    counts = Counter()
    examples: dict[tuple[int, tuple[int, ...]], tuple[int, int]] = {}
    by_G_max: dict[int, tuple[int, set[tuple[int, ...]]]] = {}
    for gc in range(1, 1 << len(Wbasis)):
        G = span_vector(Wbasis, gc)
        md = -1
        spaces: set[tuple[int, ...]] = set()
        for nc in range(1, 1 << N):
            Nform = span_vector([linear_form([i]) for i in range(N)], nc)
            h = wedge(Nform, 1, G, 2)
            if not h:
                continue
            d, qb = projected_annihilator(h, 3)
            counts[d] += 1
            examples.setdefault((d, qb), (gc, nc))
            if d > md:
                md, spaces = d, {qb}
            elif d == md:
                spaces.add(qb)
        by_G_max[gc] = (md, spaces)
    print("DEPENDENT projected annihilator counts", sorted(counts.items()))
    print("DEPENDENT global maximum", max(counts))
    for gc, (md, spaces) in by_G_max.items():
        if md >= 2:
            print(" G", "+".join(Wnames[i] for i in range(7) if gc >> i & 1),
                  "max", md, "spaces", [format_qspace(x) for x in sorted(spaces)])


def quartic_scan():
    data: dict[int, dict[str, object]] = {}
    for qc in range(1, 1 << len(Wbasis)):
        Q = span_vector(Wbasis, qc)
        for cc in range(qc + 1, 1 << len(Wbasis)):
            C = span_vector(Wbasis, cc)
            q4 = wedge(Q, 2, C, 2)
            if not q4:
                continue
            d, qb = projected_annihilator(q4, 4)
            rec = data.setdefault(q4, {"d": d, "qb": qb, "pairs": []})
            rec["pairs"].append((qc, cc))
    cnt = Counter(rec["d"] for rec in data.values())
    print("QUARTIC distinct tops by projected annihilator dimension", sorted(cnt.items()))
    print("QUARTIC global maximum", max(cnt))
    for q4, rec in data.items():
        if rec["d"] >= 2:
            qc, cc = rec["pairs"][0]
            print(" q4 reps", "+".join(Wnames[i] for i in range(7) if qc >> i & 1), "/",
                  "+".join(Wnames[i] for i in range(7) if cc >> i & 1),
                  "ann", format_qspace(rec["qb"]), "repcount", len(rec["pairs"]))


def hard_r1_matching_scan():
    lins = [linear_form([i]) for i in range(N)]
    n0c = (1 << 1) | (1 << 3)
    n0 = span_vector(lins, n0c)
    high = wedge(n0, 1, r1, 2)
    reps: list[tuple[int, int, int]] = []
    for nc in range(1, 1 << N):
        nlin = span_vector(lins, nc)
        if wedge(nlin, 1, r1, 2) != high:
            continue
        for ec in range(1 << N):
            ell = span_vector(lins, ec)
            shadow = dependent_quadratic_shadow(r1, ell, nlin)
            residue, qlabel = REDUCE_WT(shadow)
            reps.append((residue, qlabel, nc))
    groups: dict[int, set[int]] = defaultdict(set)
    group_n: dict[int, set[int]] = defaultdict(set)
    for residue, qlabel, nc in reps:
        groups[residue].add(qlabel)
        group_n[residue].add(nc)
    print("HARD r1 reps", len(reps), "matching residue groups", len(groups))
    spans = Counter()
    for residue, labels in groups.items():
        if len(labels) <= 1:
            spans[0] += 1
            continue
        base = next(iter(labels))
        diffs = [x ^ base for x in labels]
        spans[rank(diffs)] += 1
    print("HARD r1 matching affine dimensions", sorted(spans.items()))
    J = [0b0110, 0b1010]
    total = Counter()
    for labels in groups.values():
        base = next(iter(labels))
        diffs = [x ^ base for x in labels]
        total[rank(J + diffs)] += 1
    print("HARD r1 total span with annihilator", sorted(total.items()))
    for residue, labels in groups.items():
        base = next(iter(labels))
        diffs = basis([x ^ base for x in labels])
        if rank(J + diffs) == max(total):
            print(" hard extremal group labels", [f"{x:04b}" for x in sorted(labels)],
                  "diffbasis", [f"{x:04b}" for x in diffs],
                  "Nclasses", sorted(group_n[residue]))
            break


def independent_annihilator_scan():
    lins = [linear_form([i]) for i in range(N)]
    planes = []
    for sector, j, r, d in (("0", j0, r0, d0), ("inf", jinf, rinf, dinf)):
        for name, g in (("r", r), ("d", d), ("r+d", r ^ d)):
            planes.append((sector + ":" + name, j, g))
    high_to_planes: dict[int, set[str]] = defaultdict(set)
    counts = Counter()
    maxima = []
    for name, Q, C in planes:
        cols = [wedge(l, 1, C, 2) for l in lins] + [wedge(l, 1, Q, 2) for l in lins]
        ib = basis(cols)
        local_max = -1
        local_spaces: set[tuple[int, ...]] = set()
        for coeff in range(1, 1 << len(ib)):
            h = span_vector(ib, coeff)
            high_to_planes[h].add(name)
            dproj, qb = projected_annihilator(h, 3)
            counts[dproj] += 1
            if dproj > local_max:
                local_max, local_spaces = dproj, {qb}
            elif dproj == local_max:
                local_spaces.add(qb)
        maxima.append((name, len(ib), local_max, local_spaces))
    print("INDEPENDENT cubic ann counts", sorted(counts.items()))
    for name, dim, md, spaces in maxima:
        print(" independent plane", name, "module-dim", dim, "max-ann", md,
              [format_qspace(s) for s in sorted(spaces)])
    overlaps = Counter(len(v) for v in high_to_planes.values())
    print("INDEPENDENT high plane-overlap multiplicities", sorted(overlaps.items()))
    for h, ps in high_to_planes.items():
        if len(ps) > 1:
            dproj, qb = projected_annihilator(h, 3)
            print(" overlap", sorted(ps), "ann", dproj, format_qspace(qb))
            break


def quartic_matching_scan():
    # Canonical coefficient-space two-planes in W.
    planes: dict[tuple[int, int, int], tuple[int, int, int]] = {}
    for u in range(1, 1 << 7):
        for v in range(u + 1, 1 << 7):
            if u == v:
                continue
            key = tuple(sorted((u, v, u ^ v)))
            if key in planes:
                continue
            a, b = key[:2]
            Q = span_vector(Wbasis, a)
            C = span_vector(Wbasis, b)
            q4 = wedge(Q, 2, C, 2)
            if q4:
                planes[key] = (a, b, q4)

    by_q4: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for a, b, q4 in planes.values():
        by_q4[q4].append((a, b))

    exceptional = []
    for q4, pcs in by_q4.items():
        dproj, qb = projected_annihilator(q4, 4)
        if dproj == 2:
            exceptional.append((q4, qb, pcs))

    lin_forms = [span_vector([linear_form([i]) for i in range(N)], c) for c in range(1 << N)]
    lin_anfs = [form_to_anf(l, 1) for l in lin_forms]
    # The bilinear degree-two piece is shared by every factor plane.
    lm2 = [[0] * (1 << N) for _ in range(1 << N)]
    for lc, l in enumerate(lin_forms):
        for mc, m in enumerate(lin_forms):
            lm2[lc][mc] = wedge(l, 1, m, 1)

    for q4, qb, pcs in exceptional:
        groups: dict[tuple[int, int], int] = {}
        for a, b in pcs:
            Q = span_vector(Wbasis, a)
            C = span_vector(Wbasis, b)
            qanf = form_to_anf(Q, 2)
            canf = form_to_anf(C, 2)
            qc = anf_multiply(qanf, canf)
            qc3 = anf_degree_part(qc, 3)
            qc2 = anf_degree_part(qc, 2)
            q3 = [0] * (1 << N)
            q2 = [0] * (1 << N)
            c3 = [0] * (1 << N)
            c2 = [0] * (1 << N)
            for lc, lanf in enumerate(lin_anfs):
                qp = anf_multiply(qanf, lanf)
                cp = anf_multiply(canf, lanf)
                q3[lc] = anf_degree_part(qp, 3)
                q2[lc] = anf_degree_part(qp, 2)
                c3[lc] = anf_degree_part(cp, 3)
                c2[lc] = anf_degree_part(cp, 2)
            for lc in range(1 << N):
                # ell multiplies C, while m multiplies Q.
                base_h = qc3 ^ c3[lc]
                base_q2 = qc2 ^ c2[lc]
                lmrow = lm2[lc]
                for mc in range(1 << N):
                    h = base_h ^ q3[mc]
                    shadow = base_q2 ^ q2[mc] ^ lmrow[mc]
                    residue, qlabel = reduce_quadratic_fast(shadow)
                    key = (h, residue)
                    groups[key] = groups.get(key, 0) | (1 << qlabel)

        max_aff = 0
        max_total = 0
        aff_count = Counter()
        total_count = Counter()
        worst = None
        for key, labelset in groups.items():
            labels = list(iterbits(labelset))
            base = labels[0]
            diffs = [x ^ base for x in labels]
            ad = rank(diffs)
            td = rank(list(qb) + diffs)
            aff_count[ad] += 1
            total_count[td] += 1
            if td > max_total:
                max_total = td
                worst = (key, labels, basis(diffs))
            max_aff = max(max_aff, ad)
        a, b = pcs[0]
        print("QUARTIC MATCH top", "+".join(Wnames[i] for i in range(7) if a >> i & 1), "/",
              "+".join(Wnames[i] for i in range(7) if b >> i & 1),
              "ann", format_qspace(qb), "planes", len(pcs),
              "groups", len(groups), "aff", sorted(aff_count.items()),
              "total", sorted(total_count.items()), "max", max_total)
        if worst:
            print(" worst labels", [f"{x:04b}" for x in worst[1]],
                  "diffbasis", [f"{x:04b}" for x in worst[2]])


def quotient_subspaces(maxdim: int = 3):
    seen: dict[tuple[int, ...], tuple[int, ...]] = {}
    nonzero = range(1, 16)
    for d in range(maxdim + 1):
        if d == 0:
            seen[(0,)] = ()
            continue
        for gens in itertools.combinations(nonzero, d):
            if rank(list(gens)) != d:
                continue
            elems = tuple(sorted(span_vector(list(gens), c) for c in range(1 << d)))
            seen.setdefault(elems, tuple(basis(list(gens))))
    return sorted(((len(elems).bit_length() - 1, elems, gens) for elems, gens in seen.items()),
                  key=lambda x: (x[0], x[1]))


def target_rep(q: int) -> int:
    return span_vector([T[2], T[3], T[4], T[5]], q)


def independent_zero_high_scan():
    lins = [linear_form([i]) for i in range(N)]
    summary = Counter()
    counterexamples = []
    details = []
    for jdim, jelems, jgens in quotient_subspaces(3):
        Xbasis = Wbasis + [target_rep(q) for q in jgens]
        xdim = len(Xbasis)
        forms = [span_vector(Xbasis, c) for c in range(1 << xdim)]
        seen_planes = set()
        zero_planes = []
        for u in range(1, 1 << xdim):
            Q = forms[u]
            for v in range(u + 1, 1 << xdim):
                key = tuple(sorted((u, v, u ^ v)))
                if key in seen_planes:
                    continue
                seen_planes.add(key)
                C = forms[v]
                if not wedge(Q, 2, C, 2):
                    zero_planes.append((key[0], key[1]))
        proj_patterns = Counter()
        new_outputs = set()
        max_kernel = 0
        for u, v in zero_planes:
            Q, C = forms[u], forms[v]
            uq = span_vector(list(jgens), u >> 7) if jgens else 0
            vq = span_vector(list(jgens), v >> 7) if jgens else 0
            proj_patterns[rank([uq, vq])] += 1

            qanf = form_to_anf(Q, 2)
            canf = form_to_anf(C, 2)
            qc = anf_multiply(qanf, canf)
            rhs = anf_degree_part(qc, 3)
            cols = []
            c2parts = []
            q2parts = []
            for l, lanf in zip(lins, [form_to_anf(x, 1) for x in lins]):
                cp = anf_multiply(canf, lanf)
                qp = anf_multiply(qanf, lanf)
                cols.append(anf_degree_part(cp, 3))
                c2parts.append(anf_degree_part(cp, 2))
                q2parts.append(anf_degree_part(qp, 2))
            cols += [anf_degree_part(anf_multiply(qanf, form_to_anf(l, 1)), 3) for l in lins]
            sol = solve_columns(cols, rhs)
            if sol is None:
                continue
            particular, kb = sol
            max_kernel = max(max_kernel, len(kb))
            if len(kb) > 16:
                # This should not occur for an independent plane; retain as a guard.
                raise RuntimeError((jdim, jgens, u, v, len(kb)))
            for kc in range(1 << len(kb)):
                lmcoeff = particular ^ span_vector(kb, kc)
                lc = lmcoeff & ((1 << N) - 1)
                mc = lmcoeff >> N
                ell = span_vector(lins, lc)
                mlin = span_vector(lins, mc)
                prod = anf_multiply(qanf ^ form_to_anf(ell, 1),
                                    canf ^ form_to_anf(mlin, 1))
                if any(anf_degree_part(prod, d) for d in range(3, 5)):
                    raise AssertionError("bad cubic solve")
                shadow = anf_degree_part(prod, 2)
                residue, qlabel = reduce_quadratic_fast(shadow)
                if residue == 0 and qlabel not in jelems:
                    new_outputs.add(qlabel)
                    if len(counterexamples) < 20:
                        counterexamples.append((jdim, jgens, u, v, qlabel, lc, mc))
        summary[(jdim, len(zero_planes), tuple(sorted(proj_patterns.items())), max_kernel,
                 bool(new_outputs))] += 1
        if new_outputs:
            details.append((jdim, jgens, tuple(sorted(new_outputs))))
    print("INDEPENDENT ZERO-HIGH summary")
    for key, count in sorted(summary.items()):
        print(" ", count, key)
    print("INDEPENDENT ZERO-HIGH bad J", details)
    print("INDEPENDENT ZERO-HIGH examples", counterexamples[:5])


def dependent_zero_high_scan():
    lins = [linear_form([i]) for i in range(N)]
    lin_anfs = [form_to_anf(l, 1) for l in lins]
    summary = Counter()
    bad = []
    for jdim, jelems, jgens in quotient_subspaces(3):
        Xbasis = Wbasis + [target_rep(q) for q in jgens]
        bad_outputs = set()
        kernel_counts = Counter()
        for gc in range(1, 1 << len(Xbasis)):
            G = span_vector(Xbasis, gc)
            ganf = form_to_anf(G, 2)
            cubic_cols = [anf_degree_part(anf_multiply(ganf, la), 3) for la in lin_anfs]
            kb = nullspace_columns(cubic_cols)
            kernel_counts[len(kb)] += 1
            if not kb:
                continue
            for mc0 in range(1, 1 << len(kb)):
                mc = span_vector(kb, mc0)
                mlin = span_vector(lins, mc)
                manf = form_to_anf(mlin, 1)
                for lc, ell in enumerate(span_vector(lins, x) for x in range(1 << N)):
                    prod = anf_multiply(ganf ^ form_to_anf(ell, 1), manf)
                    if anf_degree_part(prod, 3):
                        raise AssertionError("dependent kernel failure")
                    shadow = anf_degree_part(prod, 2)
                    residue, qlabel = reduce_quadratic_fast(shadow)
                    if residue == 0 and qlabel not in jelems:
                        bad_outputs.add(qlabel)
                        if len(bad) < 20:
                            bad.append((jdim, jgens, gc, mc, lc, qlabel))
        summary[(jdim, tuple(sorted(kernel_counts.items())), bool(bad_outputs))] += 1
    print("DEPENDENT ZERO-HIGH summary")
    for key, count in sorted(summary.items()):
        print(" ", count, key)
    print("DEPENDENT ZERO-HIGH bad", bad[:10])


if __name__ == "__main__":
    print("dim wedge kernel W", 21 - rank([
        wedge(Wbasis[i], 2, Wbasis[j], 2)
        for i in range(7) for j in range(i + 1, 7)
    ]))
    dependent_scan()
    quartic_scan()
    hard_r1_matching_scan()
    independent_annihilator_scan()
    quartic_matching_scan()
    independent_zero_high_scan()
    dependent_zero_high_scan()
