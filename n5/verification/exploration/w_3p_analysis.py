from __future__ import annotations

import itertools
from collections import Counter, defaultdict

import w_pq_analysis as e


A = e.A
B = e.B
T = e.T
N = e.N

x0, x1, x2 = A[0], A[1], A[2]
z = A[0] ^ A[1] ^ A[2] ^ A[3] ^ A[4]
y = A[4]
X0, X1, X2 = B[0], B[1], B[2]
Z = B[0] ^ B[1] ^ B[2] ^ B[3] ^ B[4]
Y = B[4]

r0 = e.outer(x0, X0)
j0 = e.outer(x0, X1) ^ e.outer(x1, X0)
k0 = e.outer(x0, X2) ^ e.outer(x1, X1) ^ e.outer(x2, X0)
u1 = e.outer(x1, X1)
u2 = e.outer(x2, X2)
r1 = e.outer(z, Z)
rinf = e.outer(y, Y)

Wbasis = [r0, j0, k0, u1, u2, r1, rinf]
Wnames = ["r0", "j0", "k0", "u1", "u2", "r1", "rinf"]


def quotient_T_mod_S(tcoeff: int) -> int:
    # Quotient basis E3,E4,E5,E6. E0,E1,E2,E8 vanish and
    # E7 = E3+E4+E5+E6 because r1=sum_s E_s lies in S.
    q7 = tcoeff >> 7 & 1
    out = 0
    for bit, s in enumerate((3, 4, 5, 6)):
        if ((tcoeff >> s) & 1) ^ q7:
            out |= 1 << bit
    return out


def qstr(q: int) -> str:
    return "".join(str(q >> i & 1) for i in range(4))


def format_qspace(qb: tuple[int, ...]) -> str:
    return "<" + ",".join(qstr(q) for q in qb) + ">"


def target_rep(q: int) -> int:
    return e.span_vector([T[3], T[4], T[5], T[6]], q)


def projected_annihilator(high: int, dhigh: int) -> tuple[int, tuple[int, ...]]:
    cols = [e.wedge(T[s], 2, high, dhigh) for s in range(9)]
    ker = e.nullspace_columns(cols)
    qb = tuple(sorted(e.basis([quotient_T_mod_S(k) for k in ker])))
    return len(qb), qb


REDUCE_WT = e.labelled_reducer(
    [(w, 0) for w in Wbasis]
    + [(T[s], quotient_T_mod_S(1 << s)) for s in range(9)]
)
REDUCED_QUAD_BASIS = [REDUCE_WT(1 << i) for i in range(len(e.COMBS[2]))]


def reduce_quadratic_fast(q: int) -> tuple[int, int]:
    residue = 0
    label = 0
    for i in e.iterbits(q):
        r, l = REDUCED_QUAD_BASIS[i]
        residue ^= r
        label ^= l
    return residue, label


def quotient_subspaces(maxdim: int = 3):
    seen = {}
    for d in range(maxdim + 1):
        if d == 0:
            seen[(0,)] = ()
            continue
        for gens in itertools.combinations(range(1, 16), d):
            if e.rank(list(gens)) != d:
                continue
            elems = tuple(sorted(e.span_vector(list(gens), c) for c in range(1 << d)))
            seen.setdefault(elems, tuple(e.basis(list(gens))))
    return sorted(((len(es).bit_length() - 1, es, gs) for es, gs in seen.items()),
                  key=lambda x: (x[0], x[1]))


def dependent_scan():
    lins = [e.linear_form([i]) for i in range(N)]
    counts = Counter()
    by_G = {}
    hard_examples = {}
    for gc in range(1, 128):
        G = e.span_vector(Wbasis, gc)
        md = -1
        spaces = set()
        for nc in range(1, 1 << N):
            nlin = e.span_vector(lins, nc)
            h = e.wedge(nlin, 1, G, 2)
            if not h:
                continue
            d, qb = projected_annihilator(h, 3)
            counts[d] += 1
            hard_examples.setdefault((d, qb), (gc, nc, h))
            if d > md:
                md, spaces = d, {qb}
            elif d == md:
                spaces.add(qb)
        by_G[gc] = (md, spaces)
    print("DEPENDENT counts", sorted(counts.items()), "global max", max(counts))
    for gc, (md, spaces) in by_G.items():
        if md >= 2:
            print(" G", "+".join(Wnames[i] for i in range(7) if gc >> i & 1),
                  "max", md, [format_qspace(s) for s in sorted(spaces)])
    for (d, qb), (gc, nc, h) in hard_examples.items():
        if d == max(counts):
            print(" hard example", "+".join(Wnames[i] for i in range(7) if gc >> i & 1),
                  [i for i in range(10) if nc >> i & 1], format_qspace(qb))
            break


def quartic_scan():
    data = {}
    for qc in range(1, 128):
        Q = e.span_vector(Wbasis, qc)
        for cc in range(qc + 1, 128):
            C = e.span_vector(Wbasis, cc)
            q4 = e.wedge(Q, 2, C, 2)
            if not q4:
                continue
            d, qb = projected_annihilator(q4, 4)
            rec = data.setdefault(q4, {"d": d, "qb": qb, "pairs": []})
            rec["pairs"].append((qc, cc))
    counts = Counter(rec["d"] for rec in data.values())
    print("QUARTIC tops", sorted(counts.items()), "global max", max(counts))
    for rec in data.values():
        if rec["d"] >= 2:
            qc, cc = rec["pairs"][0]
            print(" q4", "+".join(Wnames[i] for i in range(7) if qc >> i & 1), "/",
                  "+".join(Wnames[i] for i in range(7) if cc >> i & 1),
                  "ann", format_qspace(rec["qb"]), "pairs", len(rec["pairs"]))


def independent_planes_scan():
    # Canonical independent zero-wedge planes in the seven-dimensional base.
    planes = {}
    for u in range(1, 128):
        Q = e.span_vector(Wbasis, u)
        for v in range(u + 1, 128):
            key = tuple(sorted((u, v, u ^ v)))
            if key in planes:
                continue
            C = e.span_vector(Wbasis, v)
            if not e.wedge(Q, 2, C, 2):
                planes[key] = (key[0], key[1])
    print("INDEPENDENT zero-wedge planes", len(planes))
    lins = [e.linear_form([i]) for i in range(N)]
    counts = Counter()
    maxima = []
    high_to_planes = defaultdict(set)
    for key, (u, v) in planes.items():
        Q = e.span_vector(Wbasis, u)
        C = e.span_vector(Wbasis, v)
        cols = [e.wedge(l, 1, C, 2) for l in lins] + [e.wedge(l, 1, Q, 2) for l in lins]
        ib = e.basis(cols)
        md = -1
        spaces = set()
        for coeff in range(1, 1 << len(ib)):
            h = e.span_vector(ib, coeff)
            high_to_planes[h].add(key)
            d, qb = projected_annihilator(h, 3)
            counts[d] += 1
            if d > md:
                md, spaces = d, {qb}
            elif d == md:
                spaces.add(qb)
        maxima.append((key, len(ib), md, spaces))
    print("INDEPENDENT ann counts", sorted(counts.items()))
    for key, dim, md, spaces in maxima:
        if md >= 1:
            print(" plane", ["+".join(Wnames[i] for i in range(7) if c >> i & 1) for c in key[:2]],
                  "module", dim, "max", md, [format_qspace(s) for s in sorted(spaces)])
    print("INDEPENDENT overlap", sorted(Counter(len(v) for v in high_to_planes.values()).items()))


def dependent_matching_scan():
    lins = [e.linear_form([i]) for i in range(N)]
    by_high = defaultdict(list)
    ann = {}
    for gc in range(1, 128):
        G = e.span_vector(Wbasis, gc)
        for nc in range(1, 1 << N):
            nlin = e.span_vector(lins, nc)
            h = e.wedge(nlin, 1, G, 2)
            if not h:
                continue
            if h not in ann:
                ann[h] = projected_annihilator(h, 3)
            if ann[h][0] >= 1:
                by_high[h].append((gc, nc))
    print("DEPENDENT MATCH nonzero-ann highs", len(by_high),
          "representations", sum(map(len, by_high.values())))
    global_max = 0
    summary = Counter()
    worst = None
    for h, pairs in by_high.items():
        groups = defaultdict(set)
        for gc, nc in pairs:
            G = e.span_vector(Wbasis, gc)
            nlin = e.span_vector(lins, nc)
            for lc in range(1 << N):
                ell = e.span_vector(lins, lc)
                shadow = e.dependent_quadratic_shadow(G, ell, nlin)
                residue, qlabel = reduce_quadratic_fast(shadow)
                groups[residue].add(qlabel)
        J = list(ann[h][1])
        hmax = 0
        hamax = 0
        for labels in groups.values():
            base = next(iter(labels))
            diffs = [x ^ base for x in labels]
            ad = e.rank(diffs)
            td = e.rank(J + diffs)
            hamax = max(hamax, ad)
            hmax = max(hmax, td)
            if td > global_max:
                global_max = td
                worst = (h, pairs, ann[h], labels, e.basis(diffs))
        summary[(ann[h][0], hamax, hmax, len(pairs))] += 1
    print("DEPENDENT MATCH summary (ann,match,total,reps)")
    for key, count in sorted(summary.items()):
        print(" ", count, key)
    print("DEPENDENT MATCH global total", global_max)
    if worst:
        h, pairs, ah, labels, db = worst
        print(" worst ann", format_qspace(ah[1]),
              "first rep", "+".join(Wnames[i] for i in range(7) if pairs[0][0] >> i & 1),
              [i for i in range(10) if pairs[0][1] >> i & 1],
              "labels", [qstr(x) for x in sorted(labels)],
              "diffbasis", [qstr(x) for x in db])


def independent_matching_scan():
    lins = [e.linear_form([i]) for i in range(N)]
    lin_anfs = [e.form_to_anf(l, 1) for l in lins]

    planes = {}
    for u in range(1, 128):
        Q = e.span_vector(Wbasis, u)
        for v in range(u + 1, 128):
            key = tuple(sorted((u, v, u ^ v)))
            if key in planes:
                continue
            C = e.span_vector(Wbasis, v)
            if not e.wedge(Q, 2, C, 2):
                planes[key] = (key[0], key[1])

    special = set()
    plane_data = []
    for key, (u, v) in planes.items():
        Q = e.span_vector(Wbasis, u)
        C = e.span_vector(Wbasis, v)
        qanf = e.form_to_anf(Q, 2)
        canf = e.form_to_anf(C, 2)
        qc = e.anf_multiply(qanf, canf)
        qc3 = e.anf_degree_part(qc, 3)
        cols = []
        for la in lin_anfs:
            cols.append(e.anf_degree_part(e.anf_multiply(canf, la), 3))
        for la in lin_anfs:
            cols.append(e.anf_degree_part(e.anf_multiply(qanf, la), 3))
        ib = e.basis(cols)
        for coeff in range(1 << len(ib)):
            h = qc3 ^ e.span_vector(ib, coeff)
            if h and projected_annihilator(h, 3)[0] >= 1:
                special.add(h)
        plane_data.append((key, Q, C, qanf, canf, qc, cols))

    groups = {h: defaultdict(set) for h in special}
    # Independent representations.
    for key, Q, C, qanf, canf, qc, cols in plane_data:
        qc3 = e.anf_degree_part(qc, 3)
        for h in special:
            sol = e.solve_columns(cols, h ^ qc3)
            if sol is None:
                continue
            particular, kb = sol
            for kc in range(1 << len(kb)):
                lm = particular ^ e.span_vector(kb, kc)
                lc = lm & ((1 << N) - 1)
                mc = lm >> N
                ell = e.span_vector(lins, lc)
                mlin = e.span_vector(lins, mc)
                prod = e.anf_multiply(qanf ^ e.form_to_anf(ell, 1),
                                     canf ^ e.form_to_anf(mlin, 1))
                if e.anf_degree_part(prod, 3) != h or e.anf_degree_part(prod, 4):
                    raise AssertionError("independent high mismatch")
                shadow = e.anf_degree_part(prod, 2)
                residue, qlabel = reduce_quadratic_fast(shadow)
                groups[h][residue].add(qlabel)

    # Dependent overlaps with the same cubic high.
    for gc in range(1, 128):
        G = e.span_vector(Wbasis, gc)
        for nc in range(1, 1 << N):
            nlin = e.span_vector(lins, nc)
            h = e.wedge(nlin, 1, G, 2)
            if h not in special:
                continue
            for lc in range(1 << N):
                ell = e.span_vector(lins, lc)
                shadow = e.dependent_quadratic_shadow(G, ell, nlin)
                residue, qlabel = reduce_quadratic_fast(shadow)
                groups[h][residue].add(qlabel)

    summary = Counter()
    global_max = 0
    worst = None
    for h, rgs in groups.items():
        J = list(projected_annihilator(h, 3)[1])
        hamax = 0
        htmax = 0
        for labels in rgs.values():
            base = next(iter(labels))
            diffs = [x ^ base for x in labels]
            ad = e.rank(diffs)
            td = e.rank(J + diffs)
            hamax = max(hamax, ad)
            htmax = max(htmax, td)
            if td > global_max:
                global_max = td
                worst = (h, J, labels, e.basis(diffs))
        summary[(len(J), hamax, htmax)] += 1
    print("INDEPENDENT MATCH special highs", len(special))
    print("INDEPENDENT MATCH summary (ann,match,total)", sorted(summary.items()))
    print("INDEPENDENT MATCH global total", global_max)
    if worst:
        print(" worst", format_qspace(tuple(worst[1])),
              [qstr(x) for x in sorted(worst[2])], [qstr(x) for x in worst[3]])


def target_line_zero_wedge_scan():
    """Classify new zero-wedge planes after one target direction is adjoined."""
    for q in range(1, 16):
        xb = Wbasis + [target_rep(q)]
        forms = [e.span_vector(xb, c) for c in range(1 << 8)]
        planes = set()
        patterns = Counter()
        examples = []
        for u in range(1, 1 << 8):
            for v in range(u + 1, 1 << 8):
                key = tuple(sorted((u, v, u ^ v)))
                if key in planes:
                    continue
                planes.add(key)
                if not e.wedge(forms[u], 2, forms[v], 2):
                    pr = e.rank([u >> 7, v >> 7])
                    patterns[pr] += 1
                    if pr and len(examples) < 4:
                        examples.append((u, v))
        print("TARGET LINE", qstr(q), "patterns", sorted(patterns.items()),
              "new", examples)


def independent_zero_high_scan():
    lins = [e.linear_form([i]) for i in range(N)]
    lin_anfs = [e.form_to_anf(x, 1) for x in lins]
    summary = Counter()
    counterexamples = []
    details = []
    for ji, (jdim, jelems, jgens) in enumerate(quotient_subspaces(3), 1):
        Xbasis = Wbasis + [target_rep(q) for q in jgens]
        xdim = len(Xbasis)
        forms = [e.span_vector(Xbasis, c) for c in range(1 << xdim)]
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
                if not e.wedge(Q, 2, C, 2):
                    zero_planes.append((key[0], key[1]))
        proj_patterns = Counter()
        new_outputs = set()
        max_kernel = 0
        for u, v in zero_planes:
            Q, C = forms[u], forms[v]
            uq = e.span_vector(list(jgens), u >> 7) if jgens else 0
            vq = e.span_vector(list(jgens), v >> 7) if jgens else 0
            proj_patterns[e.rank([uq, vq])] += 1

            qanf = e.form_to_anf(Q, 2)
            canf = e.form_to_anf(C, 2)
            qc = e.anf_multiply(qanf, canf)
            rhs = e.anf_degree_part(qc, 3)
            cols = []
            for la in lin_anfs:
                cols.append(e.anf_degree_part(e.anf_multiply(canf, la), 3))
            for la in lin_anfs:
                cols.append(e.anf_degree_part(e.anf_multiply(qanf, la), 3))
            sol = e.solve_columns(cols, rhs)
            if sol is None:
                continue
            particular, kb = sol
            max_kernel = max(max_kernel, len(kb))
            if len(kb) > 16:
                raise RuntimeError((jdim, jgens, u, v, len(kb)))
            for kc in range(1 << len(kb)):
                lmcoeff = particular ^ e.span_vector(kb, kc)
                lc = lmcoeff & ((1 << N) - 1)
                mc = lmcoeff >> N
                ell = e.span_vector(lins, lc)
                mlin = e.span_vector(lins, mc)
                prod = e.anf_multiply(qanf ^ e.form_to_anf(ell, 1),
                                      canf ^ e.form_to_anf(mlin, 1))
                if any(e.anf_degree_part(prod, d) for d in range(3, 5)):
                    raise AssertionError("bad cubic solve")
                shadow = e.anf_degree_part(prod, 2)
                residue, qlabel = reduce_quadratic_fast(shadow)
                if residue == 0 and qlabel not in jelems:
                    new_outputs.add(qlabel)
                    if len(counterexamples) < 20:
                        counterexamples.append((jdim, jgens, u, v, qlabel, lc, mc))
        summary[(jdim, len(zero_planes), tuple(sorted(proj_patterns.items())), max_kernel,
                 bool(new_outputs))] += 1
        if new_outputs:
            details.append((jdim, jgens, tuple(sorted(new_outputs))))
        print("INDEPENDENT ZERO-HIGH progress", ji, "/ 66", jdim,
              format_qspace(tuple(jgens)), "planes", len(zero_planes),
              "proj", sorted(proj_patterns.items()), "bad", sorted(new_outputs), flush=True)
    print("INDEPENDENT ZERO-HIGH summary")
    for key, count in sorted(summary.items()):
        print(" ", count, key)
    print("INDEPENDENT ZERO-HIGH bad J", details)
    print("INDEPENDENT ZERO-HIGH examples", counterexamples[:5])


def dependent_zero_high_scan():
    lins = [e.linear_form([i]) for i in range(N)]
    lin_anfs = [e.form_to_anf(l, 1) for l in lins]
    summary = Counter()
    bad = []
    for ji, (jdim, jelems, jgens) in enumerate(quotient_subspaces(3), 1):
        Xbasis = Wbasis + [target_rep(q) for q in jgens]
        bad_outputs = set()
        kernel_counts = Counter()
        for gc in range(1, 1 << len(Xbasis)):
            G = e.span_vector(Xbasis, gc)
            ganf = e.form_to_anf(G, 2)
            cubic_cols = [e.anf_degree_part(e.anf_multiply(ganf, la), 3)
                          for la in lin_anfs]
            kb = e.nullspace_columns(cubic_cols)
            kernel_counts[len(kb)] += 1
            if not kb:
                continue
            for mc0 in range(1, 1 << len(kb)):
                mc = e.span_vector(kb, mc0)
                mlin = e.span_vector(lins, mc)
                manf = e.form_to_anf(mlin, 1)
                for lc in range(1 << N):
                    ell = e.span_vector(lins, lc)
                    prod = e.anf_multiply(ganf ^ e.form_to_anf(ell, 1), manf)
                    if e.anf_degree_part(prod, 3):
                        raise AssertionError("dependent kernel failure")
                    shadow = e.anf_degree_part(prod, 2)
                    residue, qlabel = reduce_quadratic_fast(shadow)
                    if residue == 0 and qlabel not in jelems:
                        bad_outputs.add(qlabel)
                        if len(bad) < 20:
                            bad.append((jdim, jgens, gc, mc, lc, qlabel))
        summary[(jdim, tuple(sorted(kernel_counts.items())), bool(bad_outputs))] += 1
        print("DEPENDENT ZERO-HIGH progress", ji, "/ 66", jdim,
              format_qspace(tuple(jgens)), "kernels", sorted(kernel_counts.items()),
              "bad", sorted(bad_outputs), flush=True)
    print("DEPENDENT ZERO-HIGH summary")
    for key, count in sorted(summary.items()):
        print(" ", count, key)
    print("DEPENDENT ZERO-HIGH bad", bad[:10])


if __name__ == "__main__":
    images = [e.wedge(Wbasis[i], 2, Wbasis[j], 2) for i in range(7) for j in range(i + 1, 7)]
    print("wedge kernel dim", 21 - e.rank(images))
    dependent_scan()
    quartic_scan()
    independent_planes_scan()
    dependent_matching_scan()
    independent_matching_scan()
