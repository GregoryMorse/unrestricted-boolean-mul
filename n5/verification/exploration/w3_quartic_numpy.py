from __future__ import annotations

from collections import defaultdict

import numpy as np

import w_pq_analysis as e
import w_3p_analysis as w


U64 = np.uint64
NLINEAR = 1 << 10


def split120(x: int) -> tuple[int, int]:
    return x & ((1 << 64) - 1), x >> 64


def precompute_q_linear():
    nquad = 1 << len(w.Wbasis)
    lo = np.zeros((nquad, NLINEAR), dtype=np.uint64)
    hi = np.zeros((nquad, NLINEAR), dtype=np.uint64)
    q2 = np.zeros((nquad, NLINEAR), dtype=np.uint64)
    linear_basis = [e.linear_form([i]) for i in range(10)]
    for qc in range(nquad):
        Q = e.span_vector(w.Wbasis, qc)
        qanf = e.form_to_anf(Q, 2)
        blo = [0] * 10
        bhi = [0] * 10
        bq2 = [0] * 10
        for i, l in enumerate(linear_basis):
            p = e.anf_multiply(qanf, e.form_to_anf(l, 1))
            c3 = e.anf_degree_part(p, 3)
            blo[i], bhi[i] = split120(c3)
            bq2[i] = e.anf_degree_part(p, 2)
        for c in range(1, NLINEAR):
            lb = c & -c
            i = lb.bit_length() - 1
            p = c ^ lb
            lo[qc, c] = lo[qc, p] ^ U64(blo[i])
            hi[qc, c] = hi[qc, p] ^ U64(bhi[i])
            q2[qc, c] = q2[qc, p] ^ U64(bq2[i])
    return lo, hi, q2


def precompute_linear_products():
    out = np.zeros((NLINEAR, NLINEAR), dtype=np.uint64)
    lins = [e.linear_form([i]) for i in range(10)]
    basis_lins = lins
    for lc in range(NLINEAR):
        l = e.span_vector(lins, lc)
        cols = [e.wedge(l, 1, b, 1) for b in basis_lins]
        row = out[lc]
        for mc in range(1, NLINEAR):
            lb = mc & -mc
            i = lb.bit_length() - 1
            row[mc] = row[mc ^ lb] ^ U64(cols[i])
    return out


def reducer_tables():
    encoded_basis = []
    for residue, label in w.REDUCED_QUAD_BASIS:
        encoded_basis.append(residue | (label << 45))
    tabs = np.zeros((6, 256), dtype=np.uint64)
    for chunk in range(6):
        for byte in range(256):
            val = 0
            for b in range(8):
                i = 8 * chunk + b
                if byte >> b & 1 and i < 45:
                    val ^= encoded_basis[i]
            tabs[chunk, byte] = U64(val)
    return tabs


def reduce_array(q2: np.ndarray, tabs: np.ndarray):
    enc = np.zeros(q2.shape, dtype=np.uint64)
    for chunk in range(6):
        enc ^= tabs[chunk][(q2 >> U64(8 * chunk)) & U64(255)]
    residue = enc & U64((1 << 45) - 1)
    label = (enc >> U64(45)).astype(np.uint8)
    return residue, label


def canonical_planes():
    seen = set()
    by_q4 = defaultdict(list)
    anns = {}
    nquad = 1 << len(w.Wbasis)
    for u in range(1, nquad):
        Q = e.span_vector(w.Wbasis, u)
        for v in range(u + 1, nquad):
            key = tuple(sorted((u, v, u ^ v)))
            if key in seen:
                continue
            seen.add(key)
            C = e.span_vector(w.Wbasis, v)
            q4 = e.wedge(Q, 2, C, 2)
            if not q4:
                continue
            d, J = w.projected_annihilator(q4, 4)
            if d:
                by_q4[q4].append((key[0], key[1]))
                anns[q4] = J
    return by_q4, anns


def rank4(vectors):
    return e.rank(list(vectors))


def mask_dimensions(J, mask: int):
    labels = [q for q in range(16) if mask >> q & 1]
    base = labels[0]
    diffs = [q ^ base for q in labels]
    return rank4(diffs), rank4(list(J) + diffs)


def main():
    qlo, qhi, q2lin = precompute_q_linear()
    lm2 = precompute_linear_products()
    tabs = reducer_tables()
    by_q4, anns = canonical_planes()
    filter_ann = getattr(w, "QUARTIC_FILTER_ANN", None)
    items = [(q4, planes) for q4, planes in by_q4.items()
             if filter_ann is None or tuple(sorted(anns[q4])) == filter_ann]
    items.sort(key=lambda item: len(item[1]))
    print("dangerous tops", len(items), "planes", sum(len(p) for _, p in items),
          "of", len(by_q4), sum(map(len, by_q4.values())), flush=True)
    global_match = 0
    global_total = 0
    summary = defaultdict(int)
    worst = None
    lindex = np.arange(NLINEAR, dtype=np.int64)[:, None]
    mindex = np.arange(NLINEAR, dtype=np.int64)[None, :]
    for ti, (q4, planes) in enumerate(items, 1):
        los = []
        his = []
        residues = []
        labels = []
        for qc, cc in planes:
            Q = e.span_vector(w.Wbasis, qc)
            C = e.span_vector(w.Wbasis, cc)
            prod = e.anf_multiply(e.form_to_anf(Q, 2), e.form_to_anf(C, 2))
            qc3 = e.anf_degree_part(prod, 3)
            qc3lo, qc3hi = split120(qc3)
            qc2 = e.anf_degree_part(prod, 2)
            hlo = U64(qc3lo) ^ qlo[cc, :, None] ^ qlo[qc, None, :]
            hhi = U64(qc3hi) ^ qhi[cc, :, None] ^ qhi[qc, None, :]
            shadow = U64(qc2) ^ q2lin[cc, :, None] ^ q2lin[qc, None, :] ^ lm2
            residue, label = reduce_array(shadow, tabs)
            los.append(hlo.ravel())
            his.append(hhi.ravel())
            residues.append(residue.ravel())
            labels.append(label.ravel())
        lo = np.concatenate(los) if len(los) > 1 else los[0]
        hi = np.concatenate(his) if len(his) > 1 else his[0]
        residue = np.concatenate(residues) if len(residues) > 1 else residues[0]
        label = np.concatenate(labels) if len(labels) > 1 else labels[0]
        order = np.lexsort((residue, hi, lo))
        slo = lo[order]
        shi = hi[order]
        sres = residue[order]
        slab = label[order]
        starts = np.empty(len(order), dtype=bool)
        starts[0] = True
        starts[1:] = ((slo[1:] != slo[:-1]) |
                      (shi[1:] != shi[:-1]) |
                      (sres[1:] != sres[:-1]))
        ix = np.flatnonzero(starts)
        bitlabels = np.left_shift(np.uint16(1), slab.astype(np.uint16))
        masks = np.bitwise_or.reduceat(bitlabels, ix)
        J = anns[q4]
        md = 0
        td = 0
        for mask in np.unique(masks):
            a, t = mask_dimensions(J, int(mask))
            if t > td:
                worst = (q4, planes, J, int(mask))
            md = max(md, a)
            td = max(td, t)
        summary[(len(J), md, td, len(planes))] += 1
        global_match = max(global_match, md)
        global_total = max(global_total, td)
        print("progress", ti, "/", len(items), "planes", len(planes),
                  "match", md, "total", td, flush=True)
    print("SUMMARY")
    for key, count in sorted(summary.items()):
        print(count, key)
    print("global", global_match, global_total)
    if worst:
        q4, planes, J, mask = worst
        print("worst", "ann", w.format_qspace(J), "planes", len(planes),
              "labels", [w.qstr(q) for q in range(16) if mask >> q & 1])


if __name__ == "__main__":
    main()
