from __future__ import annotations

import numpy as np

import e1_pstar_analysis as w
import w_pq_analysis as e


U64 = np.uint64
NLINEAR = 1 << 10


def split120(x: int) -> tuple[int, int]:
    return x & ((1 << 64) - 1), x >> 64


def qlinear_tables():
    lo = np.zeros((64, NLINEAR), dtype=np.uint64)
    hi = np.zeros((64, NLINEAR), dtype=np.uint64)
    q2 = np.zeros((64, NLINEAR), dtype=np.uint64)
    lins = [e.linear_form([i]) for i in range(10)]
    for qc in range(64):
        Q = e.span_vector(w.Mbasis, qc)
        qa = e.form_to_anf(Q, 2)
        blo = [0] * 10
        bhi = [0] * 10
        bq2 = [0] * 10
        for i, l in enumerate(lins):
            p = e.anf_multiply(qa, e.form_to_anf(l, 1))
            blo[i], bhi[i] = split120(e.anf_degree_part(p, 3))
            bq2[i] = e.anf_degree_part(p, 2)
        for c in range(1, NLINEAR):
            lb = c & -c
            i = lb.bit_length() - 1
            p = c ^ lb
            lo[qc, c] = lo[qc, p] ^ U64(blo[i])
            hi[qc, c] = hi[qc, p] ^ U64(bhi[i])
            q2[qc, c] = q2[qc, p] ^ U64(bq2[i])
    return lo, hi, q2


def linear_products():
    out = np.zeros((NLINEAR, NLINEAR), dtype=np.uint64)
    lins = [e.linear_form([i]) for i in range(10)]
    for lc in range(NLINEAR):
        l = e.span_vector(lins, lc)
        cols = [e.wedge(l, 1, b, 1) for b in lins]
        for mc in range(1, NLINEAR):
            lb = mc & -mc
            i = lb.bit_length() - 1
            out[lc, mc] = out[lc, mc ^ lb] ^ U64(cols[i])
    return out


def reducer_tables():
    encoded = [r | (lab << 45) for r, lab in w.REDUCED_QUAD_BASIS]
    tabs = np.zeros((6, 256), dtype=np.uint64)
    for chunk in range(6):
        for byte in range(256):
            v = 0
            for b in range(8):
                i = 8 * chunk + b
                if byte >> b & 1 and i < 45:
                    v ^= encoded[i]
            tabs[chunk, byte] = U64(v)
    return tabs


def reduce_array(q2, tabs):
    enc = np.zeros(q2.shape, dtype=np.uint64)
    for chunk in range(6):
        enc ^= tabs[chunk][(q2 >> U64(8 * chunk)) & U64(255)]
    return enc & U64((1 << 45) - 1), (enc >> U64(45)).astype(np.uint8)


def zero_planes():
    forms = [e.span_vector(w.Mbasis, c) for c in range(64)]
    seen = set()
    out = []
    for a in range(1, 64):
        for b in range(a + 1, 64):
            key = tuple(sorted((a, b, a ^ b)))
            if key in seen:
                continue
            seen.add(key)
            if not e.wedge(forms[a], 2, forms[b], 2):
                out.append((key[0], key[1]))
    return out


def affine_dims():
    out = np.zeros(1 << 16, dtype=np.uint8)
    for mask in range(1, 1 << 16):
        labels = [q for q in range(16) if mask >> q & 1]
        base = labels[0]
        out[mask] = e.rank([q ^ base for q in labels])
    return out


def main():
    qlo, qhi, q2lin = qlinear_tables()
    lm2 = linear_products()
    tabs = reducer_tables()
    los = []
    his = []
    residues = []
    labels = []
    for qc, cc in zero_planes():
        Q = e.span_vector(w.Mbasis, qc)
        C = e.span_vector(w.Mbasis, cc)
        prod = e.anf_multiply(e.form_to_anf(Q, 2), e.form_to_anf(C, 2))
        b3lo, b3hi = split120(e.anf_degree_part(prod, 3))
        b2 = e.anf_degree_part(prod, 2)
        hlo = U64(b3lo) ^ qlo[cc, :, None] ^ qlo[qc, None, :]
        hhi = U64(b3hi) ^ qhi[cc, :, None] ^ qhi[qc, None, :]
        shadow = U64(b2) ^ q2lin[cc, :, None] ^ q2lin[qc, None, :] ^ lm2
        residue, label = reduce_array(shadow, tabs)
        los.append(hlo.ravel())
        his.append(hhi.ravel())
        residues.append(residue.ravel())
        labels.append(label.ravel())
    lo = np.concatenate(los)
    hi = np.concatenate(his)
    res = np.concatenate(residues)
    lab = np.concatenate(labels)
    keep = (lo != 0) | (hi != 0)
    lo, hi, res, lab = lo[keep], hi[keep], res[keep], lab[keep]
    print("records", len(lo), flush=True)
    order = np.lexsort((res, hi, lo))
    slo, shi, sres, slab = lo[order], hi[order], res[order], lab[order]
    starts = np.empty(len(order), dtype=bool)
    starts[0] = True
    starts[1:] = ((slo[1:] != slo[:-1]) | (shi[1:] != shi[:-1]) |
                  (sres[1:] != sres[:-1]))
    ix = np.flatnonzero(starts)
    masks = np.bitwise_or.reduceat(
        np.left_shift(np.uint16(1), slab.astype(np.uint16)), ix)
    dims = affine_dims()[masks]
    ghlo, ghhi = slo[ix], shi[ix]
    hstarts = np.empty(len(ix), dtype=bool)
    hstarts[0] = True
    hstarts[1:] = (ghlo[1:] != ghlo[:-1]) | (ghhi[1:] != ghhi[:-1])
    hix = np.flatnonzero(hstarts)
    hmax = np.maximum.reduceat(dims, hix)
    adims = affine_dims()
    vals, counts = np.unique(hmax, return_counts=True)
    print("groups", len(ix), "highs", len(hix), "summary",
          list(zip(vals.tolist(), counts.tolist())), "global", int(hmax.max()))
    wi = int(np.argmax(hmax))
    gs = hix[wi]
    ge = hix[wi + 1] if wi + 1 < len(hix) else len(ix)
    mi = gs + int(np.argmax(dims[gs:ge]))
    print("worst labels", [w.qstr(q) for q in range(16) if int(masks[mi]) >> q & 1])

    # Add dependent representations only on the 4,803 cubic highs that
    # overlap an independent local module.
    forms = [e.span_vector(w.Mbasis, c) for c in range(64)]
    lins = [e.linear_form([i]) for i in range(10)]
    independent_highs = {(int(ghlo[i]), int(ghhi[i])) for i in hix}
    dep_reps = []
    for gc in range(1, 64):
        G = forms[gc]
        for nc in range(1, 1 << 10):
            h = e.wedge(e.span_vector(lins, nc), 1, G, 2)
            if not h:
                continue
            keyh = split120(h)
            if keyh in independent_highs:
                dep_reps.append((gc, nc, keyh))
    overlap_highs = {x[2] for x in dep_reps}
    overlap_groups = {}
    for i in range(len(ix)):
        hk = (int(ghlo[i]), int(ghhi[i]))
        if hk in overlap_highs:
            overlap_groups[(hk[0], hk[1], int(sres[ix[i]]))] = int(masks[i])
    print("overlap highs", len(overlap_highs), "dependent reps", len(dep_reps),
          "independent groups", len(overlap_groups), flush=True)
    for ri, (gc, nc, hk) in enumerate(dep_reps, 1):
        G = forms[gc]
        N = e.span_vector(lins, nc)
        base = e.anf_degree_part(
            e.anf_multiply(e.form_to_anf(G, 2), e.form_to_anf(N, 1)), 2)
        shadows = U64(base) ^ lm2[:, nc]
        dr, dl = reduce_array(shadows, tabs)
        for residue0, label0 in zip(dr.tolist(), dl.tolist()):
            key = (hk[0], hk[1], int(residue0))
            if key in overlap_groups:
                overlap_groups[key] |= 1 << int(label0)
        if ri % 1000 == 0:
            print("dependent overlap progress", ri, "/", len(dep_reps), flush=True)
    by_high = {}
    worst_union = None
    for (a, b, _), mask in overlap_groups.items():
        d = int(adims[mask])
        if d > by_high.get((a, b), 0):
            by_high[(a, b)] = d
        if worst_union is None or d > worst_union[0]:
            worst_union = (d, mask, (a, b))
    uv, uc = np.unique(np.array(list(by_high.values()), dtype=np.uint8),
                       return_counts=True)
    print("UNION summary", list(zip(uv.tolist(), uc.tolist())),
          "global", max(by_high.values(), default=0))
    if worst_union:
        print("UNION worst labels",
              [w.qstr(q) for q in range(16) if worst_union[1] >> q & 1])


if __name__ == "__main__":
    main()
