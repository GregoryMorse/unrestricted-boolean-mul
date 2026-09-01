from __future__ import annotations

import random

import e1_g_reuse as gr
import e1_pstar_analysis as w
import w_pq_analysis as e


def span(basis, c):
    return e.span_vector(basis, c)


def main(nsamples=3):
    lins = [e.linear_form([i]) for i in range(10)]
    lin_anfs = [e.form_to_anf(x, 1) for x in lins]
    # A matching-capable r0 hard seed: (r0 + b1) * a1.
    g = e.anf_multiply(e.form_to_anf(w.r0, 2) ^ lin_anfs[6], lin_anfs[1])
    quad = w.Mbasis + [w.target_rep(1)]
    low = [1] + lin_anfs + [e.form_to_anf(q, 2) for q in quad]
    prior = low + [g]
    state_target = prior + [e.form_to_anf(t, 2) for t in w.T]
    rng = random.Random(20260831)
    found = 0
    attempts = 0
    while found < nsamples and attempts < 1000:
        attempts += 1
        ac = rng.randrange(1 << len(low))
        cc = rng.randrange(1, 1 << len(low))
        a = span(low, ac)
        c = span(low, cc)
        h = e.anf_multiply(g ^ a, c)
        if e.solve_columns(state_target, h) is not None:
            continue
        print("PROBE", found, "a", ac, "c", cc, "degree", max((m.bit_count() for m in e.iterbits(h)), default=0), flush=True)
        gr.search_seed_general(h, f"h{found}", prior, acquired=(1,), max_examples=8)
        found += 1
    print("attempts", attempts, "found", found)


if __name__ == "__main__":
    main()
