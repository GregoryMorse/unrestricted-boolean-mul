from __future__ import annotations

import e1_pstar_analysis as w
import w_pq_analysis as e


ONE = 1
LINEAR_ANFS = [e.form_to_anf(e.linear_form([i]), 1) for i in range(10)]
def target_label_from_coeff(coeff: int, low_count: int) -> int:
    # Combined columns are c*LOW_BASIS followed by LOW_BASIS and T.
    fcoeff = coeff >> low_count
    tcoeff = fcoeff >> low_count
    tf = e.span_vector(w.T, tcoeff)
    residue, label = w.REDUCE(tf)
    if residue:
        raise AssertionError("target coefficient did not reduce")
    return label


def search_g(g: int, name: str, quad_basis=None, acquired=()):
    if quad_basis is None:
        quad_basis = w.Mbasis
    low_basis = [ONE] + LINEAR_ANFS + [e.form_to_anf(q, 2) for q in quad_basis]
    state_target_basis = low_basis + [e.form_to_anf(t, 2) for t in w.T]
    acquired_elems = {e.span_vector(list(acquired), c)
                      for c in range(1 << len(acquired))}
    n = len(low_basis)
    table = [[e.anf_multiply(low_basis[i], low_basis[j])
              for j in range(n)] for i in range(n)]
    gprod = [e.anf_multiply(g, b) for b in low_basis]
    current_cols = [0] * n
    current_gc = 0
    gray_prev = 0
    useful = []
    solvable = 0
    for step in range(1, 1 << n):
        gray = step ^ (step >> 1)
        diff = gray ^ gray_prev
        i = diff.bit_length() - 1
        for j in range(n):
            current_cols[j] ^= table[i][j]
        current_gc ^= gprod[i]
        gray_prev = gray

        sol = e.solve_columns(current_cols + state_target_basis, current_gc)
        if sol is None:
            continue
        solvable += 1
        particular, kb = sol
        base_label = target_label_from_coeff(particular, n)
        dirs = e.basis([target_label_from_coeff(k, n) for k in kb])
        labels = {base_label ^ e.span_vector(dirs, c) for c in range(1 << len(dirs))}
        labels.difference_update(acquired_elems)
        if labels:
            useful.append((gray, tuple(sorted(labels)), len(kb)))
            print("USEFUL", name, "c", gray, "labels", [w.qstr(q) for q in sorted(labels)],
                  "kernel", len(kb), flush=True)
            if len(useful) >= 20:
                break
        if step % 16384 == 0:
            print("progress", name, step, "solvable", solvable, flush=True)
    print("RESULT", name, "solvable", solvable, "useful", len(useful))
    return useful


def search_seed_general(seed: int, name: str, prior_basis, acquired=(),
                        max_examples: int = 20):
    """Useful one-gate extensions of prior state after adjoining seed."""
    n = len(prior_basis)
    acquired_elems = {e.span_vector(list(acquired), c)
                      for c in range(1 << len(acquired))}
    target_basis = [e.form_to_anf(t, 2) for t in w.T]
    state_target_basis = list(prior_basis) + target_basis
    table = [[e.anf_multiply(prior_basis[i], prior_basis[j])
              for j in range(n)] for i in range(n)]
    sprod = [e.anf_multiply(seed, b) for b in prior_basis]
    current_cols = [0] * n
    current_sc = 0
    gray_prev = 0
    examples = []
    all_labels = set()

    def label_of(coeff):
        fcoeff = coeff >> n
        tcoeff = fcoeff >> n
        tf = e.span_vector(w.T, tcoeff)
        residue, label = w.REDUCE(tf)
        if residue:
            raise AssertionError("bad target label")
        return label

    for step in range(1, 1 << n):
        gray = step ^ (step >> 1)
        diff = gray ^ gray_prev
        i = diff.bit_length() - 1
        for j in range(n):
            current_cols[j] ^= table[i][j]
        current_sc ^= sprod[i]
        gray_prev = gray
        sol = e.solve_columns(current_cols + state_target_basis, current_sc)
        if sol is None:
            continue
        particular, kb = sol
        base = label_of(particular)
        dirs = e.basis([label_of(k) for k in kb])
        labels = {base ^ e.span_vector(dirs, c) for c in range(1 << len(dirs))}
        labels.difference_update(acquired_elems)
        if labels:
            all_labels.update(labels)
            if len(examples) < max_examples:
                examples.append((gray, tuple(sorted(labels)), len(kb)))
                print("NESTED USEFUL", name, gray,
                      [w.qstr(q) for q in sorted(labels)], "kernel", len(kb), flush=True)
    print("NESTED RESULT", name, "examples", len(examples),
          "labels", [w.qstr(q) for q in sorted(all_labels)],
          "span", e.rank(list(all_labels)))
    return examples, all_labels


def canonical_hard_g(place: str):
    if place == "r0":
        G = w.r0
        N = LINEAR_ANFS[1]
    elif place == "r1":
        G = w.r1
        N = LINEAR_ANFS[1] ^ LINEAR_ANFS[3]
    elif place == "rinf":
        G = w.rinf
        N = LINEAR_ANFS[3]
    else:
        raise ValueError(place)
    return e.anf_multiply(e.form_to_anf(G, 2), N)


if __name__ == "__main__":
    search_g(canonical_hard_g("r0"), "r0")
