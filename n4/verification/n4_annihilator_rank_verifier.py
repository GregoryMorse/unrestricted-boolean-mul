#!/usr/bin/env python3
"""
Exact GF(2) verifier for the n=4 exterior-algebra annihilator lemma.

This file is intentionally self-contained.  It verifies, but is not intended
to replace, the coordinate proof.

Basis of L:
    a0,a1,a2,a3,b0,b1,b2,b3.

Target:
    E_s = sum_{i+j=s} a_i ^ b_j, 0 <= s <= 6.

Rational-place adapted basis:
    X0=A(0)=a0,
    X1=A(1)=a0+a1+a2+a3,
    X2=A(infty)=a3,
    X*=a1,
and analogously Y0,Y1,Y2,Y*.

Then r_i = X_i ^ Y_i for i=0,1,2.

For G of rational-place weight 1,2,3 and M in L, verify
    Ann_T(M ^ G) = ker[t -> M ^ G ^ t]
and the claimed rank classifications.

Exterior multiplication is over F_2: monomials are bitsets and there are
no signs.  In particular every positive-degree exterior element squares
to zero in characteristic two; the Pfaffian quadratic form is NOT the
ordinary wedge square.
"""

from itertools import combinations

def xor_forms(*fs):
    out = {}
    for f in fs:
        for m, c in f.items():
            if c:
                out[m] = out.get(m, 0) ^ 1
    return {m: c for m, c in out.items() if c}

def wedge(f, g):
    out = {}
    for m, c in f.items():
        if not c:
            continue
        for n, d in g.items():
            if not d or (m & n):
                continue
            z = m | n
            out[z] = out.get(z, 0) ^ 1
    return {m: c for m, c in out.items() if c}

def bv(i):
    return {1 << i: 1}

a = [bv(i) for i in range(4)]
b = [bv(4+i) for i in range(4)]
A1 = xor_forms(*a)
B1 = xor_forms(*b)

X = [a[0], A1, a[3], a[1]]
Y = [b[0], B1, b[3], b[1]]
r = [wedge(X[i], Y[i]) for i in range(3)]

E = []
for s in range(7):
    E.append(xor_forms(*[
        wedge(a[i], b[s-i])
        for i in range(4) if 0 <= s-i < 4
    ]))

basis5 = [sum(1 << i for i in I) for I in combinations(range(8), 5)]
idx5 = {m:i for i,m in enumerate(basis5)}

def form_bits(f):
    z = 0
    for m in f:
        z ^= 1 << idx5[m]
    return z

def rank(cols):
    B = {}
    for v in cols:
        y = v
        while y:
            p = y.bit_length()-1
            if p in B:
                y ^= B[p]
            else:
                B[p] = y
                break
    return len(B)

def kernel_basis(cols):
    B = {}
    ker = []
    for j, v in enumerate(cols):
        y, c = v, 1 << j
        while y:
            p = y.bit_length()-1
            if p in B:
                y ^= B[p][0]
                c ^= B[p][1]
            else:
                B[p] = (y, c)
                break
        if not y:
            ker.append(c)
    return tuple(ker)

def span(B):
    S = {0}
    for v in B:
        S |= {x ^ v for x in tuple(S)}
    return S

def lin_from_adapted(mask, side):
    basis = X if side == "A" else Y
    return xor_forms(*[basis[i] for i in range(4) if (mask >> i) & 1])

def M_from_masks(xmask, ymask):
    return xor_forms(lin_from_adapted(xmask, "A"),
                     lin_from_adapted(ymask, "B"))

def phi_cols(M, G):
    h = wedge(M, G)
    return [form_bits(wedge(h, t)) for t in E]

def ann_basis(xmask, ymask, G):
    return kernel_basis(phi_cols(M_from_masks(xmask, ymask), G))

def dim_ann(xmask, ymask, G):
    return 7 - rank(phi_cols(M_from_masks(xmask, ymask), G))

def P(theta):
    # Nonzero M in P_theta have x,y masks in {0,e_theta}, not both zero.
    e = 1 << theta
    return {(x,y) for x in (0,e) for y in (0,e) if x or y}

def expr(mask):
    terms = [f"E{s}" for s in range(7) if (mask >> s) & 1]
    return "+".join(terms) if terms else "0"

G1 = r[0]
G2 = xor_forms(r[0], r[1])
G3 = xor_forms(r[0], r[1], r[2])

# Characteristic-two square check.
assert wedge(G3, G3) == {}

# Full exact classifications.
# Weight 1: for h != 0, dim Ann <= 3.
for x in range(16):
    for y in range(16):
        h = wedge(M_from_masks(x,y), G1)
        if h:
            assert dim_ann(x,y,G1) <= 3

# Weight 2: dim Ann = 3 iff M is in one constituent rational plane.
eq3_w2 = set()
for x in range(16):
    for y in range(16):
        h = wedge(M_from_masks(x,y), G2)
        if not h:
            continue
        d = dim_ann(x,y,G2)
        assert d <= 3
        if d == 3:
            eq3_w2.add((x,y))
assert eq3_w2 == P(0) | P(1)

# Weight 3: dim Ann = 2 iff M lies in one rational plane; otherwise 1.
eq2_w3, eq1_w3 = set(), set()
for x in range(16):
    for y in range(16):
        h = wedge(M_from_masks(x,y), G3)
        if not h:
            continue
        d = dim_ann(x,y,G3)
        assert d in (1,2)
        (eq2_w3 if d == 2 else eq1_w3).add((x,y))
assert eq2_w3 == P(0) | P(1) | P(2)

# One-sided kernel tables in adapted A-coordinates. These are the small
# coordinate row reductions used in the proof.
def one_sided_kernel(xmask, G):
    x = lin_from_adapted(xmask, "A")
    return kernel_basis([form_bits(wedge(wedge(x,G),t)) for t in E])

def group_one_sided(G):
    groups = {}
    for x in range(16):
        K = one_sided_kernel(x,G)
        # canonicalize by its span, so basis-choice variations do not split groups
        key = tuple(sorted(span(K)))
        groups.setdefault(key, []).append(x)
    return groups

print("G3 wedge G3 = 0: PASS")
print("weight 1: nonzero h => dim Ann_T(h) <= 3: PASS")
print("weight 2: dim Ann_T(h)=3 iff M in P0 union P1: PASS")
print("weight 3: dim Ann_T(h)=2 iff M in P0 union P1 union Pinf, else 1: PASS")
print()
for wt, G in [(1,G1),(2,G2),(3,G3)]:
    print(f"ONE-SIDED KERNEL GROUPS, weight {wt}")
    groups = group_one_sided(G)
    for key, xs in groups.items():
        # recover a compact basis of the subspace from all elements
        nonzero = [v for v in key if v]
        # eliminate to canonical basis
        B = {}
        for v in nonzero:
            y=v
            while y:
                p=y.bit_length()-1
                if p in B: y ^= B[p]
                else: B[p]=y; break
        kb = [B[p] for p in sorted(B, reverse=True)]
        print("  x =", ",".join(f"{x:04b}" for x in xs),
              " dim=", len(kb),
              " kernel=", " ; ".join(expr(v) for v in kb))
    print()
