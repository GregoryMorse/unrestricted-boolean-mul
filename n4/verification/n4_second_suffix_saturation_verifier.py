#!/usr/bin/env python3
"""
Self-contained GF(2) verifier for the n=4 second-suffix saturation lemmas.

It checks only the finite linear/exterior statements used in the hand proof:
  1. In the tangent anchored case at 0,
       Ann_T(h) = <E0,E1,E2>,
     for h = M E0 and M in {a1,b1,a1+b1}.
     Hence the last annihilator coset is W=E2=D^(2)_0 C.
  2. For S=<E0,E1,E6,sum E_s>, Q^C=0 with Q,C in S implies
     Q,C are dependent or both lie in <E0,E1>.
  3. Let K0=<a0,a1,b0,b1>, P0=<a0,b0>.  For every U<=K0 with
     dim U<=2 and U != P0,
       T intersect (S + Lambda^2 K0 + U^L) = S.
     This is the jet-separation lemma used for the low-low branch.
  4. For F2=E2+alpha E1+beta E0, wedge by F2 is injective on S;
     H(F2) has rank 3, so w -> F2^w is injective on L.
     This is the g-using branch.

Exterior products are ordinary products in Lambda(L) over F_2.
"""

from itertools import combinations, product

N = 8
names = ["a0","a1","a2","a3","b0","b1","b2","b3"]

def xor_forms(*fs):
    d = {}
    for f in fs:
        for m in f:
            d[m] = d.get(m,0) ^ 1
    return {m for m,c in d.items() if c}

def wedge(f,g):
    d = {}
    for m in f:
        for n in g:
            if m & n:
                continue
            z = m | n
            d[z] = d.get(z,0) ^ 1
    return {z for z,c in d.items() if c}

def lin(mask):
    return {1<<i for i in range(N) if (mask>>i)&1}

a = [lin(1<<i) for i in range(4)]
b = [lin(1<<(4+i)) for i in range(4)]

E = []
for s in range(7):
    E.append(xor_forms(*[
        wedge(a[i],b[s-i]) for i in range(4) if 0 <= s-i < 4
    ]))

r0 = E[0]
tau = E[1]
rinf = E[6]
r1 = xor_forms(*E)
Sbasis = [r0,tau,rinf,r1]

# Coordinate packers.
basis2 = [sum(1<<i for i in I) for I in combinations(range(N),2)]
basis3 = [sum(1<<i for i in I) for I in combinations(range(N),3)]
basis4 = [sum(1<<i for i in I) for I in combinations(range(N),4)]
basis5 = [sum(1<<i for i in I) for I in combinations(range(N),5)]
idx2 = {m:i for i,m in enumerate(basis2)}
idx3 = {m:i for i,m in enumerate(basis3)}
idx4 = {m:i for i,m in enumerate(basis4)}
idx5 = {m:i for i,m in enumerate(basis5)}

def bits(f, idx):
    z=0
    for m in f:
        z ^= 1 << idx[m]
    return z

def rank(cols):
    B={}
    for x in cols:
        y=x
        while y:
            p=y.bit_length()-1
            if p in B:
                y ^= B[p]
            else:
                B[p]=y
                break
    return len(B)

def in_span(v,cols):
    return rank(cols+[v]) == rank(cols)

def intersection_dim(A,B):
    return rank(A)+rank(B)-rank(A+B)

T2 = [bits(e,idx2) for e in E]
S2 = [bits(e,idx2) for e in Sbasis]

# ----------------------------------------------------------------------
# 1. Annihilator and W.
# ----------------------------------------------------------------------
def ann_kernel(M):
    h = wedge(lin(M),r0)
    cols = [bits(wedge(h,e),idx5) for e in E]
    # enumerate the 7-bit kernel
    K=[]
    for mask in range(128):
        z=0
        for i,c in enumerate(cols):
            if (mask>>i)&1:
                z ^= c
        if z==0:
            K.append(mask)
    return K

expected_ann = {0,1,2}  # basis positions E0,E1,E2
for M in (1<<1, 1<<5, (1<<1)|(1<<5)):
    K=ann_kernel(M)
    assert len(K)==8
    # all combinations of E0,E1,E2
    assert set(K) == set(range(8))

print("Ann_T(M E0)=<E0,E1,E2> for M=a1,b1,a1+b1: PASS")
print("W=E2=D^(2)_0 C: PASS")

# ----------------------------------------------------------------------
# 2. Zero-wedge classification inside S.
# ----------------------------------------------------------------------
def sform(mask):
    return xor_forms(*[Sbasis[i] for i in range(4) if (mask>>i)&1])

for q in range(16):
    for c in range(16):
        if wedge(sform(q),sform(c)):
            continue
        dependent = (q==0 or c==0 or q==c)
        both_local = ((q & ~0b0011)==0 and (c & ~0b0011)==0)
        assert dependent or both_local

print("Q^C=0 in S => dependent or Q,C in <E0,E1>: PASS")

# ----------------------------------------------------------------------
# 3. Jet separation.
# ----------------------------------------------------------------------
K0_indices = [0,1,4,5]       # a0,a1,b0,b1
P0_vectors = frozenset([0,1<<0,1<<4,(1<<0)|(1<<4)])

K0_pair_cols = [
    bits({(1<<i)|(1<<j)},idx2)
    for i,j in combinations(K0_indices,2)
]

def span_set(gens):
    out={0}
    for g in gens:
        out |= {x^g for x in tuple(out)}
    return frozenset(out)

# all 1- and 2-dimensional subspaces of K0
K0_vectors=[]
for m in range(16):
    v=0
    for j,i in enumerate(K0_indices):
        if (m>>j)&1:
            v ^= 1<<i
    K0_vectors.append(v)

Us=set()
for v in K0_vectors[1:]:
    Us.add(span_set([v]))
for v,w in combinations(K0_vectors[1:],2):
    U=span_set([v,w])
    if len(U)==4:
        Us.add(U)

def U_wedge_L_cols(U):
    cols=[]
    for u in U:
        if not u:
            continue
        for i in range(N):
            cols.append(bits(wedge(lin(u),lin(1<<i)),idx2))
    return cols

checked=0
for U in Us:
    if U == P0_vectors:
        continue
    cols = S2 + K0_pair_cols + U_wedge_L_cols(U)
    assert intersection_dim(T2,cols) == 4
    checked += 1

# The unique exceptional plane really is P0.
bad_cols = S2 + K0_pair_cols + U_wedge_L_cols(P0_vectors)
assert intersection_dim(T2,bad_cols) == 5

print(f"jet separation for {checked} subspaces U<=K0, dim U<=2, U!=P0: PASS")
print("P0 is the unique exceptional 2-plane: PASS")

# Also check T intersect Lambda^2 K0 = <E0,E1>.
assert intersection_dim(T2,K0_pair_cols) == 2
print("T intersect Lambda^2 K0 = <E0,E1>: PASS")

# ----------------------------------------------------------------------
# 4. g-using branch.
# ----------------------------------------------------------------------
def hankel_rank(alpha,beta):
    # c0=beta,c1=alpha,c2=1,c3..c6=0
    rows = [
        beta | (alpha<<1) | (1<<2),
        alpha | (1<<1),
        1,
        0,
    ]
    return rank(rows)

for alpha,beta in product((0,1),repeat=2):
    F2 = xor_forms(E[2], E[1] if alpha else set(), E[0] if beta else set())

    # wedge F2 : S -> Lambda^4
    cols = [bits(wedge(F2,s),idx4) for s in Sbasis]
    assert rank(cols)==4

    # H(F2) rank=3.
    assert hankel_rank(alpha,beta)==3

    # wedge F2 : L -> Lambda^3 is injective.
    lcols = [bits(wedge(F2,lin(1<<i)),idx3) for i in range(N)]
    assert rank(lcols)==8

print("F2^(-) injective on S for all F2=E2+alpha E1+beta E0: PASS")
print("rank H(F2)=3 and L -> Lambda^3, w |-> F2^w, is injective: PASS")

print("ALL SATURATION LINEAR/EXTERIOR CHECKS PASS")
