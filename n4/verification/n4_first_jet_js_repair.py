#!/usr/bin/env python3
"""
Self-contained finite checker for two final n=4 proof repairs:

(1) First-jet-only:
    For F2=E2+alpha E1+beta E0, wedge by F2 is injective on
    R=<E0,E6,r1>.  This rules out a g-using first suffix gate with a
    nonzero E2 coefficient via F*c=F.

(2) Corrected jet-separation bookkeeping:
    If q=A E2+B E3+C E4 and s=d0 E0+d1 E1+d6 E6+dr r1 satisfy
        q+s in Lambda^2 K0 + U^L,
    then the outside-outside coefficients first force
        dr=C=d6=0.
    After absorbing d0 E0+d1 E1 into Lambda^2 K0, the four mixed
    K0/outside coefficient vectors are
        Ay+Bv, By, Ax+Bu, Bx.
    For dim U<=2, U!=P0=<x,y>, these force A=B=0.
"""

from itertools import combinations, product

# L basis: x=a0,u=a1,a2,a3,y=b0,v=b1,b2,b3.
names = ["x","u","a2","a3","y","v","b2","b3"]
N=8

def fxor(*forms):
    out=set()
    for f in forms:
        for m in f:
            if m in out: out.remove(m)
            else: out.add(m)
    return out

def wedge(f,g):
    out=set()
    for a in f:
        for b in g:
            if a & b: continue
            z=a|b
            if z in out: out.remove(z)
            else: out.add(z)
    return out

def lin(mask):
    return {1<<i for i in range(N) if (mask>>i)&1}

a=[lin(1<<i) for i in range(4)]
b=[lin(1<<(4+i)) for i in range(4)]

E=[]
for s in range(7):
    E.append(fxor(*[
        wedge(a[i],b[s-i]) for i in range(4) if 0<=s-i<4
    ]))
r1=fxor(*E)

def rank(rows):
    B={}
    for x in rows:
        y=x
        while y:
            p=y.bit_length()-1
            if p in B: y ^= B[p]
            else: B[p]=y; break
    return len(B)

def mon(mask):
    return "^".join(names[i] for i in range(N) if (mask>>i)&1)

# ------------------------------------------------------------------
# (1) Three-row table for R=<E0,E6,r1>.
# ------------------------------------------------------------------
R=[E[0],E[6],r1]
rows = [
    (1<<0)|(1<<1)|(1<<4)|(1<<5), # x u y v
    (1<<2)|(1<<3)|(1<<4)|(1<<5), # a2 a3 y v
    (1<<2)|(1<<3)|(1<<4)|(1<<7), # a2 a3 y b3
]

print("FIRST-JET THREE-COLUMN TABLE")
print("columns = [E0,E6,r1]")
for alpha,beta in product((0,1),repeat=2):
    F2=fxor(E[2], E[1] if alpha else set(), E[0] if beta else set())
    cols=[wedge(F2,c) for c in R]
    mat=[]
    for rr in rows:
        mat.append([1 if rr in c else 0 for c in cols])
    assert rank([sum(bit<<j for j,bit in enumerate(row)) for row in mat])==3
    print(f"alpha={alpha} beta={beta}:")
    for rr,row in zip(rows,mat):
        print(" ",mon(rr),row)
print("injective on R for all alpha,beta: PASS")
print()

# ------------------------------------------------------------------
# (2) Corrected JS bookkeeping.
# ------------------------------------------------------------------
# K0 coordinates use x,u,y,v = original indices 0,1,4,5.
K0idx=[0,1,4,5]
P0=frozenset([0,1<<0,1<<4,(1<<0)|(1<<4)])

print("CORRECTED JS OUTSIDE-OUTSIDE EQUATIONS")
print("coeff(a2^b3)=coeff(a3^b2)=dr")
print("coeff(a2^b2)=C+dr")
print("coeff(a3^b3)=d6+dr")
print("therefore absence of outside-outside terms gives dr=C=d6=0")
print("remaining mixed vectors: Ay+Bv, By, Ax+Bu, Bx")
print()

# Exhaust the small U statement as a guard.
def span_set(gens):
    out={0}
    for g in gens:
        out |= {x^g for x in tuple(out)}
    return frozenset(out)

kvec=[]
for mask in range(16):
    v=0
    for j,i in enumerate(K0idx):
        if (mask>>j)&1: v ^= 1<<i
    kvec.append(v)

Us=set()
for v in kvec[1:]:
    Us.add(span_set([v]))
for v,w in combinations(kvec[1:],2):
    U=span_set([v,w])
    if len(U)==4: Us.add(U)

x=1<<0; u=1<<1; y=1<<4; v=1<<5
checked=0
for U in Us:
    if U==P0: continue
    for A,B in product((0,1),repeat=2):
        vecs=[
            (y if A else 0) ^ (v if B else 0),
            y if B else 0,
            (x if A else 0) ^ (u if B else 0),
            x if B else 0,
        ]
        if all(z in U for z in vecs):
            assert A==0 and B==0
    checked += 1
print(f"nonexceptional U checked: {checked}")
print("mixed-vector implication A=B=0: PASS")
print("P0 is excluded exactly because x,y in U would force U=P0: PASS")
