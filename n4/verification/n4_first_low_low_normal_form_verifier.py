#!/usr/bin/env python3
"""
Normal-form regression checker for the *first useful low-low suffix gate*
in the n=4 proof.

A pre-seed low product with nonzero cubic high part and no quartic part can,
modulo Aff+R, be represented as
    P(G,N,z) = (G + z) * N,
where G is one of the 7 nonzero rational-place quadratic combinations
in R=<r0,r1,rinf>, and N,z are linear forms.

The checker groups these normal forms by cubic high part and asks whether two
products with the same high part have quadratic difference in T\\R.

Claim checked:
  - exactly 9 nonzero high parts admit such a collision;
  - all 9 have target annihilator dimension 3;
  - they are precisely the three first-derivative tangent classes at each of
    the three rational places;
  - every collision target coset is the corresponding first Hasse jet modulo R.

This is a regression check only; the manuscript proves the claim by the
two-orbit comparison of the rational-place supports plus the rank<=2 Hankel
support classification.
"""

from itertools import combinations

NV=8

def lin(mask):
    return {1<<i for i in range(NV) if (mask>>i)&1}

def fxor(*forms):
    out=set()
    for f in forms:
        for m in f:
            if m in out: out.remove(m)
            else: out.add(m)
    return out

def mul(P,Q):
    out=set()
    for a in P:
        for b in Q:
            z=a|b
            if z in out: out.remove(z)
            else: out.add(z)
    return out

def wedge(P,Q):
    out=set()
    for a in P:
        for b in Q:
            if a&b: continue
            z=a|b
            if z in out: out.remove(z)
            else: out.add(z)
    return out

def rank(vecs):
    B={}
    for x in vecs:
        y=x
        while y:
            p=y.bit_length()-1
            if p in B: y^=B[p]
            else: B[p]=y; break
    return len(B)

a=[lin(1<<i) for i in range(4)]
b=[lin(1<<(4+i)) for i in range(4)]
E=[]
for s in range(7):
    E.append(fxor(*[
        wedge(a[i],b[s-i]) for i in range(4) if 0<=s-i<4
    ]))
r0=E[0]; rinf=E[6]; r1=fxor(*E)
Rbasis=[r0,r1,rinf]

basis2=[sum(1<<i for i in I) for I in combinations(range(8),2)]
basis3=[sum(1<<i for i in I) for I in combinations(range(8),3)]
basis5=[sum(1<<i for i in I) for I in combinations(range(8),5)]
idx2={m:i for i,m in enumerate(basis2)}
idx3={m:i for i,m in enumerate(basis3)}
idx5={m:i for i,m in enumerate(basis5)}

def bits(form,idx):
    z=0
    for m in form: z^=1<<idx[m]
    return z

T2=[bits(e,idx2) for e in E]
R2=[bits(e,idx2) for e in Rbasis]

def reduce(v,basis):
    B={}
    for x in basis:
        y=x
        while y:
            p=y.bit_length()-1
            if p in B:y^=B[p]
            else:B[p]=y;break
    y=v
    for p in sorted(B,reverse=True):
        if (y>>p)&1:y^=B[p]
    return y

target_res={}
for mask in range(128):
    v=0
    for i,e in enumerate(T2):
        if (mask>>i)&1:v^=e
    target_res.setdefault(reduce(v,R2),[]).append(mask)
target_nonzero=set(target_res)-{0}

def Rform(mask):
    return fxor(*[Rbasis[i] for i in range(3) if (mask>>i)&1])

Rforms=[Rform(i) for i in range(1,8)]

def highbits(P):
    return bits({m for m in P if m.bit_count()==3},idx3)

def qbits(P):
    return bits({m for m in P if m.bit_count()==2},idx2)

# For each (G,N), enumerate the q residues obtainable by z.
groups={}
for gi,G in enumerate(Rforms,1):
    for N in range(1,256):
        base=mul(G,lin(N))
        h=highbits(base)
        if h==0: continue
        qs=set()
        for z in range(256):
            P=fxor(base,mul(lin(z),lin(N)))
            qs.add(reduce(qbits(P),R2))
        groups.setdefault(h,[]).append((gi,N,qs))

def ann_dim(hb):
    h={basis3[i] for i in range(len(basis3)) if (hb>>i)&1}
    cols=[bits(wedge(h,e),idx5) for e in E]
    return 7-rank(cols)

collision={}
for h,lst in groups.items():
    hits=[]
    for i in range(len(lst)):
        gi,Ni,Qi=lst[i]
        for j in range(i,len(lst)):
            gj,Nj,Qj=lst[j]
            found=None
            for x in Qi:
                for y in Qj:
                    d=x^y
                    if d in target_nonzero:
                        found=d;break
                if found is not None: break
            if found is not None:
                hits.append((gi,Ni,gj,Nj,found))
    if hits:
        collision[h]=hits

assert len(collision)==9
assert all(ann_dim(h)==3 for h in collision)

# Identify the 9 hard tangent highs explicitly.
hard=set()
places=[
    (r0, [1<<1,1<<5,(1<<1)|(1<<5)]),            # a1,b1
    (r1, [0b1010,0b1010<<4,0b1010|(0b1010<<4)]), # A'(1),B'(1)
    (rinf,[1<<2,1<<6,(1<<2)|(1<<6)]),             # a2,b2
]
for G,Ms in places:
    for M in Ms:
        hard.add(bits(wedge(lin(M),G),idx3))
assert set(collision)==hard

# Corresponding first-jet target quotient residues.
jet_masks=[
    1<<1,                          # E1 at 0
    (1<<1)|(1<<3)|(1<<5),         # D^(1) C at 1
    1<<5,                          # E5 at infinity
]
jet_res={reduce(
    sum((T2[i] if (mask>>i)&1 else 0) for i in range(7)),R2)
    for mask in jet_masks}

for h,hits in collision.items():
    for *_,d in hits:
        assert d in jet_res

print("low-low normal-form collision highs:",len(collision))
print("all collision highs have Ann_T dimension 3: PASS")
print("collision highs are exactly 9 first-derivative tangent highs: PASS")
print("all useful target differences are the corresponding first Hasse jet mod R: PASS")
print("ALL FIRST-LOW-LOW REGRESSION CHECKS PASS")
