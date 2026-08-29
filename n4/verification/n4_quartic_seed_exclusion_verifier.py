#!/usr/bin/env python3
"""
Finite regression checker for the quartic-seed exclusion used in the
n=4 unrestricted XOR-AND polynomial-multiplication proof.

This file checks only finite coordinate statements that also have hand proofs:

1. Target Hankel forms of rank <= 2 outside the rational-place space R
   consist of the six rational tangents and the three nonzero vectors of
   the degree-2 place D_*; every such outside-R form has alternating rank 4.

2. Low-low quartic collision:
   for the three GL_2/PGL_2 orbit types of a quartic plane P <= R, the
   cubic-cancellation equation constrains the affine differences x,y as:
      P=<r0,r1>:              x in P1, y in P0;
      P=<r0,r1+rinf>:         x=0, y in P0;
      P=<r0+r1,r0+rinf>:      x=y=0.
   For every allowed U=<x,y>,
      T intersect (R + U wedge L) = R.
   This is also checked via the support criterion.

3. g-using quartic collision:
   after F c = F forces the quadratic part of c to be r0 and
   F2=tau0+eps*r0, a quartic plane containing r0 has two stabilizer orbits:
      type A: <r0,r1>,
      type B: <r0,r1+rinf>.
   On the three slices on which c=1, exhaustive solution of the exact
   complementary ANF equations finds no solution.  This guards the hand
   slice proof in the manuscript.

Exterior operations are over F_2. Boolean ANF multiplication is squarefree
union (OR) of monomial supports.
"""

from itertools import combinations, product

# ---------- basic GF(2) helpers ----------
def rank(vecs):
    B={}
    for v in vecs:
        y=v
        while y:
            p=y.bit_length()-1
            if p in B: y ^= B[p]
            else: B[p]=y; break
    return len(B)

def span(gens):
    out={0}
    for g in gens:
        out |= {x^g for x in tuple(out)}
    return out

# ---------- exterior algebra on 8 variables ----------
N=8
def lin_form(mask):
    return {1<<i for i in range(N) if (mask>>i)&1}

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
            if a&b: continue
            z=a|b
            if z in out: out.remove(z)
            else: out.add(z)
    return out

a=[lin_form(1<<i) for i in range(4)]
b=[lin_form(1<<(4+i)) for i in range(4)]
E=[]
for s in range(7):
    E.append(fxor(*[
        wedge(a[i],b[s-i]) for i in range(4) if 0<=s-i<4
    ]))
r0=E[0]
rinf=E[6]
r1=fxor(*E)
R=[r0,r1,rinf]

basis2=[sum(1<<i for i in I) for I in combinations(range(8),2)]
idx2={m:i for i,m in enumerate(basis2)}
def bits2(f):
    z=0
    for m in f: z ^= 1<<idx2[m]
    return z
Tbits=[bits2(e) for e in E]
Rbits=[bits2(e) for e in R]

def interdim(A,B):
    return rank(A)+rank(B)-rank(A+B)

# ---------- Hankel rank ----------
def h_rank(c):
    rows=[]
    for i in range(4):
        row=0
        for j in range(4):
            if (c>>(i+j))&1: row |= 1<<j
        rows.append(row)
    return rank(rows)

low=[c for c in range(1,128) if h_rank(c)<=2]
assert len(low)==15
Rseq=span([1<<0,1<<6,(1<<7)-1])
outside=[c for c in low if c not in Rseq]
assert len(outside)==9
assert all(h_rank(c)==2 for c in outside)

# six tangents and D*
tangents={
    0b0000010, 0b0000011,      # at infinity in this low-to-high display convention
    0b0100000, 0b1100000,      # at zero
    0b0101010, 0b1010101,      # at one
}
Dstar={0b0110110,0b1101101,0b1011011}
assert set(outside)==tangents|Dstar
print("rank<=2 target classification outside R: 6 tangents + 3 degree-2-place forms: PASS")

# ---------- support spaces ----------
P0=span([1<<0,1<<4])
P1=span([0b1111,0b1111<<4])
Pinf=span([1<<3,1<<7])

K0=span([1<<0,1<<1,1<<4,1<<5])
K1=span([0b1111,(1<<1)|(1<<3),0b1111<<4,((1<<1)|(1<<3))<<4])
Kinf=span([1<<3,1<<2,1<<7,1<<6])
uA=(1<<0)|(1<<2)|(1<<3)
vA=(1<<1)|(1<<2)
Kd=span([uA,vA,uA<<4,vA<<4])

assert K0 & P1 == {0}
assert K1 & P0 == {0}
assert Kinf & P0 == {0} and Kinf & P1 == {0}
assert Kd & P0 == {0} and Kd & P1 == {0}
print("tangent/degree-2 support separation from P0,P1: PASS")

# Direct finite check of the low-low separation lemma.
allL=[1<<i for i in range(8)]
def UwedgeL(U):
    cols=[]
    for u in U:
        if not u: continue
        uf=lin_form(u)
        for e in allL:
            cols.append(bits2(wedge(uf,lin_form(e))))
    return cols

allowed=[]
# type A x in P1, y in P0
for x in P1:
    for y in P0:
        allowed.append(span([x,y]))
# type B x=0,y in P0
for y in P0:
    allowed.append(span([y]))
allowed=set(map(frozenset,allowed))

for U in allowed:
    cols=Rbits+UwedgeL(U)
    assert interdim(Tbits,cols)==3
print(f"low-low separation T intersect (R+U^L)=R for {len(allowed)} allowed U: PASS")

# ---------- Boolean ANF on six complementary variables ----------
pairs=[(i,j) for i in range(6) for j in range(i+1,6)]
def lpoly(mask):
    p=0
    for i in range(6):
        if (mask>>i)&1: p ^= 1<<(1<<i)
    return p
ONE=1
def mul(P,Q):
    ps=[m for m in range(64) if (P>>m)&1]
    qs=[m for m in range(64) if (Q>>m)&1]
    z=0
    for x in ps:
        for y in qs:
            z ^= 1<<(x|y)
    return z
def part(P,d):
    z=0
    for m in range(64):
        if (P>>m)&1 and m.bit_count()==d: z^=1<<m
    return z

# complement order a1,a2,a3,b1,b2,b3
u=1<<0; aa2=1<<1; aa3=1<<2
v=1<<3; bb2=1<<4; bb3=1<<5
Abar=u|aa2|aa3
Bbar=v|bb2|bb3
Ap=lpoly(Abar); Bp=lpoly(Bbar)
Q_A=mul(Ap,Bp)
Q_inf=mul(lpoly(aa3),lpoly(bb3))
Q_B=Q_A^Q_inf
uP=lpoly(u); vP=lpoly(v)

points=((0,0),(1,0),(0,1),(1,1))

# Exhaust the exact three-slice equations for the two quartic-plane orbits.
# First factor: l + sigma_s, where sigma_s=k+A*x+B*y+x*y.
# Second factor: Q_D + n + x*Bbar+y*Abar + kappa_s.
# a contributes lambda1*r1 + lambdainf*rinf.
for typ,QD,ls in [
    ("A",Q_A,[0,Abar,Bbar,Abar^Bbar]),
    ("B",Q_B,[0]),
]:
    total=0
    for missing in range(4):
        keep=[p for i,p in enumerate(points) if i!=missing]
        count=0
        for l in ls:
            lp=lpoly(l)
            for n in range(64):
                np=lpoly(n)
                for k,A,B,k2,C,D,lam1,laminf in product((0,1),repeat=8):
                    Us=[]
                    ok=True
                    for x,y in keep:
                        sigma=k^(A*x)^(B*y)^(x*y)
                        kappa=k2^(C*x)^(D*y)^(x*y)
                        dlin=(Bbar if x else 0)^(Abar if y else 0)
                        p1=lp^(ONE if sigma else 0)
                        p2=QD^lpoly(n^dlin)^(ONE if kappa else 0)
                        g=mul(p1,p2)
                        aq=0
                        if lam1:
                            aq ^= Q_A ^ lpoly(dlin) ^ (ONE if x*y else 0)
                        if laminf:
                            aq ^= Q_inf
                        U=g^aq
                        if any(part(U,d) for d in range(2,7)):
                            ok=False; break
                        Us.append(part(U,1))
                    if not ok: continue
                    xb,yb=keep[0]
                    for j in range(1,3):
                        x,y=keep[j]
                        rhs=lpoly((u if (yb^y) else 0)^(v if (xb^x) else 0))
                        if (Us[0]^Us[j]) != rhs:
                            ok=False; break
                    if ok:
                        count+=1
        assert count==0
        total+=count
    print(f"g-using quartic orbit {typ}: no three-slice solution: PASS")

print("ALL QUARTIC-SEED EXCLUSION REGRESSION CHECKS PASS")
