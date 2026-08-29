#!/usr/bin/env python3
"""
Exact GF(2) check of the repaired three-slice Feedback argument.

Complement basis:
    u=a1, a2, a3, v=b1, b2, b3
encoded as six bits 0..5.

Let
    Abar = a1+a2+a3,
    Bbar = b1+b2+b3.

For the anchored theta=0, AnnDim=2 branch:
    F_2 = u*y + x*v + eps*x*y.

After F*c=F one has c=1 on exactly three (x,y)-slices.
Write
    M = m + A*x + B*y,
    z = n + C*x + D*y,
    a = affine + lam0*r0 + lam1*r1 + laminf*rinf.

On every c=1 slice, F_s=U_s=(g+a)_s.

Quadratic matching in the six complement variables gives
    m ^ n = lam1*Abar^Bbar + laminf*a3^b3.

Linear slice differences then give, for pairs s,t among the three kept slices,
    dmu*n + dnu*m
      + lam1*(dx*Bbar + dy*Abar)
    = dy*u + dx*v.

The verifier exhausts all parameters and checks that every solution forces
span<u,v> subset span<m,n>, hence m is in span<u,v>; in fact there are no
solutions compatible with the AnnDim=2 condition m notin span<u,v>.
"""

from itertools import product

# Six-dimensional complement vectors as bit masks.
U = 1 << 0
A2 = 1 << 1
A3 = 1 << 2
V = 1 << 3
B2 = 1 << 4
B3 = 1 << 5
ABAR = U | A2 | A3
BBAR = V | B2 | B3

# Lambda^2 of the six-dimensional complement, packed into 15 bits.
pairs = [(i,j) for i in range(6) for j in range(i+1,6)]
pidx = {ij:k for k,ij in enumerate(pairs)}

def wedge(a,b):
    out = 0
    for i,j in pairs:
        bit = ((a>>i)&1)*((b>>j)&1) ^ ((a>>j)&1)*((b>>i)&1)
        if bit:
            out ^= 1 << pidx[(i,j)]
    return out

Q1 = wedge(ABAR, BBAR)
QINF = wedge(A3, B3)

def rank2(a,b):
    if a == 0 and b == 0:
        return 0
    if a == 0 or b == 0 or a == b:
        return 1
    return 2

def in_span(x,a,b):
    return x in {0,a,b,a^b}

points = ((0,0),(1,0),(0,1),(1,1))

solutions = 0
ann2_compatible = 0
quad_case_counts = {}
for missing in range(4):
    keep = [i for i in range(4) if i != missing]
    base = keep[0]
    xb,yb = points[base]

    for lam1, laminf in product((0,1), repeat=2):
        rhsq = (Q1 if lam1 else 0) ^ (QINF if laminf else 0)
        for m in range(64):
            for n in range(64):
                if wedge(m,n) != rhsq:
                    continue

                quad_case_counts[(lam1,laminf)] = quad_case_counts.get((lam1,laminf),0)+1

                # Structural consequences of the quadratic equation.
                if lam1 and laminf:
                    raise AssertionError("rank-4 RHS unexpectedly decomposable")
                if lam1:
                    assert rank2(m,n) == 2
                    assert {0,m,n,m^n} == {0,ABAR,BBAR,ABAR^BBAR}
                if laminf:
                    assert rank2(m,n) == 2
                    assert {0,m,n,m^n} == {0,A3,B3,A3^B3}

                for A,B,C,D in product((0,1), repeat=4):
                    ok = True
                    for j in keep[1:]:
                        xj,yj = points[j]
                        dmu = (A*xb ^ B*yb) ^ (A*xj ^ B*yj)
                        dnub = C*xb ^ D*yb ^ (xb*yb)
                        dnuj = C*xj ^ D*yj ^ (xj*yj)
                        dnu = dnub ^ dnuj

                        lhs = 0
                        if dmu:
                            lhs ^= n
                        if dnu:
                            lhs ^= m
                        dx = xb ^ xj
                        dy = yb ^ yj
                        if lam1:
                            if dx:
                                lhs ^= BBAR
                            if dy:
                                lhs ^= ABAR

                        rhs = (U if dy else 0) ^ (V if dx else 0)
                        if lhs != rhs:
                            ok = False
                            break

                    if not ok:
                        continue

                    solutions += 1

                    # The two independent slice differences force u,v into span(m,n).
                    assert in_span(U,m,n)
                    assert in_span(V,m,n)
                    assert rank2(m,n) == 2
                    assert {0,m,n,m^n} == {0,U,V,U^V}

                    # AnnDim=2 means the class m mod P0 is not one of
                    # 0,u,v,u+v; in this complement parameterization that is m notin <u,v>.
                    if not in_span(m,U,V):
                        ann2_compatible += 1

assert ann2_compatible == 0

print("quadratic case counts (before linear equations):")
for k in sorted(quad_case_counts):
    print(f"  lambda1={k[0]} lambdainf={k[1]}: {quad_case_counts[k]}")
print("full quadratic+three-slice linear solutions:", solutions)
print("solutions compatible with AnnDim=2:", ann2_compatible)
print("PASS: every full solution forces span(m,n)=span(u,v)")
print("PASS: the anchored AnnDim=2 branch has no solution")
