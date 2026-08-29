#!/usr/bin/env python3
"""
Independent exterior-algebra check for n4_first_child_scan_results.txt.

Parses exactly the consolidated 14 HIGH_CHILD records (not the repeated raw
transcripts).  Each high part is cubic.  Computes rank of
    T -> Lambda^5 L,   t |-> h ^ t
over GF(2), with T=<E0,...,E6>, and reports dim Ann_T(h).
"""
from pathlib import Path
import re
from itertools import combinations

RESULTS = Path(__file__).with_name("n4_first_child_scan_results.txt")
text = RESULTS.read_text()
section = text.split("All 14 HIGH_CHILD records:\n",1)[1].split("\nRaw chunk transcripts:",1)[0]

b5 = [sum(1 << i for i in I) for I in combinations(range(8), 5)]
idx5 = {m:i for i,m in enumerate(b5)}

E = []
for s in range(7):
    E.append([
        (1 << i) | (1 << (4+s-i))
        for i in range(4) if 0 <= s-i < 4
    ])

def wedge_bits(h_terms, e_terms):
    coeff = {}
    for u in h_terms:
        for v in e_terms:
            if u & v:
                continue
            z = u | v
            coeff[z] = coeff.get(z, 0) ^ 1
    out = 0
    for z,c in coeff.items():
        if c:
            out ^= 1 << idx5[z]
    return out

def rank(cols):
    B = {}
    for x in cols:
        y = x
        while y:
            p = y.bit_length()-1
            if p in B:
                y ^= B[p]
            else:
                B[p] = y
                break
    return len(B)

records = []
for ln in section.splitlines():
    if not ln.startswith("HIGH_CHILD "):
        continue
    m = re.search(r"rep=(\d+).*high=(.*)$", ln)
    assert m
    rep = int(m.group(1))
    htxt = m.group(2)
    h_terms = []
    for item in htxt.split(","):
        mask_hex, degree = item.split(":")
        assert int(degree) == 3
        h_terms.append(int(mask_hex, 16))
    ann = 7 - rank([wedge_bits(h_terms, e) for e in E])
    records.append((rep, ann, htxt))

assert len(records) == 14
assert all(ann == 3 for _,ann,_ in records)

print("records:", len(records))
print("all Ann_T(h) dimensions equal 3: PASS")
for rep,ann,htxt in records:
    print(f"rep={rep} AnnDim={ann} high={htxt}")
