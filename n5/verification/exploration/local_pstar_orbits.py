from __future__ import annotations

import itertools
from collections import defaultdict, deque


PAIRS = list(itertools.combinations(range(4), 2))
PINDEX = {p: i for i, p in enumerate(PAIRS)}
HGEN = (1 << 1) ^ (1 << 4), (1 << 2) ^ (1 << 3) ^ (1 << 4)


def rank(vs):
    piv = {}
    for v in vs:
        while v:
            p = v.bit_length() - 1
            if p in piv:
                v ^= piv[p]
            else:
                piv[p] = v
                break
    return len(piv)


def span(vs):
    out = set()
    for c in range(1 << len(vs)):
        v = 0
        for i, b in enumerate(vs):
            if c >> i & 1:
                v ^= b
        out.add(v)
    return out


H = span(HGEN)


def wedge2_action(cols):
    out = []
    for i, j in PAIRS:
        v = 0
        for a in range(4):
            for b in range(a + 1, 4):
                bit = ((cols[i] >> a & 1) & (cols[j] >> b & 1)) ^ \
                      ((cols[i] >> b & 1) & (cols[j] >> a & 1))
                if bit:
                    v ^= 1 << PINDEX[(a, b)]
        out.append(v)
    return out


def apply(action, q):
    v = 0
    for i in range(6):
        if q >> i & 1:
            v ^= action[i]
    return v


def klein(q):
    a, b, c, d, ee, f = [(q >> i) & 1 for i in range(6)]
    return q != 0 and (a * f ^ b * ee ^ c * d) == 0


def canonical_coset(q):
    return min(q ^ h for h in H)


def main():
    grass = {q for q in range(1, 64) if klein(q)}
    fibers = defaultdict(set)
    for q in grass:
        fibers[canonical_coset(q)].add(q)
    effective = {c for c, ps in fibers.items() if len(ps) == 3}
    print("fiber sizes", sorted((len(ps), c) for c, ps in fibers.items()),
          "effective", len(effective))

    stabilizer = []
    for cols in itertools.permutations(range(1, 16), 4):
        if rank(list(cols)) != 4:
            continue
        act = wedge2_action(cols)
        if {apply(act, h) for h in H} == H:
            stabilizer.append(act)
    print("stabilizer", len(stabilizer))
    unseen = set(effective)
    orbits = []
    while unseen:
        start = next(iter(unseen))
        orb = {canonical_coset(apply(act, start)) for act in stabilizer}
        orb &= effective
        orbits.append(orb)
        unseen -= orb
    print("orbits", [len(o) for o in orbits], [sorted(o) for o in orbits])


if __name__ == "__main__":
    main()
