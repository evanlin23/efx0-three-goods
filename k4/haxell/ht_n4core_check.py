"""Validates the automorphism reduction of ht_n4core.py MODE=all on the three n4_1 cores with m = 4: the reduced
enumeration must contain exactly one profile per orbit (orbits computed here from the automorphisms), and the images
must be true isomorphisms, so an isomorphism invariant must be constant on every orbit.  The invariant (computed here
from the raw EFX0 definition, without gstar_measure) is the sorted list of welfare values of the complete EFX0
allocations, which varies with the profile.

    python3 k4/haxell/ht_n4core_check.py"""
import sys, os, itertools
sys.argv = ['x', 'MODE=all']
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ht_n4core as H


def invariant(sets, m, prof):
    n = len(sets); val = [[0] * m for _ in range(n)]
    for i, (S, v) in enumerate(zip(sets, prof)):
        for g, x in zip(S, v):
            val[i][g] = x
    out = []
    for own in itertools.product(range(n), repeat=m):
        X = [[g for g in range(m) if own[g] == j] for j in range(n)]
        mine = [sum(val[i][g] for g in X[i]) for i in range(n)]
        if all(sum(val[i][g] for g in X[j]) - min(val[i][g] for g in X[j]) <= mine[i]
               for i in range(n) for j in range(n) if j != i and len(X[j]) >= 2):
            out.append(sum(mine))
    return tuple(sorted(out))


for fname, c in H.load_cores():
    if c['m'] != 4 or not fname.endswith('n4_1.json.gz'):
        continue
    sets, m = c['sets'], c['m']
    deg = [sum(g in S for S in sets) for g in range(m)]
    doms = [H.domain(S, deg) for S in sets]
    autos = H.automorphisms(sets, m)

    def orbit(prof):
        out = set()
        for a, b in autos:
            img = [None] * len(sets)
            for i, (S, v) in enumerate(zip(sets, prof)):
                d = {b[g]: x for g, x in zip(S, v)}
                img[a[i]] = tuple(d[g] for g in sets[a[i]])
            out.add(tuple(img))
        return out
    full = set(itertools.product(*doms))
    red = [tuple(p) for p in H.profiles_all(sets, m, doms)]
    seen = set(); inv_vals = set()
    for p in red:
        o = orbit(p); assert o <= full and p == min(o) and not (o & seen), p
        seen |= o
        invs = {invariant(sets, m, q) for q in sorted(o)[:6]}
        assert len(invs) == 1, ('invariant differs within an orbit', p)
        inv_vals |= invs
    assert seen == full
    print(c['idx'], sets, '|Aut|', len(autos), 'profiles', len(full), 'orbits', len(red),
          'distinct invariants', len(inv_vals), flush=True)
print('reduction checked')
