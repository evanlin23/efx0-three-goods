"""Theta census (k4/oc1max_multi.md §2).  At a hard perfect start, for every unfrozen agent z let
Theta(z) = {d in D : d is threatened by W_z = J + {Y_z} at p_d}.  Lemma 2 with H = empty shows Theta(z) != {} for every
unfrozen z (Proposition T0).  This script records, per start:
  * min_z |Theta(z)|;
  * whether some canonical chain from k to a head z with Theta(z) = {k} exists ('single-theta chain');
  * whether the clean chains found by dred.py are of that kind, or need unfreezing (UNFRZ) of Theta(z) - {k}.

    python3 k4/oc1max_multi/theta.py FILE.jsonl [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen, sstar
from dred import canonical_chains, improving_sets, obstacles


def theta(I, base, z, D, J):
    W = J + list(base[z])
    return frozenset(d for d in D if I.threat(d, I.V(d, base[d]), W))


if __name__ == '__main__':
    T = collections.Counter(); ex = {}
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            base = base_from_picks(tuple(rec['picks'])); J = junk(I, base); D = rec['D']; F = set(frozen(I, base))
            U = [z for z in range(I.n) if z not in F]
            th = {z: theta(I, base, z, D, J) for z in U}
            T['starts'] += 1
            if any(not th[z] for z in U): T['VIOLATION: some unfrozen z has Theta(z) empty'] += 1
            mn = min(len(th[z]) for z in U); T['min |Theta| = %d' % mn] += 1
            st = set()
            for k in D:
                for path in canonical_chains(I, base, k):
                    z = path[-1]
                    for H0 in improving_sets(I, base, k, J + list(base[z]), True):
                        nb, ob = obstacles(I, base, path, H0); ok = sstar(I, nb, k)
                        if th[z] == {k}:
                            st.add('single-theta chain')
                            if ok: st.add('single-theta chain repairs')
                        if ok and not ({'HEAD', 'CROWD', 'DEMAND'} & ob):
                            st.add('clean repair')
                            if th[z] == {k}: st.add('clean repair, single theta')
                            elif k in th[z]: st.add('clean repair, Theta(z) - {k} unfrozen or raised')
                            else: st.add('clean repair, k not in Theta(z)')
            for s in st: T['  ' + s] += 1
            key = ('min|Theta|=%d' % mn, 'single-theta chain repairs' in st, 'clean repair' in st)
            T[key] += 1
            if key not in ex or I.n < len(ex[key]['inst']['sets']): ex[key] = rec
    for k in sorted(T, key=str): print(k, T[k])
    for k in sorted(ex, key=str):
        r = ex[k]; print('example', k, r['name'], json.dumps([r['inst']['sets'], r['inst']['vals']]), 'picks', r['picks'])
