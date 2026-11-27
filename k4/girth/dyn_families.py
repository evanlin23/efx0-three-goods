"""Conjectures DYN and LR on the structured k = 4 families of k4/d_stress.py (builders copied from there: chain t with
h heads, cycle t, tree t, random pure cores), with random strict core profiles.  EVIDENCE only.

For each instance: LSS's Algorithm 2 with the G1 repair + dynamic parking (DYN), and, when the hypergraph is linear,
LSS-ROT + parking (LR) and Theorem T1's hypothesis (an agent on no 3-cycle).  Vertex 0 = every agent with the default
labels until one run succeeds.

    python3 k4/girth/dyn_families.py PROFILES SEED
"""
import collections
import itertools
import random
import sys

from lss import Inst, labels, lss_dyn_safe, lss_rot, park_any_state, is_efx0, two_cycles, triangles
from sources import domains


def counter():
    c = itertools.count()
    return lambda: next(c)


def gadget(goods, g, e):
    a = [goods() for _ in range(3)]
    xs = [[a[i], goods(), goods(), g] for i in range(3)]
    return xs + [[a[0], a[1], a[2], e]]


def chain(t, heads=1):
    goods = counter()
    sets = []
    z = goods()
    for h in range(heads):
        gs = [goods() for _ in range(t)]
        sets.append([gs[0], z, goods(), goods()])
        for j in range(t):
            sets += gadget(goods, gs[j], gs[j + 1] if j + 1 < t else z)
    return sets


def cycle(t):
    goods = counter()
    gs = [goods() for _ in range(t)]
    sets = []
    for j in range(t):
        sets += gadget(goods, gs[j], gs[(j + 1) % t])
    return sets


def tree(t):
    goods = counter()
    gs = [goods() for _ in range(t)]
    z = goods()
    sets = [[gs[0], z, goods(), goods()]]
    for j in range(t):
        c1, c2 = 2 * j + 1, 2 * j + 2
        sets += gadget(goods, gs[j], gs[c1] if c1 < t else z)
        if c2 < t:
            sets.append([gs[j], gs[c2], goods(), goods()])
    return sets


def pure(n, m, rng, tries=100000):
    import networkx as nx
    for _ in range(tries):
        sets = [sorted(rng.sample(range(m), 4)) for _ in range(n)]
        deg = [sum(g in S for S in sets) for g in range(m)]
        if min(deg) < 1 or any(sum(deg[g] == 1 for g in S) > 2 for S in sets):
            continue
        G = nx.Graph()
        G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
        if nx.is_connected(G):
            return sets
    return None


def profile(sets, rng):
    m = 1 + max(g for S in sets for g in S)
    D = domains(sets, m)
    ds = [rng.choice(d) for d in D]
    return Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m)


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    print('$ python3 k4/girth/dyn_families.py', per, flush=True)
    fams = [('chain 2', chain(2)), ('chain 3', chain(3)), ('chain 2 heads 2', chain(2, 2)), ('chain 3 heads 3', chain(3, 3)),
            ('cycle 2', cycle(2)), ('cycle 3', cycle(3)), ('cycle 4', cycle(4)), ('tree 3', tree(3)), ('tree 5', tree(5))]
    for n, m in ((6, 12), (7, 14), (8, 16), (8, 18), (10, 20)):
        S = pure(n, m, rng)
        if S:
            fams.append(('pure %d %d' % (n, m), S))
    for name, sets in fams:
        C = collections.Counter()
        I0 = Inst(sets, [[1] * len(S) for S in sets], 1 + max(g for S in sets for g in S))
        lin = not two_cycles(I0)
        on = set()
        if lin:
            for x, y, z, w in triangles(I0):
                on |= {x, y, z}
        for _ in range(per):
            I = profile(sets, rng)
            C['profiles'] += 1
            for z in range(I.n):
                r, Z = lss_dyn_safe(I, labels(I, z))
                if Z is not None:
                    assert is_efx0(I, Z) and sorted(g for b in Z for g in b) == list(range(I.m))
                    C['DYN completes'] += 1
                    break
            else:
                print('  DYN: no vertex 0 completes', name, I, flush=True)
            if lin:
                for z in range(I.n):
                    r = lss_rot(I, labels(I, z))
                    Z = park_any_state(I, r.X, r.U)
                    if Z is not None:
                        assert is_efx0(I, Z)
                        C['LR completes'] += 1
                        break
        print('%-16s n=%2d m=%2d linear=%s T1-vertex=%s  %s' % (name, I0.n, I0.m, lin,
              (len(on) < I0.n) if lin else '-', dict(C)), flush=True)


if __name__ == '__main__':
    main()
