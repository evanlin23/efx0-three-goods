"""RF-PRIV gap case (k4/RFMIN.md §6): random strict connected k = 4 cores with a private-top agent f; at every
maximum-matching start where the picks have no one-absorber completion, record: D_full (frozen agents valuing the junk
above their pick), whether some one-move state has a completion with owner f, and the shape of the repairing moves
(which agent's base changes). Usage: privtop_gap.py N SEED NMIN NMAX"""
import sys, os, random, itertools, collections, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sdc'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oc1_mc2_rand import Inst, gen
from privtop_random import nu
from multiprocessing import Pool

def completion_owners(I, base):
    n = I.n; J = [g for g in range(I.m) if all(g not in b for b in base)]
    out = set()
    for a in [None] + list(range(n)):
        found = False
        for r in range(0 if a is None else 2, len(J) + 1):
            if a is None and r: break
            for S in itertools.combinations(J, r):
                rest = [g for g in J if g not in S]; others = [i for i in range(n) if i != a]
                for recv in itertools.permutations(others, len(rest)):
                    B = [list(b) for b in base]
                    if a is not None: B[a] += list(S)
                    for g, i in zip(rest, recv): B[i].append(g)
                    if I.efx0(B): found = True; break
                if found: break
            if found: break
        if found: out.add(a)
    return out

def job(args):
    n, seed = args
    rng = random.Random(seed)
    while True:
        try: sets, vals = gen(n, rng)
        except ValueError: continue
        deg = collections.Counter(g for S in sets for g in S)
        pt = [a for a in range(n) if deg[sets[a][vals[a].index(max(vals[a]))]] == 1]
        if pt: break
    I = Inst(sets, vals); N = nu(I); f = pt[0]
    C = collections.Counter(); ex = []
    for pk in set(I.sd(o) for o in itertools.permutations(range(n))):
        if sum(x is not None for x in pk) != N: continue
        C['max starts'] += 1
        base = [[g] if g is not None else [] for g in pk]
        if I.one_absorber(base): continue
        C['picks do not complete'] += 1
        J = set(range(I.m)) - {g for g in pk if g is not None}
        frozen = [a for a in range(n) if pk[a] is not None and any(i != a and I.v[i].get(pk[a], 0) > (I.v[i].get(pk[i], 0) if pk[i] is not None else 0) for i in range(n))]
        D = [a for a in frozen if I.V(a, J) > I.v[a][pk[a]]]
        C['|D_full| = %d' % len(D)] += 1
        owners, shapes = set(), set()
        two = set()
        for st in I.moves(base):
            st = [list(b) for b in st]
            ch = tuple(sorted(a for a in range(n) if sorted(st[a]) != sorted(base[a])))
            o = completion_owners(I, st)
            if o:
                owners |= o
                shapes.add(('chain through D' if any(a in D for a in ch) else 'no D agent moves', 'f moves' if f in ch else 'f fixed', len(ch)))
                if len(ch) == 2 and f in o:
                    d = next((a for a in ch if pk[a] is not None and set(st[a]) <= J), None)
                    w = next((a for a in ch if a != d), None)
                    if d is not None and pk[d] in st[w]:
                        two.add(('d in D' if d in D else 'd not in D', 'w unfrozen' if w not in frozen else 'w frozen',
                                 '|H0| = %d' % len(st[d])))
        C['two-agent chain d -> w with owner f: %s' % ('exists' if two else 'none')] += 1
        for t in two: C['  two-agent repair: %s, %s, %s' % t] += 1
        if any(t[0] == 'd in D' and t[1] == 'w unfrozen' and t[2] == '|H0| = 2' for t in two): C['  has a repair with d in D, w unfrozen, |H0| = 2'] += 1
        if not owners: C['OC1 FAILS (RF-PRIV counterexample)'] += 1; ex.append((sets, vals, pk))
        C['after one move, owner f possible' if f in owners else 'after one move, owner f never'] += 1
        for sh in shapes: C['repair: %s, %s, %d agents change' % sh] += 1
        if len(ex) < 3: ex.append((sets, vals, pk, sorted(owners, key=str), f))
    return C, ex

if __name__ == '__main__':
    N, seed, nmin, nmax = map(int, sys.argv[1:5])
    T = collections.Counter(); exs = []
    with Pool(4) as pool:
        for C, ex in pool.imap_unordered(job, [(nmin + i % (nmax - nmin + 1), seed * 1000003 + i) for i in range(N)]):
            T.update(C); exs += ex
    print('random private-top cores: %d instances, n = %d..%d' % (N, nmin, nmax))
    for k, x in sorted(T.items()): print('  %-58s %d' % (k, x))
    for e in exs[:4]: print('  example', json.dumps(e))
