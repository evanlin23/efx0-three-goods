"""Usage: classes.py FILE.json.gz ...
At every OC1^max-failing start of the data: (i) agents whose top good is private (always receivers holding their top);
(ii) for every receiver u, every u-first order's picks Y': maximum or not, and at maximum ones the class
(|U'|, |D_T'|): U' = unfrozen agents (no other agent prefers their pick to its own; pickless agents count), D_T' = frozen
agents threatened by the whole junk set J' at their pick (v(J') - min_J' v > v(pick)), as in k4/referee/rfres_ref.py."""
import sys, gzip, json, collections, itertools
from multiprocessing import Pool

def sd(v, order, m):
    taken, Y = set(), [None] * len(v)
    for a in order:
        best = max((g for g in v[a] if g not in taken), key=lambda g: v[a][g], default=None)
        if best is not None: Y[a] = best; taken.add(best)
    return tuple(Y)

def nu(v, m):
    match = {}
    def aug(a, seen):
        for g in v[a]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen): match[g] = a; return True
        return False
    return sum(aug(a, set()) for a in range(len(v)))

def frozen(v, Y, a):
    return Y[a] is not None and any(i != a and v[i].get(Y[a], 0) > v[i].get(Y[i], 0) for i in range(len(v)))

def threatened(v, a, J, t):
    S = [g for g in J]
    if len(S) < 2: return False
    tot = sum(v[a].get(g, 0) for g in S)
    return any(tot - v[a].get(h, 0) > t for h in S)

def job(args):
    sets, starts, m = args
    C = collections.Counter()
    for s in starts:
        v = [dict(zip(S, vals)) for S, vals in zip(sets, s['vals'])]
        n = len(v); Y = tuple(s['picks']); N = nu(v, m)
        privtop = [a for a in range(n) if sum(max(v[a], key=v[a].get) in S for S in sets) == 1]
        C['starts with a private-top agent'] += bool(privtop)
        rec = [u for u in range(n) if Y[u] is not None and not frozen(v, Y, u)]
        for u in rec:
            seen = set()
            for rest in itertools.permutations([i for i in range(n) if i != u]):
                Yp = sd(v, (u,) + rest, m)
                if Yp in seen: continue
                seen.add(Yp)
                if sum(x is not None for x in Yp) != N: C['u-first pick vectors, not maximum'] += 1; continue
                J = set(range(m)) - {x for x in Yp if x is not None}
                U = [a for a in range(n) if not frozen(v, Yp, a)]
                DT = [a for a in range(n) if frozen(v, Yp, a) and threatened(v, a, J, v[a][Yp[a]])]
                C['class |U\'|=%d |D_T\'|=%d' % (len(U), len(DT))] += 1
                C['u-first max pick vectors'] += 1
                C['changed agents %d' % sum(Yp[a] != Y[a] for a in range(n))] += 1
    return C

if __name__ == '__main__':
    for path in sys.argv[1:]:
        d = json.load(gzip.open(path))
        tasks = []
        for H in d['hypergraphs']:
            m = 1 + max(g for S in H['sets'] for g in S)
            st = H['starts']
            for i in range(0, len(st), 2000): tasks.append((H['sets'], st[i:i + 2000], m))
        T = collections.Counter()
        with Pool(4) as pool:
            for C in pool.imap_unordered(job, tasks): T.update(C)
        print(path)
        for k, x in sorted(T.items()): print('   %-50s %d' % (k, x))
