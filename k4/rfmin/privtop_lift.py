"""RF-PRIV probe (k4/RFMIN.md §2): at stored OC1^max-failing starts whose receiver u picked a PRIVATE good p that is not
its top, raise v_u(p) above u's other goods (keeping the type strict and balanced) and re-check OC1 at the same picks.
The picks are unchanged (nobody else values p, and u's choice is p either way). If RF holds, OC1 must hold after the
lift (Corollary RF-PRIV). Reports what repairs: the picks complete, the picks complete with u as absorber (Lemma ABS's
shape), or one move.  Usage: privtop_lift.py FILE.json.gz STRIDE"""
import sys, os, gzip, json, collections, itertools, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sdc'))
from oc1_mc2_rand import Inst
from multiprocessing import Pool

def strict_balanced(x):
    if 2 * max(x) >= sum(x): return False
    sums = collections.defaultdict(list)
    for r in range(1, len(x) + 1):
        for T in itertools.combinations(range(len(x)), r): sums[sum(x[k] for k in T)].append(set(T))
    return all(not any(not (a & b) for a, b in itertools.combinations(L, 2)) for L in sums.values())

def lift(vals, k):
    """vals with entry k raised just above the others' maximum (scaled to keep integers), strict and balanced."""
    for scale in (4, 8, 16, 32):
        base = [scale * x for x in vals]
        for bump in range(1, 4 * scale):
            y = list(base); y[k] = max(b for i, b in enumerate(base) if i != k) + bump
            if strict_balanced(y): return y
    return None

def job(args):
    sets, starts = args
    C = collections.Counter()
    for s in starts:
        Y = s['picks']; n = len(sets)
        deg = collections.Counter(g for S in sets for g in S)
        for u in s['receivers']:
            p = Y[u]
            if p is None or deg[p] != 1: continue
            vals = [list(v) for v in s['vals']]
            k = sets[u].index(p)
            if vals[u][k] == max(vals[u]): C['already top (impossible)'] += 1; continue
            y = lift(vals[u], k)
            if y is None: C['no strict balanced lift'] += 1; continue
            vals[u] = y
            I = Inst(sets, vals)
            assert tuple(I.sd(s['orders'][0])) == tuple(Y), 'picks changed'
            r = I.check(tuple(Y))
            C['lifted: ' + r] += 1
    return C

if __name__ == '__main__':
    path, stride = sys.argv[1], int(sys.argv[2])
    d = json.load(gzip.open(path))
    tasks = []
    for H in d['hypergraphs']:
        deg = collections.Counter(g for S in H['sets'] for g in S)
        st = [s for s in H['starts'] if any(deg[s['picks'][u]] == 1 for u in s['receivers'] if s['picks'][u] is not None)]
        st = st[::stride]
        for i in range(0, len(st), 50): tasks.append((H['sets'], st[i:i + 50]))
    T = collections.Counter()
    with Pool(4) as pool:
        for C in pool.imap_unordered(job, tasks): T.update(C)
    print(path, 'stride', stride)
    for k, x in sorted(T.items()): print('  %-40s %d' % (k, x))
