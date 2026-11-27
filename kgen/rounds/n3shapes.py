"""n = 3, strictly positive values: which one-round shapes reach a complete EFX allocation from each start
(kgen/rounds.md §5).  A round at n = 3 has at most one chain of length t >= 1 (plus t = 0 moves, which change nothing
for the free completion), so the shapes are
  K   keep: every agent keeps its pick                                     (no chain)
  H   hand-off x0 -> x1, x1's pick released (anywhere), z keeps its pick    (t = 1)
  S   swap x0 -> x1 with x0 taking y_x1 (a 2-ring)                          (t = 1)
  P3  chain x0 -> x1 -> x2, y_x2 released                                   (t = 2)
  R3  rotation x0 -> x1 -> x2 with x0 taking y_x2 (a 3-ring)                (t = 2)
Gains (positive values, H's maximal): receiver b of y_p: v_b(y_p) + v_b(X_b cap J) > v_b(y_b); start x0:
v_x0(X_x0 cap J) + [ring] v_x0(y_end) > v_x0(y_x0).  This is a third, separately written implementation of the
round characterization (rnd.c, kgen/rounds.md §1); 'any shape' is cross-checked against rnd.c's RNDF count.

    python3 kgen/rounds/n3shapes.py rand T SEED mmin mmax       random families (families.KINDS)
    python3 kgen/rounds/n3shapes.py file LOG                    the final instances of a stress.py climb log
"""
import sys, os, json, random, re, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rndlib, families

SHAPES = ['K', 'H', 'S', 'P3', 'R3']


def sd(V, order):
    left = set(range(len(V[0]))); y = [None] * len(V)
    for a in order:
        g = max(sorted(left), key=lambda h: V[a][h]); y[a] = g; left.discard(g)
    return y


def shapes_of(V, X, y):
    n = 3; m = len(V[0]); own = [None] * m
    for i, B in enumerate(X):
        for g in B: own[g] = i
    J = set(range(m)) - set(y)
    loc = [own[y[a]] for a in range(n)]
    vj = [sum(V[i][g] for g in X[i] if g in J) for i in range(n)]
    out = set()
    if all(loc[a] == a for a in range(n)): out.add('K')
    for x0, x1 in itertools.permutations(range(n), 2):
        z = 3 - x0 - x1
        if loc[x0] != x1 or loc[z] != z: continue
        if not (V[x1][y[x0]] + vj[x1] > V[x1][y[x1]]): continue
        ring = loc[x1] == x0
        if vj[x0] + (V[x0][y[x1]] if ring else 0) > V[x0][y[x0]]: out.add('S' if ring else 'H')
    for x0, x1, x2 in itertools.permutations(range(n), 3):
        if loc[x0] != x1 or loc[x1] != x2: continue
        if not (V[x1][y[x0]] + vj[x1] > V[x1][y[x1]]): continue
        if not (V[x2][y[x1]] + vj[x2] > V[x2][y[x2]]): continue
        ring = loc[x2] == x0
        if vj[x0] + (V[x0][y[x2]] if ring else 0) > V[x0][y[x0]]: out.add('R3' if ring else 'P3')
    return out


def efx(V, X):
    for i in range(len(X)):
        o = sum(V[i][g] for g in X[i])
        for j in range(len(X)):
            if i != j and X[j] and sum(V[i][g] for g in X[j]) - min(V[i][g] for g in X[j]) > o: return False
    return True


def classify(V):
    """per distinct start: Counter of shapes over EFX allocations (each X counted once per shape it admits)"""
    L, c = rndlib.list_efx(V)
    m = len(V[0])
    Xs = []
    for own in L:
        X = [[g for g in range(m) if own[g] == i] for i in range(3)]
        assert efx(V, X)        # raw re-check of rnd.c's enumeration
        Xs.append(X)
    res, _ = rndlib.analyze(V)
    out = {}
    for r in res:
        y = list(r['picks']); C = collections.Counter(); anyc = 0
        for X in Xs:
            s = shapes_of(V, X, y)
            for k in s: C[k] += 1
            if s: anyc += 1
        assert anyc == r['counts']['RNDF'], ('mismatch with rnd.c', V, y, anyc, r['counts']['RNDF'])
        out[tuple(y)] = (r['order'], C)
    return out


def need(C):
    if C['K']: return 'K'
    if C['H'] or C['S']:
        return 'H/S' if (C['H'] and C['S']) else ('H only' if C['H'] else 'S only')
    if C['P3'] or C['R3']:
        return '3-agent: ' + ('P3+R3' if (C['P3'] and C['R3']) else ('P3 only' if C['P3'] else 'R3 only'))
    return 'NONE'


def run(instances, label):
    T = collections.Counter(); ex = {}
    for V in instances:
        for y, (o, C) in classify(V).items():
            k = need(C); T[k] += 1
            if k.startswith('3-agent') or k == 'NONE':
                ex.setdefault(k, (V, o, dict(C)))
    print(label, dict(T))
    for k, e in ex.items(): print('  example', k, json.dumps(e[0]), 'order', e[1], e[2])
    return T


if __name__ == '__main__':
    print('$ python3 kgen/rounds/n3shapes.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'rand':
        T, seed, mmin, mmax = map(int, sys.argv[2:6]); rng = random.Random(seed)
        tot = collections.Counter()
        for kind in families.KINDS:
            insts = [families.gen(kind, 3, rng.randint(mmin, mmax), rng) for _ in range(T)]
            tot += run(insts, kind)
        print('TOTAL', dict(tot))
    else:
        insts = []
        for f in sys.argv[2:]:
            for line in open(f):
                mm = re.search(r'vals (\[\[.*?\]\])', line)
                if line.startswith('round') and mm: insts.append(json.loads(mm.group(1)))
        run(insts, 'climbed (%d instances)' % len(insts))
