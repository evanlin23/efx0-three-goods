"""Two agents, any k: which shapes of CODE-reachable EFX0 allocation (kgen/n3.md §1, adapted to n = 2) always exist?
Order (first, second) = (1, 2) after renaming.  Shapes of an EFX0 allocation X with picks y1, y2:
  A1: y1 in X1, y2 in X2, |X1 \\ R1| <= 1     (agent 1 adds the junk it values, agent 2 absorbs)
  A2: y1 in X1, y2 in X2, |X2 \\ R2| <= 1     (agent 2 adds the junk it values, agent 1 absorbs)
  B : chain 1 -> 2 (agent 2 holds y1), C: chain 2 -> 1 (agent 1 holds y2), each with its gains and absorber count.

    python3 kgen/shapes2.py SEED N MMIN MMAX"""
import sys, random, itertools, collections, json
from oc2 import efx0, sd, gen


def shapes(v, o):
    m = len(v[0]); a, b = o
    y = sd(v, o); R = [{g for g in range(m) if v[i][g] > 0} for i in range(2)]
    J = set(range(m)) - {g for g in y if g is not None}
    val = lambda i, S: sum(v[i][g] for g in S)
    out = set()
    for asg in itertools.product(range(2), repeat=m):
        X = [{g for g in range(m) if asg[g] == i} for i in range(2)]
        if not efx0(v, X): continue
        own = all(y[i] is None or y[i] in X[i] for i in range(2))
        if own:
            if len(X[a] - R[a]) <= 1: out.add('A1')
            if len(X[b] - R[b]) <= 1: out.add('A2')
        for x0, nm in ((a, 'B'), (b, 'C')):
            x1 = 1 - x0
            if y[x0] is None or y[x0] not in X[x1]: continue
            H1 = X[x1] & J & R[x1]
            if v[x1][y[x0]] + val(x1, H1) <= (v[x1][y[x1]] if y[x1] is not None else 0): continue
            pool = J | ({y[x1]} if y[x1] is not None else set())
            H0 = X[x0] & pool & R[x0]
            if val(x0, H0) <= v[x0][y[x0]]: continue
            C0 = X[x0] - H0; C1 = X[x1] - H1 - {y[x0]}
            if len(C0) <= 1 or len(C1) <= 1: out.add(nm)
    return out


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = {}
    fam = {'A1 or B': {'A1', 'B'}, 'A1 or C': {'A1', 'C'}, 'A2 or B': {'A2', 'B'}, 'A2 or C': {'A2', 'C'},
           'A1 or A2': {'A1', 'A2'}, 'B or C': {'B', 'C'}, 'A1 or B or C': {'A1', 'B', 'C'}, 'A2 or B or C': {'A2', 'B', 'C'},
           'any': {'A1', 'A2', 'B', 'C'}}
    print('$ python3 kgen/shapes2.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); v = gen(rng, m)
        for o in [(0, 1), (1, 0)]:
            S = shapes(v, o); C['starts'] += 1
            for k, F in fam.items():
                if S & F: C[k] += 1
                elif k not in ex: ex[k] = (v, o, sorted(S))
    for k in fam: print('%-15s %d / %d' % (k, C[k], C['starts']))
    for k, e in ex.items(): print('uncovered', k, json.dumps(e))
