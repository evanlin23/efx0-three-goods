"""SD-C: is there a serial-dictatorship order whose picks extend, by distributing the unpicked goods, to an EFX0 allocation?
mode 'plain': SD in the order pi; mode 'r1': agents with fewer remaining goods first (R1 priority), pi breaks ties / chooses
insertion agents."""
import sys, os, json, itertools, random
from sdclib import Enc, decode, efx0
from pysat.solvers import Cadical153
def sd(E, order, r1=False):
    left = set(range(E.m)); Y = [None] * E.n; done = [False] * E.n
    rank = {a: k for k, a in enumerate(order)}
    for _ in range(E.n):
        cand = [i for i in range(E.n) if not done[i]]
        if r1:
            def key(i):
                rem = sum(1 for g in E.R[i] if g in left)
                return (0 if rem < len(E.R[i]) else 1, rank[i])
            i = min(cand, key=key)
        else:
            i = min(cand, key=lambda a: rank[a])
        done[i] = True
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
    return Y, left
def completable(E, Y):
    cl = list(E.cl)
    for g in range(E.m): cl.append([-E.x[g][E.n]])
    for i in range(E.n):
        if Y[i] is not None: cl.append([E.x[Y[i]][i]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok
def test(sets, vals, m, mode, maxorders=5040, rng=None):
    E = Enc(sets, vals, m)
    seen = set(); tried = 0
    orders = itertools.permutations(range(E.n)) if E.n <= 7 else (rng.sample(range(E.n), E.n) for _ in range(maxorders))
    for order in orders:
        Y, J = sd(E, order, mode == 'r1')
        key = tuple(Y)
        if key in seen: continue
        seen.add(key); tried += 1
        if completable(E, Y): return True, order, tried
    return False, None, tried
if __name__ == '__main__':
    import _paths; os.chdir(_paths.DE4)
    from ss_screen import screen_set
    mode = sys.argv[1]; c = [0, 0]
    for name, I in screen_set():
        vals = [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)]
        ok, order, tried = test(I.sets, vals, I.m, mode)
        c[0] += 1; c[1] += (not ok)
        if not ok: print('NO', name, I.n, I.m, 'distinct SD outcomes', tried, json.dumps((I.sets, vals)), flush=True)
    print(mode, 'instances', c[0], 'no SD order works', c[1])
