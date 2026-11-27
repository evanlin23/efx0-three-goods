"""E17: which deletions are safe for a black-box induction (k4/sd_induct.md §6)?

For an SD outcome Y and a set D of agents, ext(U) says the picks of I_U (U = N - D, with D's picks deleted; Lemma D)
have an EFX0 completion (free: any number of absorbers; or one-absorber).  A deletion class is *safe* if
ext(N - D) implies ext(N) for every Y and every D in the class.  Classes (W(j) = the agents wanting Y_j):
  both       : D = {u}, u holds its top and W(u) is empty
  first      : D = {u}, u holds its top (u can be first)
  last       : D = {u}, W(u) empty (u can be last)
  frozen+W   : D = {j} + W(j), j frozen
  frozen+w   : D = {j, w}, w in W(j)
  suffix     : D closed under wanters (i wants Y_j, j in D => i in D), |D| <= 2; these are the first agents of some order
  prefix     : D closed under wanted (i in D wants Y_j => j in D), |D| <= 2; the last agents of some order
Counts violations (ext(N - D) true, ext(N) false) per class, for free and one-absorber completions.

    python3 k4/sdind/e17_classes.py special|screen|suite|logs|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, delete, picks_base
from e1_delete import load


def ext(I, Y, U, maxabs, cache):
    key = (tuple(sorted(U)), maxabs)
    if key in cache: return cache[key]
    rest = [i for i in range(I.n) if i not in U]
    I2, amap, gmap = delete(I, rest, [Y[i] for i in rest if Y[i] is not None])
    Y2 = [None] * I2.n
    for a, b in amap.items(): Y2[b] = gmap[Y[a]] if Y[a] is not None else None
    J2, A2 = completions(I2, picks_base(I2, Y2), maxabs)
    cache[key] = len(A2) > 0
    return cache[key]


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e17_classes.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); seen = set(); C['instances'] += 1
        J0 = None
        for o_ in itertools.permutations(range(I.n)):
            Y = list(sd(I, o_)[0])
            if tuple(Y) in seen: continue
            seen.add(tuple(Y)); W = wanted_by(I, Y); cache = {}
            J = [g for g in range(I.m) if g not in Y]
            if I.n ** len(J) > 1_000_000: continue
            top = [Y[i] is not None and Y[i] == max(I.R[i], key=lambda h: (I.V[i, h], -h)) for i in range(I.n)]
            wants = {i: set(j for j in range(I.n) if i in W[j]) for i in range(I.n)}
            classes = collections.defaultdict(list)
            for u in range(I.n):
                if top[u] and not W[u]: classes['both'].append((u,))
                if top[u]: classes['first'].append((u,))
                if not W[u]: classes['last'].append((u,))
                if W[u]:
                    classes['frozen+W'].append(tuple(sorted({u} | set(W[u]))))
                    for w in W[u]: classes['frozen+w'].append(tuple(sorted((u, w))))
            for r in (1, 2):
                for D in itertools.combinations(range(I.n), r):
                    Ds = set(D)
                    if all(set(W[j]) <= Ds for j in Ds): classes['suffix'].append(D)
                    if all(wants[i] <= Ds for i in Ds): classes['prefix'].append(D)
            for mode, A in (('free', None), ('one-abs', 1)):
                full = ext(I, Y, range(I.n), A, cache)
                for cl, Ds in classes.items():
                    for D in set(Ds):
                        if len(D) >= I.n: continue
                        U = [i for i in range(I.n) if i not in D]
                        C['%s %s: cases' % (mode, cl)] += 1
                        if ext(I, Y, U, A, cache) and not full:
                            C['%s %s: VIOLATIONS' % (mode, cl)] += 1
                            if shown[(mode, cl)] < 1:
                                shown[(mode, cl)] += 1
                                print('VIOLATION', mode, cl, name, json.dumps((sets, vals)), 'picks', Y, 'D', D, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
