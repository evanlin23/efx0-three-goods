"""Descent over orders.  deficit(Y) = least number of goods left out over partial EFX0 allocations X with Y_i in X_i
(0 iff Y extends).  Neighbours of an order: move one agent to any other position (plain SD).  Question: does every order
with deficit > 0 have a neighbour of smaller deficit (no bad local minimum)?

    python3 k4/sdc/sdc_descent.py screen RUNS SEED"""
import sys, os, json, random, collections
import _paths
from sdclib import Enc
from sdc_orders import sd
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType


def deficit(E, Y, cache):
    key = tuple(Y)
    if key in cache: return cache[key]
    cl = list(E.cl)
    for i in range(E.n):
        if Y[i] is not None: cl.append([E.x[Y[i]][i]])
    pool = [E.x[g][E.n] for g in range(E.m)]
    best = None
    for d in range(E.m + 1):
        card = CardEnc.atmost(lits=pool, bound=d, top_id=E.top, encoding=EncType.seqcounter)
        S = Cadical153(bootstrap_with=cl + card.clauses); ok = S.solve(); S.delete()
        if ok: best = d; break
    cache[key] = best; return best


def neighbours(order):
    n = len(order)
    for a in range(n):
        for b in range(n):
            if a != b:
                o = list(order); x = o.pop(a); o.insert(b, x); yield tuple(o)


if __name__ == '__main__':
    R, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/sdc_descent.py', *sys.argv[1:])
    cwd = os.getcwd(); os.chdir(_paths.DE4)
    from ss_screen import screen_set
    S = screen_set(); os.chdir(cwd)
    for name, I in S:
        if I.n > 6: continue
        E = Enc(I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m); cache = {}
        seen = set()
        for t in range(R):
            order = tuple(rng.sample(range(E.n), E.n)); Y = tuple(sd(E, order)[0])
            if Y in seen: continue
            seen.add(Y)
            d = deficit(E, list(Y), cache)
            if d == 0: continue
            C['orders with deficit > 0'] += 1
            nd = min(deficit(E, sd(E, o)[0], cache) for o in neighbours(order))
            C['has a better neighbour'] += nd < d
            C['has a neighbour with deficit 0'] += nd == 0
            if nd >= d and C['shown'] < 3:
                C['shown'] += 1; print('LOCAL MIN', name, 'deficit', d, json.dumps((I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], order)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
