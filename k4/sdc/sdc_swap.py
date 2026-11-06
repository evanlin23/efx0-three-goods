"""Contest swaps.  For an order pi whose SD outcome does not extend, a *contest swap* moves a needer j of a frozen agent x
(j prefers x's pick to its own) to just before x in pi; the SD outcome is recomputed (plain orders).  Questions:
(1) does some single contest swap give an extendable outcome?  (2) does the greedy walk "apply some swap that extends,
else any swap, never revisiting an outcome" reach an extendable outcome, and in how many steps?

    python3 k4/sdc/sdc_swap.py screen RUNS SEED"""
import sys, os, json, random, collections
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdf import frozen


def swaps(E, order):
    Y = sd(E, order)[0]; pos = {a: t for t, a in enumerate(order)}
    out = []
    for x in frozen(E, Y):
        for j in range(E.n):
            if j == x or pos[j] < pos[x]:
                continue
            vy = E.v[j][Y[j]] if Y[j] is not None else 0
            if E.v[j].get(Y[x], 0) > vy:
                o = [a for a in order if a != j]; o.insert(o.index(x), j); out.append(tuple(o))
    return out


if __name__ == '__main__':
    R, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/sdc_swap.py', *sys.argv[1:])
    cwd = os.getcwd(); os.chdir(_paths.DE4)
    from ss_screen import screen_set
    S = screen_set(); os.chdir(cwd)
    for name, I in S:
        if I.n > 7: continue
        E = Enc(I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m); cache = {}
        def ext(o):
            Y = tuple(sd(E, o)[0])
            if Y not in cache: cache[Y] = completable(E, list(Y))
            return cache[Y]
        for t in range(R):
            order = tuple(rng.sample(range(E.n), E.n))
            if ext(order): continue
            C['bad orders'] += 1
            sw = swaps(E, order)
            C['some single swap extends'] += any(ext(o) for o in sw)
            # walk
            seen = {tuple(sd(E, order)[0])}; o = order; steps = 0; ok = False
            while steps < 3 * E.n:
                sw = swaps(E, o)
                good = [p for p in sw if ext(p)]
                if good: ok = True; steps += 1; break
                fresh = [p for p in sw if tuple(sd(E, p)[0]) not in seen]
                if not fresh: break
                o = rng.choice(fresh); seen.add(tuple(sd(E, o)[0])); steps += 1
            C['walk reaches an extendable outcome'] += ok
            if ok: C['walk steps %d' % steps] += 1
            elif C['shown'] < 3: C['shown'] += 1; print('STUCK', name, json.dumps((I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], order)))
    for k in sorted(C, key=str): print(k, C[k])
