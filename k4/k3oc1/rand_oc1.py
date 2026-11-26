"""Random stress test of Theorem candidate OT (k = 3): the draft passes the simple test, or every max-score DE trade
leads to a state that passes it.  Random 3-uniform hypergraphs (n agents, m goods, plus dead goods), random
rankings, random orders.  Prints every failure.
    python3 k4/k3oc1/rand_oc1.py N_MIN N_MAX COUNT SEED [M_FACTOR (m <= M_FACTOR * n, default 2)]"""
import sys, os, json, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of
from de_moves import de_trades
from lbtest import lb_simple, lb2, parts
from rules import score
nmin, nmax, cnt, seed = map(int, sys.argv[1:5]); MF = float(sys.argv[5]) if len(sys.argv) > 5 else 2.0; rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
print('$ python3 k4/k3oc1/rand_oc1.py', *sys.argv[1:], flush=True)
for it in range(cnt):
    n = rng.randint(nmin, nmax); m = rng.randint(n + 1, max(n + 1, int(MF * n))); dead = rng.choice([0, 0, 0, 1, 2])
    rk = [tuple(rng.sample(range(m), 3)) for _ in range(n)]; M = m + dead
    order = list(range(n)); rng.shuffle(order)
    b = base_of(sd(rk, M, order), M); C['starts'] += 1
    if lb_simple(rk, M, b): C['draft passes'] += 1; continue
    mv = de_trades(rk, M, b)
    if not mv:
        C['NO TRADE'] += 1; print('NOTRADE', json.dumps(rk), M, order, flush=True); continue
    sc = [score(rk, nb) for nb, d in mv]; om = [(lambda P: len(P[1]) - len(P[5]))(parts(rk, M, nb)) for nb, d in mv]
    simp = [bool(lb_simple(rk, M, nb)) for nb, d in mv]
    C['some trade passes simple %s' % any(simp)] += 1
    if not any(simp): print('NOTRADE-SIMPLE', json.dumps(rk), M, order, flush=True)
    for rule, keys in (('max score', sc), ('least omega', [-w for w in om])):
        sel = [i for i, k in enumerate(keys) if k == max(keys)]
        if all(simp[i] for i in sel): C[rule + ': simple'] += 1
        elif all(lb2(rk, M, mv[i][0]) for i in sel): C[rule + ': exact only'] += 1
        else: C[rule + ': FAILS'] += 1; print('RULEFAIL', rule, json.dumps(rk), M, order, flush=True)
for k in sorted(C): print(k, C[k])
print('time %.0f s' % (time.time() - t0))
