"""Random stress test of Theorem candidate OT (k = 3): the draft passes the simple test, or every max-score DE trade
leads to a state that passes it.  Random 3-uniform hypergraphs (n agents, m goods, plus dead goods), random
rankings, random orders.  Prints every failure.
    python3 k4/k3oc1/rand_oc1.py N_MIN N_MAX COUNT SEED"""
import sys, os, json, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of
from de_moves import de_trades
from lbtest import lb_simple, lb2
from rules import score
nmin, nmax, cnt, seed = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
print('$ python3 k4/k3oc1/rand_oc1.py', *sys.argv[1:], flush=True)
for it in range(cnt):
    n = rng.randint(nmin, nmax); m = rng.randint(n + 1, 2 * n + 1); dead = rng.choice([0, 0, 0, 1, 2])
    rk = [tuple(rng.sample(range(m), 3)) for _ in range(n)]; M = m + dead
    order = list(range(n)); rng.shuffle(order)
    b = base_of(sd(rk, M, order), M); C['starts'] += 1
    if lb_simple(rk, M, b): C['draft passes'] += 1; continue
    mv = de_trades(rk, M, b)
    if not mv:
        C['NO TRADE'] += 1; print('NOTRADE', json.dumps(rk), M, order, flush=True); continue
    best = max(score(rk, nb) for nb, d in mv)
    ok = [bool(lb_simple(rk, M, nb)) for nb, d in mv if score(rk, nb) == best]
    if all(ok): C['every max-score trade passes'] += 1
    else:
        any_ok = any(lb_simple(rk, M, nb) for nb, d in mv)
        C['MAX-SCORE FAILS; some trade passes %s' % any_ok] += 1
        print('MAXFAIL', json.dumps(rk), M, order, 'some trade passes', any_ok, flush=True)
for k in sorted(C): print(k, C[k])
print('time %.0f s' % (time.time() - t0))
