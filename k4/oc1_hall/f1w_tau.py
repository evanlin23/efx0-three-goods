"""f = 1 with several wanters (k4/oc1_hall.md §11): tau(o) = the fewest junk goods of x that must be kept out of
W_o = {Y_o} + J so that x is not threatened.  Claim tested: if n >= 4 and some unfrozen owner o has tau(o) <= 1, the
picks have an S* completion (SAT test of big_sstar.sstar_sat).  Instances: random strict profiles of the given cores,
or random hypergraphs ("big"), sampled orders.

    python3 k4/oc1_hall/f1w_tau.py cores:FILE N SEED ORDERS | big:N COUNT SEED ORDERS
"""
import sys, os, json, random, itertools, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, threatened
from big_sstar import sstar_sat, instances
from sdclib import Enc


def tau(I, P, o, x):
    W = [P.Y[o]] + P.J if P.Y[o] is not None else list(P.J)
    for r in range(0, 4):
        for H in itertools.combinations([g for g in P.J if g in I.R[x]], r):
            if not threatened(I, x, P.pv[x], [g for g in W if g not in H]): return r
    return 4


if __name__ == '__main__':
    spec = sys.argv[1]; seed = int(sys.argv[3]); NORD = int(sys.argv[4]); rng = random.Random(seed)
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/f1w_tau.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in instances(spec, rng):
        I = Inst(sets, vals, m, name); E = None; n = I.n; seen = set()
        for _ in range(NORD):
            od = rng.sample(range(n), n); Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.F) != 1 or len(P.W[P.F[0]]) < 2: continue
            x = P.F[0]; U = [o for o in range(n) if o != x]
            tmin = min(tau(I, P, o, x) for o in U)
            if E is None: E = Enc(sets, vals, m)
            base = base_of_picks(I, Y); ok = sstar_sat(E, I, base)
            C['f = 1, several wanters: min tau %d' % tmin] += 1
            C['  min tau %d, picks complete %s' % (tmin, ok)] += 1
            if tmin <= 1 and not ok:
                print('CLAIM FAILS', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, 'x', x, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
