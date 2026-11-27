"""OC1 at k = 3 with DE trades only, fast: from the draft of every order, the one-absorber completion test lb2 (exact on
DE states; cross-checked against the exhaustive test, xcheck_lb1.py) passes, or passes after one DE trade.  Also
records which selection rules pick a repairing trade.
    python3 k4/k3oc1/oc1_lb.py SOURCE [PROFILES SEED] [dead=D] [test=exact|simple|simple+up]"""
import sys, os, json, random, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of
from de_moves import de_trades
from lbtest import lb2, lb_simple
from rules import score, nfree
from oc1_k3 import hypergraphs, profiles

if __name__ == '__main__':
    TEST = next((x[5:] for x in sys.argv[1:] if x.startswith('test=')), 'exact')
    lb1 = {'exact': lb2, 'simple': lambda rk, m, b: lb_simple(rk, m, b), 'simple+up': lambda rk, m, b: lb_simple(rk, m, b, True)}[TEST]
    args = [x for x in sys.argv[1:] if not x.startswith('dead=') and not x.startswith('test=')]
    dead = int(next((x[5:] for x in sys.argv[1:] if x.startswith('dead=')), 0))
    src = args[0]; P = int(args[1]) if len(args) > 1 else 0; seed = int(args[2]) if len(args) > 2 else 1
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/k3oc1/oc1_lb.py', *sys.argv[1:], flush=True)
    for sets, m in hypergraphs(src, rng):
        m2 = m + dead; n = len(sets); C['hypergraphs'] += 1
        for rk in profiles(sets, P, rng):
            C['profiles'] += 1; seen = {}
            for o in itertools.permutations(range(n)):
                Y = tuple(sd(rk, m2, o)); C['starts'] += 1
                if Y not in seen:
                    b = base_of(Y, m2)
                    if lb1(rk, m2, b): seen[Y] = 'draft completes'
                    else:
                        mv = de_trades(rk, m2, b); rep = [bool(lb1(rk, m2, nb)) for nb, d in mv]
                        if not any(rep):
                            seen[Y] = 'NO DE TRADE REPAIRS'
                            print('NODE', json.dumps([list(r) for r in rk]), m2, 'order', o, 'picks', Y, flush=True)
                        else:
                            sc = [score(rk, nb) for nb, d in mv]; best = max(sc)
                            okm = all(r for r, s in zip(rep, sc) if s == best)
                            seen[Y] = 'one DE trade repairs; every max-score trade repairs %s' % okm
                            if not okm:
                                print('MAXFAIL', json.dumps([list(r) for r in rk]), m2, 'order', o, 'picks', Y, flush=True)
                            print('HARD', json.dumps([list(r) for r in rk]), m2, 'order', o, 'picks', Y, 'chain', flush=True)
                C[seen[Y]] += 1
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
