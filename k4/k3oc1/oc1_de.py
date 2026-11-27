"""Theorem candidate (k = 3): from the draft of every order, Draft and Exchange's own finishing test passes, or it
passes after the single DE trade of largest total score (every such trade).  Exhaustive over profiles and orders.

    python3 k4/k3oc1/oc1_de.py SOURCE [PROFILES SEED] [dead=D]     (SOURCE as in oc1_k3.py)"""
import sys, os, json, random, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of, completion, vals
from de_moves import de_trades, de_can_finish
from rules import score
from oc1_k3 import hypergraphs, profiles

if __name__ == '__main__':
    args = [x for x in sys.argv[1:] if not x.startswith('dead=')]
    dead = int(next((x[5:] for x in sys.argv[1:] if x.startswith('dead=')), 0))
    src = args[0]; P = int(args[1]) if len(args) > 1 else 0; seed = int(args[2]) if len(args) > 2 else 1
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/k3oc1/oc1_de.py', *sys.argv[1:], flush=True)
    for sets, m in hypergraphs(src, rng):
        m2 = m + dead; n = len(sets); C['hypergraphs'] += 1
        for rk in profiles(sets, P, rng):
            C['profiles'] += 1; seen = {}
            for o in itertools.permutations(range(n)):
                Y = tuple(sd(rk, m2, o)); C['starts'] += 1
                if Y not in seen:
                    b = base_of(Y, m2)
                    if de_can_finish(rk, m2, b): seen[Y] = 'finish at draft'
                    else:
                        mv = de_trades(rk, m2, b)
                        if not mv: seen[Y] = 'NO TRADE'
                        else:
                            best = max(score(rk, nb) for nb, d in mv)
                            sel = [(nb, d) for nb, d in mv if score(rk, nb) == best]
                            okb = [bool(de_can_finish(rk, m2, nb)) for nb, d in sel]
                            oka = any(de_can_finish(rk, m2, nb) for nb, d in mv)
                            seen[Y] = 'max-score trade: all %s any %s; some trade %s' % (all(okb), any(okb), oka)
                            if not all(okb):
                                print('BAD', json.dumps([list(r) for r in rk]), m2, 'order', o, 'picks', Y,
                                      [d for (nb, d), k in zip(sel, okb) if not k][:3], flush=True)
                C[seen[Y]] += 1
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
