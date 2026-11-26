"""OT at k = 3, exhaustive over profiles, with the distinct drafts of a profile enumerated directly: serial
dictatorship over every order, merged by (agents processed, their picks) -- the drafts of all n! orders without
running n! orders.  For each draft failing the simple test (lbtest.lb_simple): is there a DE trade after which it
passes, and does every max-score DE trade pass?  Shard by core index for parallel runs.
    python3 k4/k3oc1/oc1_fast.py SOURCE SHARD NSHARDS [dead=D]"""
import sys, os, json, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of
from de_moves import de_trades
from lbtest import lb_simple
from rules import score
from oc1_k3 import hypergraphs, profiles

def drafts(rk, n):
    out = set(); seen = set()
    def go(done, taken, Y):
        key = (done, tuple(Y))
        if key in seen: return
        seen.add(key)
        if done == (1 << n) - 1: out.add(tuple(Y)); return
        for i in range(n):
            if done >> i & 1: continue
            g = next((h for h in rk[i] if not taken >> h & 1), None)
            Y2 = list(Y); Y2[i] = g
            go(done | (1 << i), taken | ((1 << g) if g is not None else 0), Y2)
    go(0, 0, [None] * n)
    return out

if __name__ == '__main__':
    dead = int(next((x[5:] for x in sys.argv[1:] if x.startswith('dead=')), 0))
    args = [x for x in sys.argv[1:] if not x.startswith('dead=')]
    src, shard, nsh = args[0], int(args[1]), int(args[2])
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/k3oc1/oc1_fast.py', *sys.argv[1:], flush=True)
    for ci, (sets, m) in enumerate(hypergraphs(src, None)):
        if ci % nsh != shard: continue
        m2 = m + dead; n = len(sets); C['hypergraphs'] += 1
        for rk in profiles(sets, 0, None):
            C['profiles'] += 1
            for Y in drafts(rk, n):
                C['distinct drafts'] += 1
                b = base_of(Y, m2)
                if lb_simple(rk, m2, b): continue
                C['hard'] += 1
                mv = de_trades(rk, m2, b)
                ok = [bool(lb_simple(rk, m2, nb)) for nb, d in mv]
                if not any(ok):
                    C['NO DE TRADE REPAIRS'] += 1
                    print('NODE', json.dumps([list(r) for r in rk]), m2, 'picks', Y, flush=True); continue
                best = max(score(rk, nb) for nb, d in mv)
                if not all(o for o, (nb, d) in zip(ok, mv) if score(rk, nb) == best):
                    C['MAX-SCORE FAILS'] += 1
                    print('MAXFAIL', json.dumps([list(r) for r in rk]), m2, 'picks', Y, flush=True)
        print('core', ci, dict(C), '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
