"""OT1 and OT-omega in DE's general core case (every agent values exactly three goods, strictly balanced; any number
of private goods; disconnected allowed; D dead goods), exhaustively: one representative per isomorphism class of
hypergraph (gen_all.gen, canonical form over agent permutations), every ranking profile, the drafts of every order.
Completion test: lbtest.lb2 (exact on DE states).  Hard = the draft fails it.
  OT1     : some DE trade leads to a state that passes lb2 (if not: general chains, exhaustive completion)
  OT-omega: every DE trade of least omega does
    python3 k4/k3oc1/oc1_general.py N DEAD [SHARD NSHARDS]"""
import sys, os, json, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, completion, chains, vals
from de_moves import de_trades
from lbtest import lb2, parts
from gen_all import gen
from oc1_fast import drafts
from oc1_k3 import profiles

def canon(sets, n):
    m = 1 + max(max(s) for s in sets)
    inc = [[a for a in range(n) if g in sets[a]] for g in range(m)]
    return min(tuple(sorted(tuple(sorted(p[a] for a in I)) for I in inc)) for p in itertools.permutations(range(n)))

if __name__ == '__main__':
    n, dead = int(sys.argv[1]), int(sys.argv[2])
    shard, nsh = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 1)
    reps = {}
    for sets, m in gen(n):
        reps.setdefault(canon(sets, n), (sets, m))
    reps = [reps[k] for k in sorted(reps)]
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/k3oc1/oc1_general.py', *sys.argv[1:], '(%d classes)' % len(reps), flush=True)
    for ci, (sets, m) in enumerate(reps):
        if ci % nsh != shard: continue
        m2 = m + dead; C['hypergraphs'] += 1
        for rk in profiles(sets, 0, None):
            C['profiles'] += 1
            for Y in drafts(rk, n):
                C['distinct drafts'] += 1; b = base_of(Y, m2)
                if lb2(rk, m2, b): continue
                C['hard'] += 1
                mv = de_trades(rk, m2, b)
                ok = [bool(lb2(rk, m2, nb)) for nb, d in mv]
                if not any(ok):
                    V = vals(rk)
                    g = any(completion(rk, m2, nb, 1, V) is not None for nb, d in chains(rk, m2, b, V))
                    C['OT1 FAILS; OC1 by a general chain %s' % g] += 1
                    print('OT1FAIL', json.dumps([list(r) for r in rk]), m2, 'picks', Y, 'general chain repairs', g, flush=True)
                    continue
                om = [(lambda P: len(P[1]) - len(P[5]))(parts(rk, m2, nb)) for nb, d in mv]
                if not all(o for o, w in zip(ok, om) if w == min(om)):
                    C['OT-omega FAILS'] += 1
                    print('OMEGAFAIL', json.dumps([list(r) for r in rk]), m2, 'picks', Y, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
