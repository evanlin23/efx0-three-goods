"""Cross-check of the exact test lbtest.lb2 against the exhaustive one-absorber completion (k3lib.completion) on the
class of statement (P) (k4/k3_oc1.md §11): agents valuing one, two or three goods, every hypergraph class
(perfect_small.gen_mixed), every ranking, every perfect draft, and the states after every DE trade from it.
    python3 k4/k3oc1/mixed_check.py N [DEAD [SHARD NSHARDS]]"""
import sys, os, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, completion
from lbtest import lb2
from de_moves import de_trades
from oc1_fast import drafts
from perfect_small import gen_mixed, canon
n = int(sys.argv[1]); dead = int(sys.argv[2]) if len(sys.argv) > 2 else 0
shard, nsh = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 1)
reps = {}
for sets, m in gen_mixed(n): reps.setdefault(canon(sets, n), (sets, m))
C = collections.Counter(); t0 = time.time()
print('$ python3 k4/k3oc1/mixed_check.py', *sys.argv[1:], '(%d classes)' % len(reps), flush=True)
for ci, key in enumerate(sorted(reps)):
    if ci % nsh != shard: continue
    sets, m = reps[key]; m2 = m + dead
    for rk in itertools.product(*[list(itertools.permutations(s)) for s in sets]):
        for Y in drafts(rk, n):
            if any(g is None for g in Y): continue
            b = base_of(Y, m2)
            states = [('draft', b)] + [('trade', nb) for nb, d in de_trades(rk, m2, b)]
            for kind, st in states:
                a = bool(lb2(rk, m2, st)); e = completion(rk, m2, st) is not None
                C['%s: lb2 %s, exhaustive %s' % (kind, a, e)] += 1
                if a != e: print('MISMATCH', kind, [list(r) for r in rk], m2, 'base', st, flush=True)
for k in sorted(C): print(k, C[k])
print('time %.0f s' % (time.time() - t0))
