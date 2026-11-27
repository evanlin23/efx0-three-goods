"""lb2 (exact test; earlier lb1 = LB+'s Lemma 1, slots of size one) against the exhaustive one-absorber completion, on drafts of every order and
on every state one DE trade away.   python3 k4/k3oc1/xcheck_lb1.py small:N [PROFILES SEED]"""
import sys, os, itertools, random, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of, completion, vals
from de_moves import de_trades
from lbtest import lb1, lb2
from oc1_k3 import hypergraphs, profiles
src = sys.argv[1]; P = int(sys.argv[2]) if len(sys.argv) > 2 else 0; rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
C = collections.Counter()
for sets, m in hypergraphs(src, rng):
    n = len(sets)
    for rk in profiles(sets, P, rng):
        V = vals(rk); seen = set()
        for o in itertools.permutations(range(n)):
            b = base_of(sd(rk, m, o), m)
            if b in seen: continue
            seen.add(b)
            for s, kind in [(b, 'draft')] + [(nb, 'after trade') for nb, d in de_trades(rk, m, b)]:
                x = completion(rk, m, s, 1, V) is not None; y = lb2(rk, m, s) is not None
                C[kind + (' agree' if x == y else ' MISMATCH brute %s lb1 %s' % (x, y))] += 1
                if x != y and C['shown'] < 5: C['shown'] += 1; print('MISMATCH', kind, rk, m, s, x, y)
for k in sorted(C): print(k, C[k])
