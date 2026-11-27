"""Soundness check of lbtest.lb_simple (Lemma 1) against the exhaustive one-absorber completion (k3lib.completion),
on drafts and on every state one DE trade away: whenever lb_simple passes, a completion must exist.
    python3 k4/k3oc1/xcheck_simple.py SOURCE PROFILES SEED"""
import sys, os, itertools, random, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of, completion, vals
from de_moves import de_trades
from lbtest import lb_simple
from oc1_k3 import hypergraphs, profiles
src = sys.argv[1]; P = int(sys.argv[2]); rng = random.Random(int(sys.argv[3])); C = collections.Counter()
for sets, m in hypergraphs(src, rng):
    n = len(sets)
    for rk in profiles(sets, P, rng):
        V = vals(rk); seen = set()
        for o in itertools.permutations(range(n)):
            b = base_of(sd(rk, m, o), m)
            if b in seen: continue
            seen.add(b)
            for s in [b] + [nb for nb, d in de_trades(rk, m, b)]:
                if lb_simple(rk, m, s):
                    ok = completion(rk, m, s, 1, V) is not None
                    C['simple passes; exhaustive completion exists %s' % ok] += 1
                    if not ok: print('UNSOUND', rk, m, s)
for k in sorted(C): print(k, C[k])
