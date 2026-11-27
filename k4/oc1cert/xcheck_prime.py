"""Cross-check of cegar.Cert.moves(prime=True) (rings removed) against kgen-rounds' one_chain_prime (verify_k4zero.py,
proof/kgen-rounds 27f1111), on random strict profiles of random n = 4 and n = 5 cores and random orders.
    python3 k4/oc1cert/xcheck_prime.py N DIR   (DIR: verify_k4zero.py, e.g. git show origin/proof/kgen-rounds:kgen/rounds/verify_k4zero.py)"""
import sys, json, gzip, random, itertools, collections
import os
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, sys.argv[2])   # a directory holding kgen/rounds/verify_k4zero.py from proof/kgen-rounds
from cegar import Cert
import verify_k4zero as KR
rng = random.Random(7); C = collections.Counter()
cores = []
for lst in ('4_n4_3', '4_pure', '5_pure'):
    cores += [c['sets'] for c in json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_%s.json.gz') % lst))['cores']]
for it in range(int(sys.argv[1])):
    sets = rng.choice(cores); E = Cert(sets, prime=True, cap_aut=0)
    prof = [rng.randrange(len(D)) for D in E.dom]; vals = E.vals_of(prof)
    V = [[vals[i].get(g, 0) for g in range(E.m)] for i in range(E.n)]
    o = list(range(E.n)); rng.shuffle(o)
    y = KR.sd(V, o)
    base = [(g,) if g is not None else () for g in y]
    mine = {tuple(frozenset(b) for b in base)}
    for kind, path, Hs, nb, imp in E.moves(list(base), vals):
        if kind == 'ring': continue
        mine.add(tuple(frozenset(nb.get(a, base[a])) for a in range(E.n)))
    theirs = KR.one_chain_prime(V, [frozenset(b) for b in base])
    C['agree' if mine == theirs else 'DIFFER'] += 1
    C['states'] += len(mine)
    if mine != theirs and C['shown'] < 3:
        C['shown'] += 1; print('DIFF', sets, V, y, 'only mine', list(mine - theirs)[:3], 'only theirs', list(theirs - mine)[:3])
print(dict(C))
