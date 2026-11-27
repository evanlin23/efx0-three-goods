"""Cross-check k3lib.completion (exhaustive, values 4, 3, 2) against the SAT test oc_absorb.extends_A of k4/sdc
(sdclib's EFX0 encoding) with random strictly balanced values, on SD picks and on states one chain away.

    python3 k4/k3oc1/xcheck_sat.py N M COUNT SEED"""
import sys, os, random, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
import _paths
from k3lib import sd, base_of, completion, chains, vals
from sdclib import Enc
from oc_absorb import extends_A

n, m, cnt, seed = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
for t in range(cnt):
    rk = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
    sets = []; vv = []
    for r in rk:
        while True:
            a, b, c = sorted(rng.sample(range(1, 40), 3), reverse=True)
            if a < b + c: break
        sets.append(list(r)); vv.append([a, b, c])
    E = Enc(sets, vv, m); V = vals(rk)
    o = list(range(n)); rng.shuffle(o)
    b = base_of(sd(rk, m, o), m)
    states = [b] + [nb for nb, d in chains(rk, m, b, V)][:30]
    for s in states:
        x = completion(rk, m, s, 1, V) is not None
        y = extends_A(E, s, 1)
        C['agree' if x == y else 'MISMATCH'] += 1
        if x != y: print('MISMATCH', rk, vv, s, x, y)
        C['extends %s' % x] += 1
print(dict(C))
