"""K4.SDC.K3 data (with k3_leader*.py). Rule X1: in LB+'s bad case, re-run the last block with a needer of a_{k*} (an agent
that prefers k*'s top to its own pick) as leader. Does every needer, with every continuation, avoid rotation? Compared
with leader r.

    python3 k4/sdc/k3_needer.py SEED N n m CONT"""
import sys, random, collections, json
import _paths
import k3algo as K
from k3_leader_r import run_from
from k3_leader_r2 import random_run, last_block_start_info
seed, N, n, m, cont = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter(); tries = 0
def rank(v, i, g):
    if g is None: return 3
    return sorted(v[i], key=lambda h: (-v[i][h], h)).index(g)
while C['bad'] < N and tries < 400000:
    tries += 1
    if rng.random() < 0.5:
        vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
        v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
    else:
        v = K.random_core(n, m, rng, vmax=30)
        if any(len(set(x.values())) < 3 for x in v): continue
    info, order = random_run(n, m, v, rng)
    if not info['branch'].startswith('rot'): continue
    C['bad'] += 1
    s = last_block_start_info(order, v); r = info['r']; B = order[s:]; k = order[s]
    Y = info['picks']; U = set(info.get('upgraded') or [])
    ak = Y[k]
    needers = [j for j in B if j != k and j not in U and ak in v[j] and rank(v, j, ak) < rank(v, j, Y[j])]
    C['needers %d' % len(needers)] += 1
    for name, cands in (('needer of a_k*', needers), ('r', [r])):
        allok = True
        for y in cands:
            for t in range(cont):
                i3, _ = run_from(n, m, v, order[:s], y, rng if t else None)
                if i3['branch'].startswith('rot'): allok = False
        C[name + ': every choice, every continuation avoids rotation'] += allok
print(tries)
for key in sorted(C, key=str): print(key, C[key])
