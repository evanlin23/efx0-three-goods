"""K4.SDC.K3 data: how the re-run with leader r (k3_leader_r.py) changes the last block: picks that change, agents worse
off, total pick rank of the block, junk count.

    python3 k4/sdc/k3_rerun_stats.py SEED N n m"""
import sys, random, collections, json
import _paths
import k3algo as K
from k3_leader_r import run_from
from k3_leader_r2 import random_run, last_block_start_info
seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
def picks_of(n, m, v, order):
    pool = set(range(m)); Y = {}
    for i in order:
        rr = [g for g in v[i] if g in pool]
        Y[i] = max(rr, key=lambda h: (v[i][h], -h)) if rr else None
        if Y[i] is not None: pool.discard(Y[i])
    return Y
def rank(v, i, g):
    if g is None: return 3
    return sorted(v[i], key=lambda h: (-v[i][h], h)).index(g)
while C['bad'] < N:
    vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
    v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
    info, order = random_run(n, m, v, rng)
    if not info['branch'].startswith('rot'): continue
    C['bad'] += 1
    s = last_block_start_info(order, v); r = info['r']; B = order[s:]
    i2, o2 = run_from(n, m, v, order[:s], r)
    Y1 = picks_of(n, m, v, order); Y2 = picks_of(n, m, v, o2)
    rs1 = sum(rank(v, i, Y1[i]) for i in B); rs2 = sum(rank(v, i, Y2[i]) for i in B)
    C['rank sum in B*: ' + ('down' if rs2 < rs1 else 'same' if rs2 == rs1 else 'up')] += 1
    j1 = m - sum(1 for i in range(n) if Y1[i] is not None); j2 = m - sum(1 for i in range(n) if Y2[i] is not None)
    C['junk: ' + ('down' if j2 < j1 else 'same' if j2 == j1 else 'up')] += 1
    C['r gets its top in rerun'] += rank(v, r, Y2[r]) == 0
    C['r had rank %d' % rank(v, r, Y1[r])] += 1
    changed = [i for i in B if Y1[i] != Y2[i]]
    C['agents of B* whose pick changes: %d of %d' % (len(changed), len(B))] += 1
    better = sum(1 for i in changed if rank(v, i, Y2[i]) < rank(v, i, Y1[i])); worse = len(changed) - better
    C['changed agents: worse off %d' % worse] += 1
    k = order[s]
    C['leader k* in rerun gets rank %d' % rank(v, k, Y2[k])] += 1
    C['rerun rotates'] += i2['branch'].startswith('rot')
for key in sorted(C, key=str): print(key, C[key])
