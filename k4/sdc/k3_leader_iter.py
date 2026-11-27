"""Iterate the leader rule of k3_leader_r.py: while LB+ is in the bad case, re-run the last block with its r as leader
(continuation by index, or random).  Does it stop without rotation, and after how many re-runs?

    python3 k4/sdc/k3_leader_iter.py SEED N n m"""
import sys, random, collections, json
import _paths
import k3algo as K
from k3_leader_r import run_from
from k3_leader_r2 import random_run, last_block_start_info

if __name__ == '__main__':
    seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/k3_leader_iter.py', *sys.argv[1:])
    tries = 0
    while C['bad case'] < N and tries < 300000:
        tries += 1
        if rng.random() < 0.5:
            vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
            v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
        else:
            v = K.random_core(n, m, rng, vmax=30)
            if any(len(set(x.values())) < 3 for x in v): continue
        info, order = random_run(n, m, v, rng)
        if not info['branch'].startswith('rot'): continue
        C['bad case'] += 1
        for mode in ('index', 'random'):
            inf, o, seen, it = info, order, set(), 0
            while inf['branch'].startswith('rot') and it < 20:
                s = last_block_start_info(o, v); r = inf['r']
                key = (tuple(o[:s]), r)
                if key in seen and mode == 'index': break
                seen.add(key)
                inf, o = run_from(n, m, v, o[:s], r, rng if mode == 'random' else None); it += 1
            ok = not inf['branch'].startswith('rot')
            C[(mode, 'stops without rotation')] += ok
            C[(mode, 're-runs', it if ok else 'never')] += 1
            if not ok and C['shown'] < 3:
                C['shown'] += 1; print('NO STOP', mode, json.dumps(([sorted(x.items()) for x in v], order)))
    print('tries', tries)
    for k in sorted(C, key=str): print(k, C[k])
