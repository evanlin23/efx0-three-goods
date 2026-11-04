"""K4.SDC.K3 via deferral in a FIXED order.  P = the plain neediest-first run (an R1 run at k = 3).  In LB+'s bad case,
let P' = P's order with k* (the leader of the last block) moved to the end.  In serial dictatorship with a fixed order,
moving one agent to the end makes every other agent's pick weakly better (its available set only grows).  Does SD(P')
extend?  Does k* get its b?  Also tries moving r to the end.

    python3 k4/sdc/k3_defer.py SEED N n m"""
import sys, random, collections, json
import _paths
import k3algo as K
from k3_leader_r2 import last_block_start_info
from sdclib import Enc
from sdc_orders import sd, completable
from no_k3 import no_order0, lbplus_on


def ranked(v, i):
    return sorted(v[i], key=lambda h: (-v[i][h], h))


if __name__ == '__main__':
    seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); tries = 0
    print('$ python3 k4/sdc/k3_defer.py', *sys.argv[1:])
    while C['bad case'] < N and tries < 500000:
        tries += 1
        if rng.random() < 0.5:
            vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
            v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
        else:
            v = K.random_core(n, m, rng, vmax=30)
            if any(len(set(x.values())) < 3 for x in v): continue
        sets = [sorted(v[i]) for i in range(n)]; vals = [[v[i][g] for g in sets[i]] for i in range(n)]
        E = Enc(sets, vals, m)
        Y0, ord0 = no_order0(E); info = lbplus_on(n, m, v, ord0)
        if not info['branch'].startswith('rot'): continue
        C['bad case'] += 1
        s = last_block_start_info(ord0, v); k = ord0[s]; r = info['r']
        for who, x in (('k*', k), ('r', r)):
            o2 = [i for i in ord0 if i != x] + [x]
            Y2 = sd(E, o2)[0]
            # monotonicity check
            rk = lambda i, g: 9 if g is None else ranked(v, i).index(g)
            assert all(rk(i, Y2[i]) <= rk(i, Y0[i]) for i in range(n) if i != x)
            ok = completable(E, Y2)
            C[who + ' last (fixed order): extends'] += ok
            if who == 'k*':
                C['k* last: k* gets ' + 'abc'[rk(k, Y2[k])] if Y2[k] is not None else 'k* last: k* gets -'] += 1
                okk = ok
        C['k* last or r last extends'] += okk or completable(E, sd(E, [i for i in ord0 if i != r] + [r])[0])
    print('tries', tries, dict(C))
