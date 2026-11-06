"""Conjecture NO at k = 3 (every agent exactly three goods, balanced).  The plain neediest-first run P (no owner) is an
R1 run of LB's Phase 1.  Rule: if LB+ completes P without rotation, done (owner LB's r).  Otherwise (bad case), take
o = k*, the leader of P's last block, and use NO(k*).  Does NO(k*) then extend?  (SAT completion check, any completion.)
Also reports whether NO(k*) avoids LB+'s rotation when run through LB+ itself.

    python3 k4/sdc/no_k3.py SEED N n m"""
import sys, random, collections, json
import _paths
import k3algo as K
from k3_leader_r import run_from
from k3_leader_r2 import last_block_start_info
from sdclib import Enc
from sdc_orders import completable
from sdc_need import rule_order
from sdc_need_owner import order_with_last


def no_order0(E, o=None):
    """NO's order with the note's convention: an agent without available goods has need 0 (so it is processed before
    fresh agents, whose need is negative at k = 3).  Same picks as order_with_last; this order is an R1 run."""
    left = set(range(E.m)); Y = [None] * E.n; done = []
    def need(i):
        av = sorted((E.v[i][g] for g in E.R[i] if g in left), reverse=True) + [0, 0, 0]
        return av[0] - av[1] - av[2]
    while len(done) < E.n:
        rest = [i for i in range(E.n) if i not in done and (i != o or len(done) == E.n - 1)]
        i = max(rest, key=lambda j: (need(j), -j))
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
        done.append(i)
    return Y, done


def lbplus_on(n, m, v, order):
    """LB+ (k3algo._lbplus_fast) on an explicit R1 order."""
    agents = list(range(n)); goods = list(range(m))
    a, b, c = {}, {}, {}
    for i in agents:
        a[i], b[i], c[i] = K.sort3(lambda g: v[i][g], None, sorted(v[i]))
    rank = {i: {a[i]: 0, b[i]: 1, c[i]: 2} for i in agents}
    holders = collections.defaultdict(list)
    for i in agents:
        for g in (a[i], b[i], c[i]): holders[g].append(i)
    pool = set(goods); Y, blk = {}, {}; nblk = 0
    for i in order:
        full = all(g in pool for g in (a[i], b[i], c[i]))
        lost_exists = any(any(g not in pool for g in (a[j], b[j], c[j])) for j in agents if j not in Y)
        assert not (full and lost_exists and any(j not in Y and not all(g in pool for g in (a[j], b[j], c[j])) for j in agents if j != i)), 'not an R1 order'
        if full: nblk += 1
        blk[i] = nblk
        y = next((g for g in (a[i], b[i], c[i]) if g in pool), None); Y[i] = y
        if y is not None: pool.discard(y)
    info = {'peeled': 0, 'branch': None, 'core_n': n, 'core_m': m}
    X = [None] * m
    X, info = K._lbplus_fast(agents, goods, order, a, b, c, rank, holders, Y, blk, X, info)
    assert K.raw_efx0(n, m, v, X)
    return info

if __name__ == '__main__':
    seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); tries = 0
    print('$ python3 k4/sdc/no_k3.py', *sys.argv[1:])
    while C['bad case'] < N and tries < 400000:
        tries += 1
        if rng.random() < 0.5:
            vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
            v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
        else:
            v = K.random_core(n, m, rng, vmax=30)
            if any(len(set(x.values())) < 3 for x in v): continue
        sets = [sorted(v[i]) for i in range(n)]; vals = [[v[i][g] for g in sets[i]] for i in range(n)]
        E = Enc(sets, vals, m)
        Y0, ord0 = no_order0(E)
        assert Y0 == rule_order(E, 'need2', False)[0]
        s = last_block_start_info(ord0, v)
        info = lbplus_on(n, m, v, ord0)
        C['runs'] += 1
        if not info['branch'].startswith('rot'):
            C['plain run: no bad case'] += 1; continue
        C['bad case'] += 1
        kstar = ord0[s]
        Yk, ok_ord = no_order0(E, kstar)
        ok = completable(E, Yk)
        C['NO(k*) extends'] += ok
        r = info['r']; okr = completable(E, no_order0(E, r)[0])
        C['NO(r) extends'] += okr; C['NO(k*) or NO(r) extends'] += (ok or okr)
        C['plain run extends anyway'] += completable(E, Y0)
        C['some owner works'] += ok or any(completable(E, order_with_last(E, 'need2', False, o)[0]) for o in range(n))
        if not ok and C['shown'] < 3:
            C['shown'] += 1; print('NO(k*) FAILS', json.dumps((sets, vals)), 'plain order', ord0, 'k*', kstar)
    print('tries', tries, dict(C))
