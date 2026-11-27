"""Displacement chains (k4/sdc.md §10).  For an order pi and an agent k, moving k last changes SD only along one chain:
j1 = the first agent after k preferring Y_k to its pick takes Y_k, j2 = the first agent after j1 preferring Y_{j1} to its
pick takes Y_{j1}, ...  This script (1) checks that claim against SD directly on random instances, and (2) at k = 3 in
LB+'s bad case, classifies the displacement chain from k*: an LB need chain ending at r (Theorem B applies), a chain
through an upgraded agent, a chain continuing past r, and records whether SD(pi with k* last) or SD(pi with r last)
extends in each class.

    python3 k4/sdc/k3_disp.py SEED N n m"""
import sys, random, collections, json
import _paths
import k3algo as K
from k3_leader_r2 import last_block_start_info
from sdclib import Enc
from sdc_orders import sd, completable
from no_k3 import no_order0, lbplus_on


def ranked(v, i):
    return sorted(v[i], key=lambda h: (-v[i][h], h))


def prefers(E, j, h, y):
    if h is None or h not in E.v[j]: return False
    return y is None or (E.v[j][h], -h) > (E.v[j][y], -y)


def displacement(E, order, Y, k):
    """The chain [k, j1, j2, ...] and the final hole."""
    pos = order.index(k); hole = Y[k]; chain = [k]
    if hole is None: return chain, None
    for x in order[pos + 1:]:
        if prefers(E, x, hole, Y[x]):
            chain.append(x); hole, = [Y[x]]
            if hole is None: break
    return chain, hole


def predicted(E, order, Y, k):
    chain, hole = displacement(E, order, Y, k)
    Z = list(Y)
    for t in range(1, len(chain)): Z[chain[t]] = Y[chain[t - 1]]
    picked = set(g for i, g in enumerate(Z) if g is not None and i != k)
    av = [g for g in E.R[k] if g not in picked]
    Z[k] = max(av, key=lambda h: (E.v[k][h], -h)) if av else None
    return Z, chain


if __name__ == '__main__':
    seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); tries = 0
    print('$ python3 k4/sdc/k3_disp.py', *sys.argv[1:])
    # (1) the displacement lemma, on random instances with up to 4 goods per agent and random orders
    for t in range(3000):
        nn = rng.randint(2, 7); mm = rng.randint(nn, 3 * nn)
        sets = [sorted(rng.sample(range(mm), min(mm, rng.randint(1, 4)))) for _ in range(nn)]
        vals = [rng.sample(range(1, 40), len(s)) for s in sets]
        E = Enc(sets, vals, mm); order = rng.sample(range(nn), nn); Y = sd(E, order)[0]; k = rng.randrange(nn)
        Z, _ = predicted(E, order, Y, k)
        assert Z == sd(E, [i for i in order if i != k] + [k])[0], (sets, vals, order, k)
    C['displacement lemma checked'] = 3000
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
        s = last_block_start_info(ord0, v); k = ord0[s]; r = info['r']; U = set(info['upgraded'])
        Z, chain = predicted(E, ord0, Y0, k)
        through_U = any(x in U for x in chain[1:])
        past_r = r in chain and chain[-1] != r
        cls = 'ends at r, no upgraded agent (Theorem B)' if (chain[-1] == r and not through_U) else \
              'continues past r' if past_r else 'through an upgraded agent' if through_U else 'other'
        okk = completable(E, Z); okr = completable(E, sd(E, [i for i in ord0 if i != r] + [r])[0])
        C[cls] += 1; C[cls + ': k* last extends'] += okk; C[cls + ': k* last or r last extends'] += (okk or okr)
    print('tries', tries)
    for kk in sorted(C, key=str): print(kk, C[kk])
