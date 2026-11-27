"""K4.SDC.K3: compare SD(pi with k* moved last) with LB+'s rotated pre-allocation (Theorem B: along a need chain
k* = x0 -> x1 -> ... -> xt = r, x_i takes Y_{x_{i-1}}, k* takes b_{k*} (and c_{k*}), Y_r is released).  If the picks
agree (k*'s pick b_{k*}), Theorem B's completion is a completion of SD(pi_k): Lemma D holds there with LB+'s proof.

    python3 k4/sdc/k3_defer_rot.py SEED N n m"""
import sys, random, collections, json
import _paths
import k3algo as K
from k3_leader_r2 import last_block_start_info
from sdclib import Enc
from sdc_orders import sd, completable
from no_k3 import no_order0, lbplus_on


def ranked(v, i):
    return sorted(v[i], key=lambda h: (-v[i][h], h))


def chains(v, Y, U, B, k, r):
    def needs(j):
        if Y[j] is None: return set(v[j])
        R = ranked(v, j); return set(R[:R.index(Y[j])])
    out = []
    def dfs(p):
        x = p[-1]
        if x == r: out.append(list(p)); return
        for j in B:
            if j not in p and j not in U and Y[x] is not None and Y[x] in needs(j): dfs(p + [j])
    dfs([k]); return out


if __name__ == '__main__':
    seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); tries = 0
    print('$ python3 k4/sdc/k3_defer_rot.py', *sys.argv[1:])
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
        s = last_block_start_info(ord0, v); k = ord0[s]; r = info['r']; B = ord0[s:]; U = set(info['upgraded'])
        Y2 = sd(E, [i for i in ord0 if i != k] + [k])[0]
        a, b, c = ranked(v, k)
        rot_match = False
        for ch in chains(v, Y0, U, B, k, r):
            Yr = list(Y0)
            for t in range(1, len(ch)): Yr[ch[t]] = Y0[ch[t - 1]]
            Yr[k] = b
            if Yr == list(Y2): rot_match = True
        C['k* gets b'] += Y2[k] == b
        C['SD(pi_k) = rotated picks (some chain)'] += rot_match
        C['k* gets b, not a rotation'] += (Y2[k] == b and not rot_match)
        if Y2[k] == b and not rot_match:
            C['  ... and extends'] += completable(E, Y2)
    print('tries', tries, dict(C))
