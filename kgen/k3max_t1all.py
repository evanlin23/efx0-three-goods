"""Theorem T1' candidate (kgen/n3.md §15.4): for EVERY perfect draft (hard or not) whose state after LB's upgrades
has one terminal t and |E_t| >= 2, some rotation from an exposed k in E_t along a need chain into t gives, after LB's
upgrades again, |J'| <= |T'| (Lemma 1 (a): a completion with no owner, every bundle of at most two goods).
Also checked: Lemma 2's count, i.e. omega' = |J'| - |T'| equals (m - 2n) + e' + nu' with nu' the wanted goods.
Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_t1all.py small:4|certs:5|small:5 [SHARD NSHARDS]"""
import sys, os, json, collections, time
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, parts, exposed, upgrade
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles
from thm_bstar import chains_to
from k3max_t1 import rotate


def wanted(rk, B, U):
    n = len(rk); w = set()
    for j in range(n):
        if U[j] or not B[j]: continue
        y = B[j][0]
        for g in rk[j][:rk[j].index(y)]: w.add(g)
    return w


if __name__ == '__main__':
    src = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter(); t0 = time.time(); shown = 0
    print('$ python3 kgen/k3max_t1all.py', *sys.argv[1:], flush=True)
    for ci, (sets, m) in enumerate(hypergraphs(src, None)):
        if ci % nsh != shard: continue
        n = len(sets)
        for rk in profiles(sets, 0, None):
            for Y in drafts(rk, n):
                if None in Y: continue
                ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub)
                if len(T) != 1: continue
                t = T[0]; E = exposed(rk, ub, t, B, J, U)
                if len(E) < 2: continue
                hard = not lb2(rk, m, base_of(Y, m))
                C['perfect drafts with T = {t}, |E_t| >= 2 (hard: %s)' % hard] += 1
                best = None
                for k in E:
                    for P in chains_to(rk, B, U, k, t):
                        nb = upgrade(rk, m, rotate(rk, ub, B, k, P)); B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
                        om = len(J2) - len(T2)
                        assert om == (m - 2 * n) + sum(1 for i in range(n) if not B2[i]) + len(wanted(rk, B2, U2)), 'Lemma 2 count'
                        best = om if best is None else min(best, om)
                C['  some rotation reaches |J\'| <= |T\'| (hard: %s): %s' % (hard, best is not None and best <= 0)] += 1
                if (best is None or best > 0) and shown < 4:
                    shown += 1; print('T1\' FAILS', 'hard' if hard else 'not hard', json.dumps([list(x) for x in rk]), m, 'picks', Y, 'J', J, 'E_t', E, 'least omega\'', best, flush=True)
    for k in sorted(C): print(C[k], k)
    print('time %.0f s' % (time.time() - t0))
