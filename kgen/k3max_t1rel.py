"""T1' with dead goods, and where the releases of the least-omega' rotation come from (kgen/n3.md §15.4).  For every
perfect draft with T = {t} after LB's upgrades and |E_t| >= 2 (cores of SRC plus DEAD goods valued by nobody):
is the least omega' over rotations into t at most 0, and which agents does that rotation release?  Needs K3OC1 as
kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_t1rel.py small:4 DEAD"""
import sys, os, json, collections
K = os.environ['K3OC1']; sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, parts, exposed, upgrade
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles
from thm_bstar import chains_to
from k3max_t1 import rotate
src = sys.argv[1]; dead = int(sys.argv[2]); C = collections.Counter()
print('$ python3 kgen/k3max_t1rel.py', *sys.argv[1:], flush=True)
for sets, m in hypergraphs(src, None):
    m = m + dead; n = len(sets)
    for rk in profiles(sets, 0, None):
        for Y in drafts(rk, n):
            if None in Y: continue
            ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub)
            if len(T) != 1: continue
            t = T[0]; E = exposed(rk, ub, t, B, J, U)
            if len(E) < 2: continue
            C['drafts'] += 1
            res = []
            for k in E:
                for P in chains_to(rk, B, U, k, t):
                    nb0 = rotate(rk, ub, B, k, P); nb = upgrade(rk, m, nb0)
                    B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
                    res.append((len(J2) - len(T2), k, P, nb0, nb, T2, U2))
            om = min(r[0] for r in res)
            C['least omega\' <= 0: %s' % (om <= 0)] += 1
            if om <= 0 or dead: 
                r = [r for r in res if r[0] == om][0]; om_, k, P, nb0, nb, T2, U2 = r
                rel = [x for x in T2 if x != t]
                C['  released agents (terminal after, besides t): %d; |J| - 1 = %d' % (len(rel), len(J) - 1)] += 1
                C['  released: in E_t %d, on the chain %d, other %d' % (sum(1 for x in rel if x in E), sum(1 for x in rel if x in P), sum(1 for x in rel if x not in E and x not in P))] += 1
                newU = [i for i in range(n) if U2[i] and not U[i] and i != k]
                C['  upgrades after the rotation: %d' % len(newU)] += 1
                C['  t terminal after: %s' % (t in T2)] += 1
for k in sorted(C): print(C[k], k)
