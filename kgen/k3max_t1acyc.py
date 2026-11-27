"""After a rotation from E_t into t (kgen/n3.md §15.5): does the want graph stay acyclic, and is there a terminal
(before upgrades)?  Per |J| and |E_t|, over every perfect draft with T = {t} after LB's upgrades and |E_t| >= 2.
Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_t1acyc.py small:4|small:5 SHARD NSHARDS"""
import sys, os, json, collections
K = os.environ['K3OC1']; sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles
from thm_bstar import chains_to
from k3max_t1 import rotate
def acyclic(rk, B, U):
    n = len(rk); holder = {B[i][0]: i for i in range(n) if not U[i] and len(B[i]) == 1}
    adj = collections.defaultdict(set)
    for j in range(n):
        if U[j] or not B[j]: continue
        for g in rk[j][:rk[j].index(B[j][0])]:
            if g in holder: adj[holder[g]].add(j)
    color = {}
    def dfs(u):
        color[u] = 1
        for w in adj[u]:
            if color.get(w) == 1: return False
            if w not in color and not dfs(w): return False
        color[u] = 2; return True
    return all(dfs(u) for u in range(n) if u not in color)
src, shard, nsh = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); C = collections.Counter()
print('$ python3 kgen/k3max_t1acyc.py', *sys.argv[1:], flush=True)
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
            key = '|J| = %d, |E_t| = %d' % (len(J), len(E)); C[key] += 1
            allac = True; allT = True
            for k in E:
                for P in chains_to(rk, B, U, k, t):
                    nb = rotate(rk, ub, B, k, P); B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
                    allac &= acyclic(rk, B2, U2); allT &= len(T2) >= 1
            C[key + ': every rotation keeps the want graph acyclic %s' % allac] += 1
            C[key + ': every rotation leaves a terminal (before upgrades) %s' % allT] += 1
for k in sorted(C): print(C[k], k)
