"""Structure of the one-terminal gap drafts (kgen/n3.md §15): where t's pick sits, who wants the exposed tops, the
exposed pairs, and what the best-for-t rotation from E_t into t produces.  Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_t1stats.py small:4|certs:5 SHARD NSHARDS"""
import sys, os, json, collections
K = os.environ['K3OC1']; sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, parts, exposed, upgrade
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles
from r1compat import r1_compatible
from thm_bstar import bstar, chains_to, mh
from k3max_t1 import rotate
src = sys.argv[1]; shard, nsh = int(sys.argv[2]), int(sys.argv[3]); C = collections.Counter()
print('$ python3 kgen/k3max_t1stats.py', *sys.argv[1:], flush=True)
for ci, (sets, m) in enumerate(hypergraphs(src, None)):
    if ci % nsh != shard: continue
    n = len(sets)
    for rk in profiles(sets, 0, None):
        for Y in drafts(rk, n):
            if None in Y: continue
            b = base_of(Y, m)
            if lb2(rk, m, b) or r1_compatible(rk, Y): continue
            bs, found = bstar(rk, m, Y)
            if found and any(f[3] for f in found): continue
            ub = upgrade(rk, m, b); B, J, U, NA, F, T = parts(rk, m, ub)
            if len(T) != 1: continue
            t = T[0]; E = exposed(rk, ub, t, B, J, U)
            C['gap'] += 1
            C['Y_t is t\'s %s' % 'abc'[rk[t].index(B[t][0])]] += 1
            # who wants each exposed top
            wanters = lambda g: [j for j in range(n) if not U[j] and g in rk[j] and B[j] and rk[j].index(g) < rk[j].index(B[j][0])]
            C['every exposed top wanted by t %s' % all(t in wanters(B[x][0]) for x in E)] += 1
            C['every exposed top wanted only by t %s' % all(wanters(B[x][0]) == [t] for x in E)] += 1
            pairs = [frozenset((rk[x][1], rk[x][2])) for x in E]
            C['exposed pairs pairwise distinct %s' % (len(set(pairs)) == len(pairs))] += 1
            C['exposed pairs share a common good %s' % bool(frozenset.intersection(*pairs))] += 1
            C['some exposed pair contains Y_t %s' % any(B[t][0] in p for p in pairs)] += 1
            C['|J| = %d, |E_t| = %d' % (len(J), len(E))] += 1
            C['upgraded agents at the draft: %d' % sum(U)] += 1
            # best rotation outcome
            rots = []
            for k in E:
                for P in chains_to(rk, B, U, k, t):
                    nb = rotate(rk, ub, B, k, P); rots.append((rk[t].index(B[P[-2]][0]), k, P, nb))
            best = min(r[0] for r in rots)
            for r in rots:
                if r[0] != best: continue
                nb = r[3]; ub2 = upgrade(rk, m, nb); B2, J2, U2, NA2, F2, T2 = parts(rk, m, ub2)
                C['best rotation: t gets its %s' % 'abc'[best]] += 1
                C['best rotation: chain length s = %d' % (len(r[2]) - 1)] += 1
                C['best rotation: no owner (|J\'| <= |T\'|) %s' % (len(J2) <= len(T2))] += 1
                C['best rotation: t terminal afterwards %s' % (t in T2)] += 1
                C['best rotation: other exposed agents terminal afterwards: %d of %d' % (sum(1 for x in E if x != r[1] and x in T2), len(E) - 1)] += 1
                break
for k in sorted(C): print(C[k], k)
