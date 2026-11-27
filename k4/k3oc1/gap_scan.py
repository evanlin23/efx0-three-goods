"""The gap of the joint proof (k4/k3_oc1.md §11): hard perfect drafts (every agent picks; no one-absorber completion,
lbtest.lb2) covered neither by Theorem R1C (R1-compatible) nor by Theorem B* (thm_bstar.bstar).  Exhaustive over a
source's profiles and the drafts of every order.  Writes every gap draft as a GAP line (instance, m, an order, picks,
|T| after LB's upgrades, |E_t| for each terminal t).
    python3 k4/k3oc1/gap_scan.py SOURCE [SHARD NSHARDS]     (SOURCE as in oc1_max.py)"""
import sys, os, json, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of
from lbtest import lb2, upgrade, parts, exposed
from r1compat import r1_compatible
from thm_bstar import bstar
from oc1_fast import drafts
from oc1_k3 import profiles
from oc1_max import sources

def an_order(rk, Y):
    n = len(rk); holder = {g: i for i, g in enumerate(Y) if g is not None}
    pre = [set(holder[g] for g in rk[i][:(rk[i].index(Y[i]) if Y[i] is not None else 3)]) for i in range(n)]
    order = []; left = set(range(n))
    while left:
        i = min(j for j in left if pre[j] <= set(order)); order.append(i); left.discard(i)
    return order

if __name__ == '__main__':
    src = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/k3oc1/gap_scan.py', *sys.argv[1:], flush=True)
    for ci, (sets, m) in enumerate(sources(src)):
        if ci % nsh != shard: continue
        n = len(sets); C['hypergraphs'] += 1
        for rk in profiles(sets, 0, None):
            for Y in drafts(rk, n):
                if any(g is None for g in Y): continue
                b = base_of(Y, m)
                if lb2(rk, m, b): continue
                C['hard perfect'] += 1
                bu = upgrade(rk, m, b); B, J, U, NA, F, T = parts(rk, m, bu)
                if r1_compatible(rk, Y): C['covered by R1C'] += 1; continue
                r, found = bstar(rk, m, Y)
                if r == 'B* applies': C['covered by B* (not R1C)'] += 1; continue
                ET = [len(exposed(rk, bu, t, B, J, U)) for t in T]
                C['GAP, |T| = %d' % len(T)] += 1
                print('GAP', json.dumps([list(x) for x in rk]), m, 'order', tuple(an_order(rk, Y)), 'picks', tuple(Y), '|T|', len(T), '|E_t|', ET, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
