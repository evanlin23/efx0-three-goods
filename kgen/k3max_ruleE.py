"""Rule E for the rotation into the unique terminal (kgen/n3.md §15.6): from k in E_t, the next receiver is always
the earliest wanter of the current good, in a fixed topological order of the draft's need DAG (holders before
wanters; ties by index).  Tested: does Rule E's rotation keep the want graph acyclic, for every k in E_t (Lemma G5
candidate)?  And for some k, does it reach |J'| <= |T'| after LB's upgrades (T1' with Rule E)?  Needs K3OC1 as
kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_ruleE.py small:4|certs:5|small:5 [SHARD NSHARDS]"""
import sys, os, json, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade, lb2
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles
from k3max_t1 import rotate
from k3max_t1acyc import acyclic


def topo(rk, B, U):
    n = len(rk); holder = {B[i][0]: i for i in range(n) if not U[i] and len(B[i]) == 1}
    pre = [set() for _ in range(n)]
    for j in range(n):
        if U[j] or not B[j]: continue
        for g in rk[j][:rk[j].index(B[j][0])]:
            if g in holder: pre[j].add(holder[g])
    order, done = [], set()
    while len(order) < n:
        i = min(i for i in range(n) if i not in done and pre[i] <= done)
        order.append(i); done.add(i)
    return {i: p for p, i in enumerate(order)}


def rule_e_chain(rk, B, U, k, t, pos):
    n = len(rk); P = [k]
    while P[-1] != t:
        g = B[P[-1]][0]
        W = [w for w in range(n) if w not in P and not U[w] and B[w] and g in rk[w] and rk[w].index(g) < rk[w].index(B[w][0])]
        if not W: return None
        P.append(min(W, key=lambda w: pos[w]))
    return P


if __name__ == '__main__':
    src = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter(); shown = 0
    print('$ python3 kgen/k3max_ruleE.py', *sys.argv[1:], flush=True)
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
                pos = topo(rk, B, U); C['drafts'] += 1
                allac, best = True, None; omk = {}
                for k in E:
                    P = rule_e_chain(rk, B, U, k, t, pos)
                    if P is None: C['Rule E chain does not reach t (impossible with one terminal)'] += 1; continue
                    nb = rotate(rk, ub, B, k, P); B2, J2, U2 = parts(rk, m, nb)[:3]
                    ac = acyclic(rk, B2, U2); allac &= ac
                    P3 = parts(rk, m, upgrade(rk, m, nb)); om = len(P3[1]) - len(P3[5])
                    best = om if best is None else min(best, om); omk[k] = om
                C['Rule E rotation keeps the want graph acyclic for every k: %s' % allac] += 1
                if omk:
                    jk = '|J| = %d' % len(J)
                    first = min(omk, key=lambda x: pos[x]); last = max(omk, key=lambda x: pos[x])
                    tbest = min(omk, key=lambda x: (rk[t].index(B[x][0]) if B[x][0] in rk[t] else 9, pos[x]))
                    C[jk + ': k = sigma-first exposed agent works: %s' % (omk[first] <= 0)] += 1
                    C[jk + ': k = sigma-last exposed agent works: %s' % (omk[last] <= 0)] += 1
                    C[jk + ': k = exposed agent whose top t ranks highest works: %s' % (omk[tbest] <= 0)] += 1
                    C[jk + ': every k works: %s' % all(o <= 0 for o in omk.values())] += 1
                    lbk = {}
                    for k2 in E:
                        P = rule_e_chain(rk, B, U, k2, t, pos)
                        if P is not None: lbk[k2] = bool(lb2(rk, m, rotate(rk, ub, B, k2, P)))
                    C[jk + ': every k completes with an owner allowed (lb2 after the Rule E rotation): %s' % all(lbk.values())] += 1
                C['Rule E: some k reaches |J\'| <= |T\'| (T1\' with Rule E): %s' % (best is not None and best <= 0)] += 1
                if not allac and shown < 3:
                    shown += 1; print('RULE E CYCLE', json.dumps([list(x) for x in rk]), m, 'picks', Y, 'E_t', E, flush=True)
    for k in sorted(C): print(C[k], k)
