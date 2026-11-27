"""Owner t after one Rule E rotation, with t last in the order (kgen/n3.md §15.18).  sigma = a topological order of
the draft's need DAG (holders before wanters, ties by index) with t deferred to the end, which is allowed because
nobody wants Y_t.  For every one-terminal gap draft with |E_t| >= 2 and every k in E_t, along k's Rule E chain:
  G6  the good g that t receives has t as its only wanter in P, and t is a terminal of P' (before upgrades);
  G7  every exposed agent y of t in P' is (a) an old exposed agent with pi_y disjoint from pi_k, or holds a_y with
      pi_y = {g, j}, j in J' -- (b) a non-receiver, or (c) the receiver x_{s-1};
  B   Lemma 3 for owner t: h({pi_y ∩ J' : y in E'_t ∩ F'}) <= |T' - E'_t| - 1; and whether E'_t ∩ F' is empty.
Per draft, by class (A: Proposition A applies; R1 twins; R2): does some rotation satisfy B, and does some rotation with
(a) empty (every other exposed pair meets pi_k) satisfy B?  Also: R2 drafts whose exposed pairs share a good.

    K3OC1=... python3 kgen/k3max_propB.py GAPFILE [SHARD NSHARDS]
    K3OC1=... python3 kgen/k3max_propB.py sample SOURCE PROFILES SEED [SHARD NSHARDS]   (hard perfect one-terminal drafts)"""
import sys, os, json, re, ast, gzip, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade
from thm_bstar import mh
from k3max_t1 import rotate
from k3max_ruleE import rule_e_chain


def topo_last(rk, B, U, t):
    n = len(rk); holder = {B[i][0]: i for i in range(n) if not U[i] and len(B[i]) == 1}
    pre = [set() for _ in range(n)]
    for j in range(n):
        if U[j] or not B[j]: continue
        for g in rk[j][:rk[j].index(B[j][0])]:
            if g in holder: pre[j].add(holder[g])
    order, done = [], set()
    while len(order) < n - 1:
        i = min(i for i in range(n) if i not in done and i != t and pre[i] <= done)
        order.append(i); done.add(i)
    order.append(t)
    return {i: p for p, i in enumerate(order)}


def wanters(rk, B, U, g):
    return [w for w in range(len(rk)) if not U[w] and B[w] and g in rk[w] and rk[w].index(g) < rk[w].index(B[w][0])]


def analyse(rk, m, Y, C):
    ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub)
    if len(T) != 1: return
    t = T[0]; E = exposed(rk, ub, t, B, J, U)
    if len(E) < 2: return
    pr = {x: frozenset(rk[x][1:]) for x in E}
    A = any(not any(pr[x] == pr[k] for x in E if x != k) and mh([list(pr[x] - pr[k]) for x in E if x != k]) <= 1 for k in E)
    cls = 'A ' if A else ('R1' if len(E) == 2 else 'R2')
    if cls == 'R2': C['R2: exposed pairs share a good: %s' % bool(set.intersection(*[set(p) for p in pr.values()]))] += 1
    pos = topo_last(rk, B, U, t); someB = someB0 = someE = False
    for k in E:
        P = rule_e_chain(rk, B, U, k, t, pos)
        if P is None: C['FAIL no chain'] += 1; continue
        g = B[P[-2]][0]
        if wanters(rk, B, U, g) != [t]: C['FAIL G6 (g has another wanter)'] += 1
        nb = rotate(rk, ub, B, k, P); B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
        if t not in T2: C['FAIL G6 (t frozen)'] += 1; continue
        Eo = exposed(rk, nb, t, B2, J2, U2); a_empty = all(pr[x] & pr[k] for x in E if x != k)
        for y in Eo:
            if y in E: ok = not (set(rk[y][1:]) & pr[k])
            else: ok = g in rk[y][1:] and all(h in J2 for h in rk[y][1:] if h != g) and (y not in P or y == P[-2])
            if not ok: C['FAIL G7'] += 1
        Ef = [y for y in Eo if y in F2]
        b = mh([[h for h in rk[y][1:] if h in J2] for y in Ef]) <= len([z for z in T2 if z not in Eo]) - 1
        someB |= b; someB0 |= (b and a_empty); someE |= (a_empty and not Ef)
    C['%s drafts: some rotation passes Lemma 3 for owner t: %s' % (cls, someB)] += 1
    C['%s drafts: some rotation with (a) empty passes Lemma 3 for t: %s' % (cls, someB0)] += 1
    C['%s drafts: some rotation with (a) empty leaves t no frozen exposed agent: %s' % (cls, someE)] += 1
    C['%s drafts, |J| %s 3' % (cls, '>=' if len(J) >= 3 else '<')] += 1


if __name__ == '__main__':
    print('$ python3 kgen/k3max_propB.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True); C = collections.Counter()
    if sys.argv[1] == 'sample':
        import random
        from oc1_fast import drafts
        from oc1_k3 import profiles
        from oc1_max import sources as hypergraphs
        from lbtest import lb2
        src, NP, seed = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        shard, nsh = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (0, 1)
        rng = random.Random(seed * 1000 + shard)
        for ci, (sets, m) in enumerate(hypergraphs(src, rng)):
            if ci % nsh != shard: continue
            for rk in profiles(sets, NP, rng):
                for Y in drafts(rk, len(sets)):
                    if any(g is None for g in Y) or lb2(rk, m, base_of(Y, m)): continue
                    analyse(rk, m, Y, C)
    else:
        fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
        for li, line in enumerate(gzip.open(fn, 'rt')):
            if li % nsh != shard: continue
            mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
            if not mt or int(mt.group(5)) != 1: continue
            analyse([tuple(r) for r in json.loads(mt.group(1))], int(mt.group(2)), ast.literal_eval(mt.group(4)), C)
    for k in sorted(C): print(C[k], k)
