"""Check of Proposition A's proof (kgen/n3.md §15.17), step by step, on data (evidence for the write-up, not part of
the proof).  At a one-terminal perfect state P (after LB's upgrades) with |E_t| >= 2, for every k in E_t such that
  (alpha) no x in E_t - k has {b_x, c_x} = {b_k, c_k}, and (beta) the sets {b_x, c_x} - {b_k, c_k} (x in E_t - k) have
  a common good:
the Rule E chain from k exists and ends at t; the rotated state P' (no upgrades) is valid (every wanted good held
alone), its want graph is acyclic, E'_k = E_t - k with pi'_x = pair_x - pair_k, |T'| >= 1; and the explicit Lemma 1 (b)
completion (the common good to a terminal of P', every other junk good to k) is EFX0 for the values 4, 3, 2 (exact for
every strictly balanced profile: k4/k3_oc1.md §1).

    K3OC1=... python3 kgen/k3max_propA.py GAPFILE [SHARD NSHARDS]
    K3OC1=... python3 kgen/k3max_propA.py sample SOURCE PROFILES SEED [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, collections, random
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of, bundles, vals, efx0
from lbtest import parts, exposed, upgrade, lb2
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain


def wants(rk, B, U, i):
    if U[i]: return set()
    if not B[i]: return set(rk[i])
    return set(rk[i][:rk[i].index(B[i][0])])


def valid(rk, m, base):
    n = len(rk); B = bundles(base, n); U = [len(B[i]) == 2 for i in range(n)]
    for i in range(n):
        for g in wants(rk, B, U, i):
            if base[g] < 0 or len(B[base[g]]) != 1: return False
    return True


def acyclic(rk, base):
    n = len(rk); B = bundles(base, n); U = [len(B[i]) == 2 for i in range(n)]
    arc = {u: [w for w in range(n) if B[u] and not U[u] and B[u][0] in wants(rk, B, U, w)] for u in range(n)}
    col = [0] * n
    def dfs(u):
        col[u] = 1
        for w in arc[u]:
            if col[w] == 1 or (col[w] == 0 and not dfs(w)): return False
        col[u] = 2; return True
    return all(col[u] or dfs(u) for u in range(n))


def analyse(rk, m, Y, C, bad, tag=''):
    ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub)
    if len(T) != 1: return
    t = T[0]; E = exposed(rk, ub, t, B, J, U)
    if len(E) < 2: return
    pr = {x: frozenset(rk[x][1:]) for x in E}; pos = topo(rk, B, U); V = vals(rk); n = len(rk); hit = False
    for k in E:
        others = [x for x in E if x != k]
        if any(pr[x] == pr[k] for x in others): continue
        common = set.intersection(*[set(pr[x] - pr[k]) for x in others])
        if not common: continue
        hit = True; C['(alpha), (beta) hold for k'] += 1
        P = rule_e_chain(rk, B, U, k, t, pos); fails = []
        if P is None or P[-1] != t: fails.append('chain')
        else:
            nb = rotate(rk, ub, B, k, P); B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
            if not valid(rk, m, nb): fails.append('valid')
            if not acyclic(rk, nb): fails.append('acyclic')
            E2 = exposed(rk, nb, k, B2, J2, U2)
            if sorted(E2) != sorted(others): fails.append("E'_k")
            if any(set(rk[x][1:]) & set(J2) != set(pr[x] - pr[k]) for x in E2): fails.append("pi'")
            if not T2: fails.append("T' empty")
            else:
                X = [list(b) for b in B2]; g0 = min(common); X[T2[0]].append(g0)
                for g in J2:
                    if g != g0: X[k].append(g)
                if g0 not in J2 or not efx0(V, X): fails.append('completion')
        for f in fails: C['FAIL ' + f] += 1
        if fails and len(bad) < 5: bad.append((rk, m, Y, k, fails))
    C['drafts: some k with (alpha), (beta): %s' % hit] += 1


if __name__ == '__main__':
    print('$ python3 kgen/k3max_propA.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True)
    C = collections.Counter(); bad = []
    if sys.argv[1] == 'sample':
        from oc1_fast import drafts
        from oc1_k3 import profiles
        from oc1_max import sources as hypergraphs
        src, NP, seed = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        shard, nsh = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (0, 1)
        rng = random.Random(seed * 1000 + shard)
        for ci, (sets, m) in enumerate(hypergraphs(src, rng)):
            if ci % nsh != shard: continue
            for rk in profiles(sets, NP, rng):
                for Y in drafts(rk, len(sets)):
                    if any(g is None for g in Y) or lb2(rk, m, base_of(Y, m)): continue
                    analyse(rk, m, Y, C, bad)
    else:
        fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
        for li, line in enumerate(gzip.open(fn, 'rt')):
            if li % nsh != shard: continue
            mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
            if not mt or int(mt.group(5)) != 1: continue
            analyse([tuple(r) for r in json.loads(mt.group(1))], int(mt.group(2)), ast.literal_eval(mt.group(4)), C, bad)
    for k in sorted(C): print(C[k], k)
    for b in bad: print('BAD', json.dumps(b))
