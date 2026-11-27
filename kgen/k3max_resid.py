"""The residual of Proposition A (kgen/n3.md §15.17): one-terminal hard states with |E_t| >= 2 in which no k in E_t has
(alpha) no equal exposed pair and (beta) a common good of the sets pair_x - pair_k.  Class R1: |E_t| = 2 with equal
pairs; class R2: |E_t| >= 3.  For each Rule E rotation from k in E_t: omega' after LB's upgrades, and whether it
passes owner none or k (kgen/k3max_owner.own_none_or_k).  Reports how many k reach omega' <= 0 and whether every k
does, and for R2 whether some k with (alpha) has h_k <= |T'| (B*'s count for owner k).

    K3OC1=... python3 kgen/k3max_resid.py GAPFILE [SHARD NSHARDS]
    K3OC1=... python3 kgen/k3max_resid.py sample SOURCE PROFILES SEED [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, collections, random
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade, lb2
from thm_bstar import mh
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain
from k3max_owner import own_none_or_k


def analyse(rk, m, Y, C, tag=''):
    ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub)
    if len(T) != 1: return
    t = T[0]; E = exposed(rk, ub, t, B, J, U)
    if len(E) < 2: return
    pr = {x: frozenset(rk[x][1:]) for x in E}; al = {}; hk = {}
    for k in E:
        others = [x for x in E if x != k]; al[k] = not any(pr[x] == pr[k] for x in others)
        hk[k] = mh([list(pr[x] - pr[k]) for x in others if pr[x] != pr[k]])
    if any(al[k] and hk[k] <= 1 for k in E): return
    cls = 'R1' if len(E) == 2 else 'R2 |E_t| = %d' % len(E)
    pos = topo(rk, B, U); res = []
    for k in E:
        P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P); P2 = parts(rk, m, upgrade(rk, m, nb))
        res.append((k, len(P2[1]) - len(P2[5]), len(P2[5]), own_none_or_k(rk, m, nb, k), len(P) - 1))
    nz = sum(1 for r in res if r[1] <= 0)
    C['%s, |J| = %d: %d of %d rotations reach omega\' <= 0' % (cls, len(J), nz, len(E))] += 1
    if not nz: print('NONE', json.dumps(rk), m, Y, flush=True)
    if cls != 'R1':
        cnt = any(al[k] and hk[k] <= T2 for k, o, T2, ok, L in res)
        C['%s: some k with (alpha) and h_k <= |T\'_k|: %s' % (cls, cnt)] += 1
        C['%s: some rotation passes owner none/k: %s' % (cls, any(r[3] for r in res))] += 1


if __name__ == '__main__':
    print('$ python3 kgen/k3max_resid.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True); C = collections.Counter()
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
                    analyse(rk, m, Y, C)
    else:
        fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
        for li, line in enumerate(gzip.open(fn, 'rt')):
            if li % nsh != shard: continue
            mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
            if not mt or int(mt.group(5)) != 1: continue
            analyse([tuple(r) for r in json.loads(mt.group(1))], int(mt.group(2)), ast.literal_eval(mt.group(4)), C)
    for k in sorted(C): print(C[k], k)
