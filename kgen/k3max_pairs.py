"""The exposed pairs of the terminal at one-terminal hard drafts (kgen/n3.md §15.17).  For T = {t} and E_t: the shape
of the pairs {b_x, c_x} (x in E_t) relative to Y_t (how many contain Y_t, how many lie in J, repeated pairs), and for
each k in E_t the owner-k count h_k = h({pair_x - pair_k : x in E_t - k}) with 'same_k' (a pair equal to k's).  Reports
whether some k has h_k <= 1 and no equal pair (then owner k completes after any Rule E rotation from k, since
|T'| >= 1: §15.17), and the least omega' of the Rule E rotations otherwise.

    K3OC1=... python3 kgen/k3max_pairs.py GAPFILE [SHARD NSHARDS]
    K3OC1=... python3 kgen/k3max_pairs.py sample SOURCE PROFILES SEED [SHARD NSHARDS]"""
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
    yt = B[t][0]; pr = {x: frozenset((rk[x][1], rk[x][2])) for x in E}
    nY = sum(1 for x in E if yt in pr[x]); rep = len(E) - len(set(pr.values()))
    hk = {}
    for k in E:
        same = any(pr[x] == pr[k] for x in E if x != k)
        hk[k] = (same, mh([list(pr[x] - pr[k]) for x in E if x != k and pr[x] != pr[k]]))
    good = [k for k in E if not hk[k][0] and hk[k][1] <= 1]
    C[tag + '|E_t| = %d, %d pairs contain Y_t, %d repeated; some k with h_k <= 1, no equal pair: %s' % (len(E), nY, rep, bool(good))] += 1
    if not good:
        pos = topo(rk, B, U); oms = []; okk = []
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P); nbu = upgrade(rk, m, nb); P2 = parts(rk, m, nbu)
            oms.append(len(P2[1]) - len(P2[5])); okk.append(own_none_or_k(rk, m, nb, k))
        lo = min(oms)
        C[tag + '   no such k: least omega\' = %d; a least-omega\' rotation passes owner none/k: %s' % (lo, any(o for o, w in zip(okk, oms) if w == lo))] += 1
        if lo > 0: print('NOK', json.dumps(rk), m, Y, 'E_t', E, flush=True)


if __name__ == '__main__':
    print('$ python3 kgen/k3max_pairs.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True); C = collections.Counter()
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
                    C['hard perfect drafts'] += 1; analyse(rk, m, Y, C)
    else:
        fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
        for li, line in enumerate(gzip.open(fn, 'rt')):
            if li % nsh != shard: continue
            mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
            if not mt or int(mt.group(5)) != 1: continue
            analyse([tuple(r) for r in json.loads(mt.group(1))], int(mt.group(2)), ast.literal_eval(mt.group(4)), C)
    for k in sorted(C): print(C[k], k)
