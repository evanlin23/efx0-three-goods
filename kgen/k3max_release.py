"""What the least-omega' Rule E rotation releases at one terminal (kgen/n3.md §15.14).  For every |T| = 1 line of
k3-oc1's gap lists: over the Rule E rotations from k in E_t, the least omega' after LB's upgrades (the release bound
(R): least omega' <= 1).  For a least-omega' rotation, each released good (wanted before, wanted by nobody after the
rotation and its upgrades) is classified by its former wanters: t only, chain agents only (not t), t and chain
agents, or with an agent upgraded after the rotation.  Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_release.py GAPFILE [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain


def wanters(rk, B, U):
    n = len(rk); W = collections.defaultdict(set)
    for j in range(n):
        if U[j] or not B[j]: continue
        for g in rk[j][:rk[j].index(B[j][0])]: W[g].add(j)
    return W


if __name__ == '__main__':
    fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter()
    print('$ python3 kgen/k3max_release.py', os.path.basename(fn), *sys.argv[2:], flush=True)
    for li, line in enumerate(gzip.open(fn, 'rt')):
        if li % nsh != shard: continue
        mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or int(mt.group(5)) != 1: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]
        E = exposed(rk, ub, t, B, J, U); pos = topo(rk, B, U); W0 = wanters(rk, B, U)
        omega = len(J) - len(T); best = None
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P); nbu = upgrade(rk, m, nb)
            B2, J2, U2, NA2, F2, T2 = parts(rk, m, nbu); om = len(J2) - len(T2)
            if best is None or om < best[0]: best = (om, k, P, nb, nbu)
        om, k, P, nb, nbu = best; jk = '|J| = %d: ' % len(J)
        C[jk + 'drafts'] += 1; C[jk + 'least omega\' = %d (omega = %d)' % (om, omega)] += 1
        B1, J1, U1 = parts(rk, m, nb)[:3]; B2, J2, U2 = parts(rk, m, nbu)[:3]
        W2 = wanters(rk, B2, U2); upg = {i for i in range(len(rk)) if U2[i] and not U1[i]}
        for g, ws in W0.items():
            if W2.get(g): continue
            cat = ('with an upgraded agent' if ws & upg else
                   't only' if ws == {t} else 'chain agents only' if t not in ws and ws <= set(P) else
                   't and chain agents' if ws <= set(P) else 'OTHER (an off-chain wanter stopped wanting: impossible)')
            C[jk + 'released goods, former wanters: ' + cat] += 1
        C[jk + 'release count r = %d, need omega - 1 = %d' % (omega - om, omega - 1)] += 1
    for k in sorted(C): print(C[k], k)
