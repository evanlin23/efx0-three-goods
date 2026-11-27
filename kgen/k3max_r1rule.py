"""Class R1 of the residual (kgen/n3.md §15.17: T = {t}, E_t = {k, x} with {b_k, c_k} = {b_x, c_x}), |J| >= 3: which of
the two Rule E rotations reaches omega' <= 0 (after LB's upgrades), against simple rules: sigma-first twin, sigma-last
twin, shorter chain, longer chain, the rotation giving t its top.

    K3OC1=... python3 kgen/k3max_r1rule.py GAPFILE [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain

if __name__ == '__main__':
    print('$ python3 kgen/k3max_r1rule.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True); C = collections.Counter()
    fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    for li, line in enumerate(gzip.open(fn, 'rt')):
        if li % nsh != shard: continue
        mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or int(mt.group(5)) != 1: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]; E = exposed(rk, ub, t, B, J, U)
        if len(E) != 2 or set(rk[E[0]][1:]) != set(rk[E[1]][1:]) or len(J) < 3: continue
        pos = topo(rk, B, U); R = {}
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos); P2 = parts(rk, m, upgrade(rk, m, rotate(rk, ub, B, k, P)))
            R[k] = (len(P2[1]) - len(P2[5]) <= 0, len(P), B[P[-2]][0] == rk[t][0])
        a, b = sorted(E, key=lambda w: pos[w])
        C['R1 |J| >= 3 drafts'] += 1
        C['  sigma-first twin works'] += R[a][0]; C['  sigma-last twin works'] += R[b][0]
        s = min(E, key=lambda w: (R[w][1], pos[w])); l = max(E, key=lambda w: (R[w][1], -pos[w]))
        C['  shorter chain works'] += R[s][0]; C['  longer chain works'] += R[l][0]
        tt = [w for w in E if R[w][2]]
        C['  some twin gives t its top: %s' % bool(tt)] += 1
        if tt: C['  every twin giving t its top works: %s' % all(R[w][0] for w in tt)] += 1
        C['  pi inside J: %s' % (set(rk[a][1:]) <= set(J))] += 1
    for k in sorted(C): print(C[k], k)
