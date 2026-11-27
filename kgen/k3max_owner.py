"""Which completion does the Rule E rotation from each k in E_t reach (kgen/n3.md §15.8)?  On k3-oc1's gap lists
(|T| = 1 lines): lb2's answer (no owner / owner k / owner t / another terminal / another pair holder; upgrades used),
and whether the simple test lb_simple (LB's maximal upgrades, then Lemma 1 (a), (b) or (c)) already passes.
Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_owner.py GAPFILE [SHARD NSHARDS [MAXLINES]]"""
import sys, os, json, re, ast, gzip, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, lb_simple, parts, exposed, upgrade
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain

if __name__ == '__main__':
    fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    maxl = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9; C = collections.Counter(); done = 0
    print('$ python3 kgen/k3max_owner.py', os.path.basename(fn), *sys.argv[2:], flush=True)
    for li, line in enumerate(gzip.open(fn, 'rt')):
        if li % nsh != shard: continue
        mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or int(mt.group(5)) != 1: continue
        done += 1
        if done > maxl: break
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]
        E = exposed(rk, ub, t, B, J, U); pos = topo(rk, B, U)
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P)
            res = lb2(rk, m, nb); jk = '|J| = %d: ' % len(J)
            if not res: C[jk + 'lb2 FAILS (contradicts T1-E)'] += 1; continue
            kind = res[0]
            if kind == 'owner':
                o = res[1]; T2 = parts(rk, m, nb)[5]
                kind = 'owner k' if o == k else ('owner t' if o == t else ('owner: another terminal' if o in T2 else 'owner: another pair holder'))
            ups = [x for x in res if isinstance(x, tuple) and x and x[0] == 'upgrades']
            nup = len(ups[0][1]) if ups else 0
            C[jk + 'lb2: %s, %s upgrade(s)' % (kind, nup)] += 1
            C[jk + 'simple test (LB upgrades, then Lemma 1) passes: %s' % bool(lb_simple(rk, m, nb, upgrades=True))] += 1
    for k in sorted(C): print(C[k], k)
