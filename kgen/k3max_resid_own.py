"""Residual of Proposition A (kgen/n3.md §15.17), terminal owners after one Rule E rotation, before LB's upgrades:
for each rotation from k in E_t, the terminals o of P' with Lemma 3's condition h(E'_o ∩ F') <= |T' - E'_o| - 1
(base condition automatic for a terminal), in particular those with no frozen exposed agent (E'_o ∩ F' empty), and
whether o = t is one.  Also whether the rotation passes Lemma 1 (a) (no owner) before upgrades.

    K3OC1=... python3 kgen/k3max_resid_own.py GAPFILE [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade
from thm_bstar import mh
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain

if __name__ == '__main__':
    print('$ python3 kgen/k3max_resid_own.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True); C = collections.Counter()
    fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    for li, line in enumerate(gzip.open(fn, 'rt')):
        if li % nsh != shard: continue
        mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or int(mt.group(5)) != 1: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]; E = exposed(rk, ub, t, B, J, U)
        if len(E) < 2 or len(J) < 3: continue
        pr = {x: frozenset(rk[x][1:]) for x in E}
        if any(not any(pr[x] == pr[k] for x in E if x != k) and mh([list(pr[x] - pr[k]) for x in E if x != k]) <= 1 for k in E): continue
        cls = 'R1' if len(E) == 2 else 'R2'; pos = topo(rk, B, U); C[cls + ' drafts (|J| >= 3)'] += 1; anyrot = anyrot_t = anyrot_e = False
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P); B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
            good, empty = [], []
            for o in T2:
                Eo = exposed(rk, nb, o, B2, J2, U2); Ef = [x for x in Eo if x in F2]
                if not Ef: empty.append(o)
                if mh([[g for g in rk[x][1:] if g in J2] for x in Ef]) <= len([z for z in T2 if z not in Eo]) - 1: good.append(o)
            a = len(J2) <= len(T2)
            C[cls + '  rotation: no owner (pre-upgrade) %s, a terminal owner by Lemma 3 %s, t is one %s, some terminal with no frozen exposed %s' % (a, bool(good), t in good, bool(empty))] += 1
            anyrot |= a or bool(good); anyrot_t |= (t in good); anyrot_e |= bool(empty)
        C[cls + ' some rotation completes by (a) or a Lemma 3 terminal owner: %s' % anyrot] += 1
        C[cls + ' some rotation has owner t by Lemma 3: %s' % anyrot_t] += 1
        C[cls + ' some rotation leaves a terminal with no frozen exposed agent: %s' % anyrot_e] += 1
    for k in sorted(C): print(C[k], k)
