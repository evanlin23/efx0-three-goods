"""T1' and Lemma G5 on k3-oc1's gap lists (results/k4_k3oc1/gap_*.gap.gz on branch claude/k4-k3-oc1): for every GAP
line with |T| = 1, check (kgen/n3.md §15.6):
  - Lemma G5: the Rule E rotation from every k in E_t keeps the want graph acyclic;
  - T1' with Rule E: some k in E_t reaches |J'| <= |T'| after LB's upgrades;
  - T1' over all need chains (only when Rule E fails, as a fallback);
  - T1 with an owner allowed (lbtest.lb2 after the Rule E rotation), for every k and for some k.
Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_gapfile.py GAPFILE [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, collections, time
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, parts, exposed, upgrade
from thm_bstar import chains_to
from k3max_t1 import rotate
from k3max_t1acyc import acyclic
from k3max_ruleE import topo, rule_e_chain

if __name__ == '__main__':
    fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter(); t0 = time.time(); shown = 0
    print('$ python3 kgen/k3max_gapfile.py', os.path.basename(fn), *sys.argv[2:], flush=True)
    for li, line in enumerate(gzip.open(fn, 'rt')):
        if li % nsh != shard: continue
        mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt: continue
        if int(mt.group(5)) != 1: C['gap lines with |T| != 1 (not this part)'] += 1; continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4)); n = len(rk)
        ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub)
        if len(T) != 1: C['|T| != 1 on recomputation (MISMATCH)'] += 1; continue
        t = T[0]; E = exposed(rk, ub, t, B, J, U); C['gap drafts with |T| = 1'] += 1; C['  |J| = %d' % len(J)] += 1
        pos = topo(rk, B, U); allac = True; best = None
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos)
            if P is None: C['  Rule E chain does not reach t (MISMATCH)'] += 1; continue
            nb = rotate(rk, ub, B, k, P); P2 = parts(rk, m, nb); allac &= acyclic(rk, P2[0], P2[2])
            P3 = parts(rk, m, upgrade(rk, m, nb)); om = len(P3[1]) - len(P3[5]); best = om if best is None else min(best, om)
        C['  Lemma G5: Rule E keeps the want graph acyclic for every k: %s' % allac] += 1
        lbk = []
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos)
            if P is not None: lbk.append(bool(lb2(rk, m, rotate(rk, ub, B, k, P))))
        C['  T1-E (owner allowed): the Rule E rotation completes (lb2) for EVERY k: %s' % all(lbk)] += 1
        C['  T1 (owner allowed): the Rule E rotation completes (lb2) for SOME k: %s' % any(lbk)] += 1
        if not any(lbk):
            anyr = False
            for k in E:
                for P in chains_to(rk, B, U, k, t):
                    if lb2(rk, m, rotate(rk, ub, B, k, P)): anyr = True; break
                if anyr: break
            C['  T1 over all need chains into t (owner allowed), when Rule E fails for every k: %s' % anyr] += 1
            if shown < 6:
                shown += 1; print('RULE E FAILS EVEN WITH AN OWNER', line.strip(), 'some chain into t works:', anyr, flush=True)
        okE = best is not None and best <= 0
        C['  T1\' with Rule E (some k): %s' % okE] += 1
        if not okE:
            anyok = False
            for k in E:
                for P in chains_to(rk, B, U, k, t):
                    P3 = parts(rk, m, upgrade(rk, m, rotate(rk, ub, B, k, P)))
                    if len(P3[1]) <= len(P3[5]): anyok = True; break
                if anyok: break
            C['  T1\' over all need chains (Rule E failed): %s' % anyok] += 1
            if shown < 3:
                shown += 1; print('RULE E T1\' FAILS', line.strip(), 'all chains:', anyok, flush=True)
    for k in sorted(C): print(C[k], k)
    print('time %.0f s' % (time.time() - t0))
