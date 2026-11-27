"""Owner t after one Rule E rotation (kgen/n3.md §15.18), before LB's upgrades.  For every Rule E rotation from k in
E_t into t at a one-terminal gap draft (|E_t| >= 2): is t a terminal of P' (nobody wants the good g = Y_{x_{s-1}} it
received)?  The frozen exposed agents E'_t ∩ F' of t in P', by type:
  (a) old exposed agents x in E_t - k (pair disjoint from pi_k),
  (b) non-receivers whose pair contains g,
  (c) receivers that got their top;
and whether Lemma 3 holds for owner t.  Split by the class of the draft (A: Proposition A applies; R1 twins; R2).

    K3OC1=... python3 kgen/k3max_ownt.py GAPFILE [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade
from thm_bstar import mh
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain

if __name__ == '__main__':
    print('$ python3 kgen/k3max_ownt.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True); C = collections.Counter()
    fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    for li, line in enumerate(gzip.open(fn, 'rt')):
        if li % nsh != shard: continue
        mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or int(mt.group(5)) != 1: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]; E = exposed(rk, ub, t, B, J, U)
        if len(E) < 2: continue
        pr = {x: frozenset(rk[x][1:]) for x in E}
        A = any(not any(pr[x] == pr[k] for x in E if x != k) and mh([list(pr[x] - pr[k]) for x in E if x != k]) <= 1 for k in E)
        cls = 'A ' if A else ('R1' if len(E) == 2 else 'R2'); pos = topo(rk, B, U); some = False
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P); B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
            g = B2[t][0]; tT = t in T2
            if not tT:
                C[cls + ' rotation: t frozen in P\''] += 1; continue
            Eo = exposed(rk, nb, t, B2, J2, U2); Ef = [x for x in Eo if x in F2]
            ty = collections.Counter('a' if x in E else ('c' if x in P else 'b') for x in Ef)
            ok = mh([[h for h in rk[x][1:] if h in J2] for x in Ef]) <= len([z for z in T2 if z not in Eo]) - 1
            some |= ok
            C[cls + ' rotation: t terminal; frozen exposed of t: a %d b %d c %d; Lemma 3 for t %s' % (ty['a'], ty['b'], ty['c'], ok)] += 1
        C[cls + ' drafts, |J| %s 3: some rotation has owner t by Lemma 3: %s' % ('>=' if len(J) >= 3 else '<', some)] += 1
    for k in sorted(C): print(C[k], k)
