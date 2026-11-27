"""Twins (class R1, kgen/n3.md §15.17-§15.19) and owner t.  For each twin k (E_t = {k, x}, pi_k = pi_x), k's Rule E
chain with t last, and the rotated state P' (no upgrades): N = the frozen exposed agents of t in P' (by G7 all hold
their top with pair {g, j}, g = t's new good); whether Lemma 3 holds for owner t; the kinds (b)/(c) of N; |T'|.
Rules tested for the choice of twin: sigma-first, sigma-last, longer chain, shorter chain, t gets its top, N empty.

    K3OC1=... python3 kgen/k3max_twins_t.py GAPFILE [SHARD NSHARDS]"""
import sys, os, json, re, ast, gzip, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade
from thm_bstar import mh
from k3max_t1 import rotate
from k3max_ruleE import rule_e_chain
from k3max_propB import topo_last

if __name__ == '__main__':
    print('$ python3 kgen/k3max_twins_t.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True); C = collections.Counter()
    fn = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1); shown = 0
    for li, line in enumerate(gzip.open(fn, 'rt')):
        if li % nsh != shard: continue
        mt = re.match(r'GAP (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or int(mt.group(5)) != 1: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]; E = exposed(rk, ub, t, B, J, U)
        if len(E) != 2 or set(rk[E[0]][1:]) != set(rk[E[1]][1:]): continue
        pos = topo_last(rk, B, U, t); R = {}
        for k in E:
            P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P); B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
            g = B2[t][0]; Eo = exposed(rk, nb, t, B2, J2, U2); N = [y for y in Eo if y in F2]
            ok = mh([[h for h in rk[y][1:] if h in J2] for y in N]) <= len([z for z in T2 if z not in Eo]) - 1
            R[k] = dict(ok=ok, N=N, L=len(P), top=(g == rk[t][0]), T=len(T2), kinds=''.join(sorted('c' if y in P else 'b' for y in N)), P=P, g=g)
            C['twin rotation: |N| = %d (%s), |T\'| = %d, t gets top %s, Lemma 3 for t %s' % (len(N), R[k]['kinds'], len(T2), R[k]['top'], ok)] += 1
        a, b = sorted(E, key=lambda w: pos[w])
        C['drafts'] += 1
        for name, w in (('sigma-first', a), ('sigma-last', b), ('longer chain', max(E, key=lambda w: (R[w]['L'], -pos[w]))), ('shorter chain', min(E, key=lambda w: (R[w]['L'], pos[w])))):
            C['rule %s passes' % name] += R[w]['ok']
        C['some twin passes'] += any(R[w]['ok'] for w in E)
        tt = [w for w in E if R[w]['top']]
        C['some twin gives t its top: %s' % bool(tt)] += 1
        if tt: C['  then every such twin passes: %s' % all(R[w]['ok'] for w in tt)] += 1
        C['some twin leaves N empty: %s' % any(not R[w]['N'] for w in E)] += 1
        if not all(R[w]['ok'] for w in E) and shown < 3:
            shown += 1; print('EX', ' '.join('%d:%s' % (i, '>'.join(map(str, r))) for i, r in enumerate(rk)), 'picks', Y, 'J', J, 't', t, {w: (R[w]['P'], R[w]['g'], R[w]['N'], R[w]['ok']) for w in E})
    for k in sorted(C): print(C[k], k)
