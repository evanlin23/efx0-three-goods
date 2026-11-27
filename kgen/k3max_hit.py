"""B*'s count for owner k after the least-omega' Rule E rotation (kgen/n3.md §15.17).  On one-terminal hard drafts:
the distribution of (|E_t|, omega, least omega' over the Rule E rotations from E_t into t); and where least omega' >= 1,
for every least-omega' rotation: |T'|, |E'_k| = |E_t| - 1, exposed pairs equal to k's pair, the hitting number h of
{pair_x - pair_k}, and whether h <= |T'| (B*'s count for owner k).  Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/k3max_hit.py GAPFILE [SHARD NSHARDS]                  k3-oc1's gap lists (|T| = 1 lines)
    K3OC1=... python3 kgen/k3max_hit.py sample SOURCE PROFILES SEED [SHARD NSHARDS]  k3-oc1's sampler (te_sample.py),
                                                                                 every hard perfect one-terminal draft"""
import sys, os, json, re, ast, gzip, collections, random
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import parts, exposed, upgrade, lb2
from thm_bstar import mh
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain


def analyse(rk, m, Y, C, tag=''):
    ub = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, ub)
    if len(T) != 1: return
    t = T[0]; E = exposed(rk, ub, t, B, J, U); pos = topo(rk, B, U); rots = []
    for k in E:
        P = rule_e_chain(rk, B, U, k, t, pos)
        if P is None: C[tag + 'no Rule E chain from an exposed k (unexpected)'] += 1; continue
        nbu = upgrade(rk, m, rotate(rk, ub, B, k, P)); P2 = parts(rk, m, nbu)
        rots.append((len(P2[1]) - len(P2[5]), k, P2))
    if not rots: C[tag + 'no rotation'] += 1; print('NOROT', json.dumps(rk), m, Y, flush=True); return
    lo = min(r[0] for r in rots); om = len(J) - len(T)
    C[tag + '|E_t| = %d, omega = %d, least omega\' = %d' % (len(E), om, lo)] += 1
    if lo <= 0: return
    for om2, k, P2 in rots:
        if om2 != lo: continue
        B2, J2, U2, NA2, F2, T2 = P2; pk = {rk[k][1], rk[k][2]}; Ex = [x for x in E if x != k]
        same = sum(1 for x in Ex if {rk[x][1], rk[x][2]} == pk)
        h = mh([[g for g in (rk[x][1], rk[x][2]) if g not in pk] for x in Ex if {rk[x][1], rk[x][2]} != pk])
        ok = same == 0 and h <= len(T2)
        C[tag + '  least-omega\' >= 1 rotation: |T\'| = %d, |E\'_k| = %d, same pair %d, h = %d, owner-k count %s' % (len(T2), len(Ex), same, h, ok)] += 1
        if not ok: print('COUNTFAIL', json.dumps(rk), m, Y, 'k', k, flush=True)


if __name__ == '__main__':
    print('$ python3 kgen/k3max_hit.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True); C = collections.Counter()
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
