"""The one-terminal gap of OC1 at maximum-matching starts, k = 3 (kgen/n3.md §15): hard perfect drafts with |T| = 1
after LB's upgrades, covered by neither Theorem R1C nor Theorem B* (k4/k3_oc1.md §3 on claude/k4-k3-oc1).  With
T = {t}, B* applies exactly when |E_t| = 1, so the gap is |E_t| >= 2.

Candidate rule tested: rotate some exposed agent k in E_t along a need chain k = x0 -> ... -> xs = t.  Each x_i takes
Y_{x_{i-1}}, k takes its pair {b_k, c_k} (from J, or from J + {Y_t}: a ring with one pair arrow), and t's pick is
released.  Recorded:
  - does some such rotation give a state that lbtest.lb2 completes?  Does every one?
  - does the rotation that gives t its most preferred good work (ties: any)?
  - after a repairing rotation: does Lemma 1 hold with no owner (|J'| <= |T'|), or does it need an owner?
  - does every rotation of least omega' = |J'| - |T'| (after LB's upgrades, or before) repair?
Needs k4/k3oc1/ from branch claude/k4-k3-oc1 (K3OC1, as in kgen/k3max_cover.py).

    K3OC1=... python3 kgen/k3max_t1.py small:4|certs:5 [SHARD NSHARDS]"""
import sys, os, json, collections, time
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K)
from k3lib import base_of
from de_moves import de_trades
from lbtest import lb2, parts, exposed, upgrade
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles
from r1compat import r1_compatible
from thm_bstar import bstar, chains_to


def rotate(rk, b, B, k, P):
    nb = list(b); t = P[-1]
    for g in B[t]: nb[g] = -1
    for s in range(len(P) - 1, 0, -1): nb[B[P[s - 1]][0]] = P[s]
    nb[rk[k][1]] = k; nb[rk[k][2]] = k
    return tuple(nb)


if __name__ == '__main__':
    src = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 kgen/k3max_t1.py', *sys.argv[1:], flush=True)
    for ci, (sets, m) in enumerate(hypergraphs(src, None)):
        if ci % nsh != shard: continue
        n = len(sets)
        for rk in profiles(sets, 0, None):
            for Y in drafts(rk, n):
                if None in Y: continue
                b = base_of(Y, m)
                if lb2(rk, m, b): continue
                if r1_compatible(rk, Y): continue
                bs, found = bstar(rk, m, Y)
                if found and any(f[3] for f in found): continue
                ub = upgrade(rk, m, b); B, J, U, NA, F, T = parts(rk, m, ub)
                if len(T) != 1: C['gap drafts with |T| != 1'] += 1; continue
                t = T[0]; E = exposed(rk, ub, t, B, J, U)
                C['gap drafts (|T| = 1)'] += 1; C['  |E_t| = %d' % len(E)] += 1
                rots = []
                for k in E:
                    for P in chains_to(rk, B, U, k, t):
                        nb = rotate(rk, ub, B, k, P)
                        newt = B[P[-2]][0]
                        rots.append((k, tuple(P), rk[t].index(newt), bool(lb2(rk, m, nb)), nb))
                C['  rotations from E_t into t exist'] += bool(rots)
                if rots:
                    om = []
                    for r in rots:
                        P2 = parts(rk, m, upgrade(rk, m, r[4])); om.append(len(P2[1]) - len(P2[5]))
                    lo = min(om)
                    C['  every least-omega rotation into t (omega after upgrades) repairs'] += all(r[3] for r, o in zip(rots, om) if o == lo)
                    P2 = [parts(rk, m, r[4]) for r in rots]; om0 = [len(p[1]) - len(p[5]) for p in P2]; lo0 = min(om0)
                    C['  every least-omega rotation into t (omega before upgrades) repairs'] += all(r[3] for r, o in zip(rots, om0) if o == lo0)
                    C['  least omega after a repairing rotation <= 0 %s' % (min(o for r, o in zip(rots, om) if r[3]) <= 0 if any(r[3] for r in rots) else 'n/a')] += 1
                ok = [r for r in rots if r[3]]
                C['  some rotation from E_t into t repairs'] += bool(ok)
                C['  every rotation from E_t into t repairs'] += bool(rots) and len(ok) == len(rots)
                if rots:
                    best = min(r[2] for r in rots)
                    bestok = all(r[3] for r in rots if r[2] == best)
                    C['  every rotation giving t its best reachable good repairs'] += bestok
                    if not bestok and shown['best'] < 3:
                        shown['best'] += 1
                        print('BEST-FOR-T ROTATION FAILS', json.dumps([list(x) for x in rk]), m, 'picks', Y, 'J', J, 'T', T, 'E_t', E,
                              'rotations (k, chain, rank of t\'s new good, repairs):', [(r[0], r[1], r[2], r[3]) for r in rots], flush=True)
                    C['  t gets its top in some repairing rotation'] += any(r[2] == 0 for r in ok)
                    C['  t gets its top in some rotation'] += any(r[2] == 0 for r in rots)
                for r in ok[:1]:
                    B2, J2, U2, NA2, F2, T2 = parts(rk, m, upgrade(rk, m, r[4]))
                    C['  first repairing rotation: no owner needed (|J\'| <= |T\'|) %s' % (len(J2) <= len(T2))] += 1
                if not ok and shown['norot'] < 3:
                    shown['norot'] += 1
                    print('NO REPAIRING ROTATION', json.dumps([list(x) for x in rk]), m, 'picks', Y, 'J', J, 'T', T, 'E_t', E, 'rotations', [(r[0], r[1]) for r in rots], flush=True)
                    for nb, d in de_trades(rk, m, b):
                        if lb2(rk, m, nb): print('    a repairing DE trade:', d, flush=True)
    for k in sorted(C): print(C[k], k)
    print('time %.0f s' % (time.time() - t0))
