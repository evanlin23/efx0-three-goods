"""The second move of OC2^max (k4/oc1_hall.md §23), on the known OC1^max failures: the certifier's 11 n = 4 cores
(results/k4_oc1_hall/oc1max_cex_n4_from_cert.json, copied from compute/k4-oc1max-cert:results/k4_oc1max/oc1max_cex_n4.json),
the coordinator's cex2 and the TTC session's n = 5 strict core.  At the failing start:
  - D, and for each k in D whether J alone threatens k;
  - SHARED: pairs k != k' of D and an unfrozen z such that some minimal improving set T of k inside (J + B_z) & R_k is
    also improving for k' (v_{k'}(T) > p_{k'}): the shared pool danger sets of §22;
  - every repairing pair of sequential official moves (de_free.moves, chains and rings, then a one-absorber completion,
    SAT), classified by: is the first move a canonical chain (no middle or head junk) from a dangerous agent; after it,
    the DEMAND agents (dangerous at the picks, frozen after the first move, threatened by the junk plus the first
    agent's bundle); does the second move start at a DEMAND agent, at the first move's own first agent, or elsewhere.

    python3 k4/oc1_hall/oc2_cases.py
"""
import sys, os, json, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, threatened
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
DF.CHAIN_ONLY = False
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def instances():
    d = json.load(open(os.path.join(ROOT, 'results', 'k4_oc1_hall', 'oc1max_cex_n4_from_cert.json')))
    for x in d['instances']:
        yield '%s#%d' % (x['list'], x['idx']), x['sets'], x['vals'], tuple(x['picks'])
    yield 'coord-cex2', [[0,4,5,6],[1,2,3,5],[1,3,5,6],[2,4,6]], [[2,3,10,6],[3,10,6,8],[5,3,7,6],[4,3,2]], None, (3, 1, 2, 0)
    yield 'ttc-n5-core', [[0,4,5,6],[2,3,4,6],[0,1,5,6],[2,4,5,6],[0,1,7,8]], [[3,2,10,6],[4,1,6,8],[2,8,5,4],[5,4,8,2],[7,8,2,4]], None, (1, 3, 4, 2, 0)


def minimal_improving(I, k, pk, ground):
    imp = [H for r in range(1, len(ground) + 1) for H in itertools.combinations(ground, r) if I.val(k, H) > pk]
    return [H for H in imp if not any(set(K) < set(H) for K in imp)]


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/oc2_cases.py', flush=True)
    T = collections.Counter()
    for item in instances():
        name, sets, vals = item[0], item[1], item[2]
        m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m, name); E = Enc(sets, vals, m)
        if item[3] is not None: Y = item[3]
        else: Y = picks(I, item[4])
        P = Picks(I, Y); base = base_of_picks(I, Y); n = I.n
        assert not extends_A(E, base, 1)
        mv1 = DF.moves(E, base, describe=True, all_desc=True)
        assert not any(extends_A(E, b2, 1) for b2 in mv1)
        print('=====', name, 'n', n, 'm', m, 'picks', list(Y), 'J', P.J, 'F', P.F, 'D', P.D,
              'J alone threatens', [k for k in P.D if threatened(I, k, P.pv[k], P.J)], flush=True)
        shared = set()
        for z in range(n):
            if z in P.F: continue
            Pi = list(P.J) + ([Y[z]] if Y[z] is not None else [])
            for k in P.D:
                for Tset in minimal_improving(I, k, P.pv[k], [g for g in Pi if g in I.R[k]]):
                    for k2 in P.D:
                        if k2 != k and I.val(k2, Tset) > P.pv[k2]: shared.add((min(k, k2), max(k, k2), tuple(sorted(Tset)), z))
        print('  SHARED pool danger sets (k, k\', T, z):', sorted(shared))
        T['instances'] += 1; T['instances with a shared pool danger set'] += bool(shared)
        kinds = collections.Counter()
        for b2, ds in mv1.items():
            B2 = bundles_of(I, b2); F2 = set(frozen_set(I, b2)); J2 = [g for g in range(m) if b2[g] < 0]
            for kind, path, H in ds:
                x0 = path[0]
                canon = kind == 'chain' and x0 in P.D and all(not H.get(i) for i in range(1, len(path)))
                pool = list(B2[x0]) + J2
                demand = [q for q in P.D if q != x0 and q in F2 and threatened(I, q, I.val(q, B2[q]), pool)]
                for b3, ds3 in DF.moves(E, b2, describe=True, all_desc=True).items():
                    if not extends_A(E, b3, 1): continue
                    if canon:
                        B3 = bundles_of(I, b3); F3 = set(frozen_set(I, b3)); J3 = [g for g in range(m) if b3[g] < 0]
                        starts = {d3[1][0] for d3 in ds3}
                        how = []
                        for q in demand:
                            if q in starts: how.append('starts at it')
                            elif q not in F3: how.append('unfreezes it')
                            elif not threatened(I, q, I.val(q, B3[q]), J3 + [g for o in range(n) if len(B3[o]) >= 2 for g in B3[o] if o != q]): how.append('leaves it frozen, unthreatened')
                            else: how.append('other')
                        lab = 'no DEMAND after the first chain' if not demand else ('second move removes every DEMAND (starts at it or unfreezes it)' if all(h in ('starts at it', 'unfreezes it') for h in how) else 'second move leaves a DEMAND agent frozen: ' + ','.join(sorted(set(how))))
                        kinds[('LIFT', lab)] += 1
                    for kind3, path3, H3 in ds3:
                        y0 = path3[0]
                        where = 'a DEMAND agent' if y0 in demand else ('the same first agent' if y0 == x0 else
                                ('another agent of D' if y0 in P.D else ('an agent of F - D' if y0 in P.F else 'an agent unfrozen at the picks')))
                        canon3 = kind3 == 'chain' and all(not H3.get(i) for i in range(1, len(path3)))
                        if canon and kinds['shown2 ' + where] < 1 and where not in ('a DEMAND agent',):
                            kinds['shown2 ' + where] += 1
                            print('  e.g. first', kind, path, dict(H), 'DEMAND', demand, '; second (from %s)' % where, kind3, path3, dict(H3), 'canonical' if canon3 else '')
                        kinds[('first: canonical chain from D' if canon else 'first: other move', 'second from ' + where, 'DEMAND after first: %d' % len(demand))] += 1
                        if canon and y0 in demand and kinds['shown'] < 2:
                            kinds['shown'] += 1
                            print('  e.g. first', kind, path, dict(H), 'DEMAND', demand, '; second', kind3, path3, dict(H3))
        for kk, c in sorted((k, c) for k, c in kinds.items() if not str(k).startswith('shown')): print('  repairing pairs:', kk, c)
        T['instances repaired by a canonical first chain from D, then a move from a DEMAND agent'] += any(k[0].startswith('first: canonical') and k[1] == 'second from a DEMAND agent' for k in kinds if not str(k).startswith('shown'))
        T['instances repaired by a canonical first chain from D (any second move)'] += any(k[0].startswith('first: canonical') for k in kinds if not str(k).startswith('shown'))
        for lab in sorted({k[1] for k in kinds if not str(k).startswith('shown') and k[0] == 'LIFT'}): T['  instances with a repair (canonical first chain from D): %s' % lab] += 1
        firsts = {k[1] for k in kinds if not str(k).startswith('shown') and str(k[0]).startswith('first: canonical')}
        for w in sorted(firsts): T['  instances with a repair: canonical first chain from D, %s' % w] += 1
    for k, c in sorted(T.items()): print(k, c)
