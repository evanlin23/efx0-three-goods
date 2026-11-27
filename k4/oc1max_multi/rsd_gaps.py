"""The obstruction to RSD at kgen-rounds' REC-S gaps (k4/oc1max_multi.md §16): for each start, every settlement
available by an earliest-wanter chain (pair, or triple with (L*)), and for each the number of completions of the reduced
instance after at most one official move, and how many of them lift (raw EFX0 in the full instance, the settled agent
keeping its set); then the same after a second settlement.

    python3 k4/oc1max_multi/rsd_gaps.py ROWS.jsonl     (rows: sets, vals, picks, orders, list, idx)
"""
import sys, os, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous, moves, oa_absorbers
from reduce_s import earliest_chain
from dred import apply_chain
from reduce_check import reduced


def settle(I, b, order):
    J = junk(I, b); p = [I.V(i, b[i]) for i in range(I.n)]
    for k in dangerous(I, b):
        P = earliest_chain(I, b, k, order)
        pool = [g for g in J + list(b[P[-1]]) if g in I.R[k]]
        for T in [T for r in (2, 3) for T in itertools.combinations(pool, r)]:
            if I.V(k, T) <= p[k]: continue
            nb = apply_chain(I, b, P, T)
            thr = [i for i in range(I.n) if i != k and I.threat(i, I.V(i, nb[i]), T)]
            if len(T) == 3 and thr:
                yield k, P, T, None, None, None, None, thr; continue
            I2, b2, keep = reduced(I, nb, k)
            yield k, P, T, I2, b2, keep, [keep.index(a) for a in order if a != k], []


def lifts(I, fixed, I3, b3, lab_a, lab_g):
    tot = ok = 0
    for B3 in [b3] + list(moves(I3, b3)):
        for o, X in oa_absorbers(I3, B3, want_witness=True).items():
            A = [list(fixed.get(a, [])) for a in range(I.n)]
            for j, a in enumerate(lab_a): A[a] = [lab_g[g] for g in X[j]]
            tot += 1; ok += I.efx0(A)
    return tot, ok


if __name__ == '__main__':
    print('$ python3 k4/oc1max_multi/rsd_gaps.py', *sys.argv[1:])
    for line in open(sys.argv[1]):
        r = json.loads(line); I = Inst(r['sets'], r['vals']); b = base_from_picks(tuple(r['picks']))
        print('%s#%s picks %s dangerous %s' % (r.get('list'), r.get('idx'), r['picks'], dangerous(I, b)))
        seen = set()
        for o in r['orders']:
            for k, P, T, I2, b2, keep, o2, thr in settle(I, b, o):
                if (k, P, T) in seen: continue
                seen.add((k, P, T))
                if I2 is None: print('   settle %d by %s, T %s: triple fails (L*), threatens %s' % (k, P, T, thr)); continue
                g1 = [g for g in range(I.m) if g not in set(T)]
                tot, ok = lifts(I, {k: list(T)}, I2, b2, keep, g1)
                sec = []
                for k2, P2, T2, I3, b3, keep3, o3, thr2 in settle(I2, b2, o2):
                    if I3 is None: sec.append('second %d: triple fails (L*)' % keep[k2]); continue
                    g2 = [g1[g] for g in range(I2.m) if g not in set(T2)]
                    t2, k2ok = lifts(I, {k: list(T), keep[k2]: [g1[g] for g in T2]}, I3, b3, [keep[a] for a in keep3], g2)
                    sec.append('second %d by %s, T %s: %d completions, %d lift' % (keep[k2], tuple(keep[a] for a in P2), tuple(g1[g] for g in T2), t2, k2ok))
                print('   settle %d by %s, T %s: %d completions of I- after <= 1 move, %d lift; second settlements: %s'
                      % (k, P, T, tot, ok, sec if sec else 'none possible'))
