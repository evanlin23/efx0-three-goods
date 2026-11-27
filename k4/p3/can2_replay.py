"""Replay the failures of a CAN2 certification run (k4/p3/can2cert.py) with independent code (k4/p3/p3lib.py,
oc1max.py, keep2.py; no code of compute/k4-oc1max-cert). For every failing (profile, picks):
  - the picks are the serial-dictatorship outcome of some order, form a maximum matching, and every agent holds one;
  - they have no one-absorber completion (SAT, models re-checked raw);
  - for every frozen agent k and every improving H0 inside (J + {Y_z}) & R_k, the state after the canonical chain P(k)
    has no one-absorber completion (so CAN2 fails there);
  - which official moves do repair (oc1max.Checker: additions, chains, rings), with their kinds.
    python3 k4/p3/can2_replay.py CERT.json.gz
Hardness and the failure of every canonical chain are checked twice, by SAT and by plain enumeration of the junk's
owners; whether some ED chain (Hall's form: only the head may add junk) repairs is counted as well.
"""
import sys, os, gzip, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst, sd
from oc1max import Checker, nu
from keep2 import analyse, chain, state
from p3lib import efx0, bundles


def brute_complete(I, base):
    """one-absorber EFX0 completion of the bases by plain enumeration of the junk's owners (no SAT)"""
    held = set().union(*base); J = [g for g in range(I.m) if g not in held]
    for own in itertools.product(range(I.n), repeat=len(J)):
        c = collections.Counter(own)
        if sum(1 for a in c if c[a] >= 2) > 1: continue
        X = [list(b) for b in base]
        for g, a in zip(J, own): X[a].append(g)
        if efx0(I, X): return X
    return None



if __name__ == '__main__':
    D = json.load(gzip.open(sys.argv[1], 'rt'))
    cnt = collections.Counter(); first = None; noed = []
    print('$ python3 k4/p3/can2_replay.py ' + ' '.join(sys.argv[1:]))
    for rec in D['cores']:
        if rec['result'] == 'certified': continue
        for f in rec.get('fails', []):
            I = Inst(rec['sets'], f['vals']); Y = f['picks']; K = Checker(I)
            orders = [o for o in itertools.permutations(range(I.n)) if sd(I, o) == list(Y)]
            assert orders and sum(y is not None for y in Y) == nu(I) and None not in Y, 'not a perfect maximum SD start'
            base = tuple(frozenset([y]) for y in Y)
            assert K.complete(base) is None, 'picks complete'
            assert brute_complete(I, base) is None, 'picks complete (brute force)'
            J, p, w, F, Dg, DT, EJ = analyse(I, list(Y))
            for k in sorted(F):
                P = chain(w, k); z = P[-1]
                pool = [g for g in J if g in I.R[k]] + ([Y[z]] if Y[z] in I.R[k] else [])
                for r in range(1, len(pool) + 1):
                    for H0 in itertools.combinations(pool, r):
                        if I.val(k, H0) > p[k]:
                            cnt['canonical (chain, H0) tested'] += 1
                            assert K.complete(tuple(state(I, Y, P, H0))) is None, ('CAN2 holds here', P, H0)
                            assert brute_complete(I, tuple(state(I, Y, P, H0))) is None, ('CAN2 holds here (brute)', P, H0)
            kinds = collections.Counter(); reps = []
            for st, tag in K.moves(base).items():
                if K.complete(st) is not None:
                    assert brute_complete(I, st) is not None, 'SAT and brute force disagree'
                    kinds[tag[2] + (' of %d' % tag[1] if tag[2] != 'addition' else '')] += 1
                    reps.append([sorted(b) for b in st])
            # ED form (k4/oc1_hall.md): a chain x_0..x_t in which x_1..x_{t-1} take exactly their predecessor's pick
            # (only the head may add junk). Enumerated directly: path along wanters, head any agent gaining with junk.
            ed = 0
            for path in itertools.permutations(range(I.n)):
                for t in range(1, I.n):
                    Pth = path[:t + 1]
                    if any(I.v[Pth[i]].get(Y[Pth[i - 1]], 0) <= p[Pth[i]] for i in range(1, t)): continue
                    zz = Pth[t]; free = [g for g in J if g in I.R[zz]]
                    for Ht in (h for r in range(len(free) + 1) for h in itertools.combinations(free, r)):
                        if I.val(zz, [Y[Pth[t - 1]], *Ht]) <= p[zz]: continue
                        pool0 = [g for g in J if g not in Ht and g in I.R[Pth[0]]] + ([Y[zz]] if Y[zz] in I.R[Pth[0]] else [])
                        for H0 in (h for r in range(1, len(pool0) + 1) for h in itertools.combinations(pool0, r)):
                            if I.val(Pth[0], H0) <= p[Pth[0]]: continue
                            B = [frozenset([y]) for y in Y]; B[Pth[0]] = frozenset(H0)
                            for i in range(1, t + 1): B[Pth[i]] = frozenset([Y[Pth[i - 1]]])
                            B[zz] = B[zz] | frozenset(Ht)
                            if K.complete(tuple(B)) is not None: ed += 1
            cnt['ED chains repairing: ' + ('some' if ed else 'none')] += 1
            if not ed: noed.append({'sets': rec['sets'], 'vals': f['vals'], 'picks': Y, 'repairs': dict(kinds)})
            if I.m <= 8:                       # every move state: SAT and plain enumeration agree
                for st in K.moves(base):
                    cnt['move states cross-checked by enumeration (m <= 8)'] += 1
                    assert (K.complete(st) is None) == (brute_complete(I, st) is None), 'SAT and brute force disagree'
            cnt['failures replayed'] += 1
            cnt[f'|D| = {len(Dg)}, |D_T| = {len(DT)}'] += 1
            cnt['repaired by: ' + ', '.join(sorted(kinds)) if kinds else 'NOT REPAIRED BY ONE MOVE'] += 1
            key = (I.n, I.m)
            if first is None or key < first[0]:
                first = (key, {'sets': rec['sets'], 'vals': f['vals'], 'picks': Y, 'orders': orders[:3], 'J': J, 'D': sorted(Dg),
                               'D_T': sorted(DT), 'E_J': sorted(EJ), 'wanter': w, 'repairs': dict(kinds), 'repairing bases': reps})
            K.close()
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
    print('smallest', json.dumps(first[1]) if first else None)
    for e in noed: print('no repairing ED chain', json.dumps(e))
