"""The cross ring at the crossed starts (k4/p3.md section 6, the CAN2 failures): two trees with roots z1, z2 and
dangerous agents d1 (in z1's tree, threatened through Y_{z2}) and d2 (in z2's tree, threatened through Y_{z1}).
The cross ring is the official chain d1 -> P(d1) up to z1 -> d2 -> P(d2) up to z2, closed at d1:
  - every agent of P(d1) and P(d2) other than d1, d2 takes its child's pick (it wants it);
  - d2 takes Y_{z1} plus junk H2 (worth more than p_{d2});
  - d1 takes Y_{z2} plus junk H0 (worth more than p_{d1}).
Tests, for every failure record of a CAN2 certificate (k4/p3/can2cert.py), every such (H0, H2): does the state have a
one-absorber completion (SAT, k4/p3/oc1max.Checker, models re-checked raw)?
    python3 k4/p3/cross2.py CERT.json.gz
"""
import sys, os, gzip, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst
from oc1max import Checker
from keep2 import analyse, chain, threatened

if __name__ == '__main__':
    D = json.load(gzip.open(sys.argv[1], 'rt')); cnt = collections.Counter()
    print('$ python3 k4/p3/cross2.py ' + ' '.join(sys.argv[1:]))
    for rec in D['cores']:
        if rec['result'] == 'certified': continue
        for f in rec['fails']:
            I = Inst(rec['sets'], f['vals']); Y = f['picks']; K = Checker(I)
            J, p, w, F, Dg, DT, EJ = analyse(I, Y)
            U = [i for i in range(I.n) if i not in F]
            ok = False; tried = 0
            for d1, d2 in itertools.permutations(sorted(Dg), 2):
                P1, P2 = chain(w, d1), chain(w, d2); z1, z2 = P1[-1], P2[-1]
                if z1 == z2 or set(P1) & set(P2): continue
                if Y[z1] not in I.R[d2] or Y[z2] not in I.R[d1]: continue
                J2 = [g for g in J if g in I.R[d2]]
                for H2 in (h for r in range(len(J2) + 1) for h in itertools.combinations(J2, r)):
                    if I.val(d2, (Y[z1],) + H2) <= p[d2]: continue
                    J1 = [g for g in J if g in I.R[d1] and g not in H2]
                    for H0 in (h for r in range(len(J1) + 1) for h in itertools.combinations(J1, r)):
                        if I.val(d1, (Y[z2],) + H0) <= p[d1]: continue
                        B = [frozenset([y]) for y in Y]
                        for P in (P1, P2):
                            for i in range(1, len(P)): B[P[i]] = frozenset([Y[P[i - 1]]])
                        B[d2] = frozenset((Y[z1],) + H2); B[d1] = frozenset((Y[z2],) + H0)
                        tried += 1
                        if K.complete(tuple(B)) is not None: ok = True
            cnt['crossed starts'] += 1; cnt['cross rings tried'] += tried
            cnt['some cross ring repairs' if ok else 'no cross ring repairs' if tried else 'no cross ring exists'] += 1
            K.close()
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
