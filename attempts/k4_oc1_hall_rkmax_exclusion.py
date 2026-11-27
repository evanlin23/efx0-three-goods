"""Repro for attempts/k4-oc1-hall-rkmax-exclusion.md: a sigma-maximal maximum-matching SD vector with one receiver and
two truly dangerous agents at n = 5 (5_pure idx 358).  Uses only the raw checker k4/sdc/oc1_mc2_rand.Inst.
    python3 attempts/k4_oc1_hall_rkmax_exclusion.py      (exit status 0 iff the configuration is as stated)"""
import sys, os, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k4', 'sdc'))
from oc1_mc2_rand import Inst
sets = [[0, 1, 4, 5], [1, 3, 6, 7], [2, 3, 6, 7], [2, 4, 5, 7], [4, 5, 6, 7]]
vals = [[17, 4, 2, 19], [13, 14, 20, 16], [2, 16, 20, 17], [5, 17, 15, 7], [20, 17, 4, 8]]
R = Inst(sets, vals)
mx = [Y for Y in set(R.sd(o) for o in itertools.permutations(range(5))) if None not in Y]
def sig(Y):
    s = [0] * 4
    for i, g in enumerate(Y): s[sorted(sets[i], key=lambda h: -R.v[i][h]).index(g)] += 1
    return tuple(s)
best = max(map(sig, mx)); top = sorted(Y for Y in mx if sig(Y) == best)
ok = True
for Y in top:
    J = [g for g in range(R.m) if g not in Y]; pv = [R.v[i][Y[i]] for i in range(5)]
    F = [j for j in range(5) if any(R.v[i].get(Y[j], 0) > pv[i] for i in range(5) if i != j)]
    U = [j for j in range(5) if j not in F]
    def thr(i):
        vs = [R.v[i].get(g, 0) for g in J]; return sum(vs) - min(vs) > pv[i]
    DT = [x for x in F if any(g in R.R[x] for g in J) and thr(x)]
    res = R.check(Y)
    print('sigma-maximal', Y, 'sigma', best, 'J', J, 'U', U, 'D_T', DT, 'OC1:', res)
    ok = ok and len(U) == 1 and len(DT) == 2 and res == 'one move repairs'
sys.exit(0 if ok and top else 1)
