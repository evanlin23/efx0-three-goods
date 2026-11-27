"""SD outcomes with exactly one frozen agent x (judged on picks): how often do they fail to extend, and what does a
failing one look like (x's type, how many of x's lower goods are unpicked, number of unwanted agents)?

    python3 k4/sdc/sdc_f1.py screen"""
import sys, os, json, itertools, collections
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdf import frozen

if __name__ == '__main__':
    C = collections.Counter()
    print('$ python3 k4/sdc/sdc_f1.py', *sys.argv[1:])
    cwd = os.getcwd(); os.chdir(_paths.DE4)
    from ss_screen import screen_set
    S = screen_set(); os.chdir(cwd)
    for name, I in S:
        if I.n > 6: continue
        E = Enc(I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m)
        outs = set(tuple(sd(E, o)[0]) for o in itertools.permutations(range(E.n)))
        for Y in outs:
            F = frozen(E, list(Y))
            if len(F) != 1: continue
            x = next(iter(F)); picked = set(g for g in Y if g is not None)
            R = sorted(E.R[x], key=lambda g: (-E.v[x][g], g))
            low = [g for g in R if E.v[x][g] < E.v[x][Y[x]] or (E.v[x][g] == E.v[x][Y[x]] and g != Y[x] and R.index(g) > R.index(Y[x]))]
            junk_low = [g for g in low if g not in picked]
            ok = completable(E, list(Y))
            key = 'x has %d goods, pick rank %d, %d unpicked lower goods' % (len(R), R.index(Y[x]), len(junk_low))
            C[(key, ok)] += 1; C['f = 1 outcomes'] += 1; C['f = 1 outcomes that extend'] += ok
            if not ok and C['shown'] < 3:
                C['shown'] += 1; print('F1 FAIL', name, 'x', x, 'Y', Y, json.dumps((I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)])))
    for k in sorted(C, key=str): print(k, C[k])
