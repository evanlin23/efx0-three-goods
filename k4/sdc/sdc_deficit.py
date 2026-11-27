"""A counting test for SD-C at k = 4.  For an SD outcome Y: frozen agents F (pick wanted by someone, judged on picks);
cost(x) = least number of x's unpicked goods to remove so that the rest is worth at most its pick; slots = unwanted
agents with a pick (one good each) plus twice the unwanted agents without one, minus one (the owner).
deficit(Y) = sum of costs - slots.  Questions: does deficit <= 0 imply that Y extends?  Do all SD outcomes of least
deficit extend?

    python3 k4/sdc/sdc_deficit.py screen [r1]"""
import sys, os, json, itertools, collections
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdf import frozen


def deficit(E, Y):
    picked = set(g for g in Y if g is not None)
    F = frozen(E, Y)
    cost = 0
    for x in F:
        U = sorted((E.v[x][g] for g in E.R[x] if g not in picked), reverse=True)
        c = 0
        while sum(U[c:]) > E.v[x][Y[x]]:
            c += 1
        cost += c
    slots = sum(1 if Y[i] is not None else 2 for i in range(E.n) if i not in F) - 1
    return cost - slots


if __name__ == '__main__':
    r1 = len(sys.argv) > 2 and sys.argv[2] == 'r1'; C = collections.Counter()
    print('$ python3 k4/sdc/sdc_deficit.py', *sys.argv[1:])
    cwd = os.getcwd(); os.chdir(_paths.DE4)
    from ss_screen import screen_set
    S = screen_set(); os.chdir(cwd)
    for name, I in S:
        if I.n > 7: continue
        E = Enc(I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m)
        outs = set(tuple(sd(E, o, r1)[0]) for o in itertools.permutations(range(E.n)))
        D = {Y: deficit(E, list(Y)) for Y in outs}; X = {Y: completable(E, list(Y)) for Y in outs}
        C['instances'] += 1
        for Y in outs:
            C['outcomes'] += 1
            C['deficit<=0'] += D[Y] <= 0
            C['deficit<=0 but does not extend'] += (D[Y] <= 0 and not X[Y])
            C['deficit>0 but extends'] += (D[Y] > 0 and X[Y])
        mn = min(D.values())
        C['all least-deficit outcomes extend'] += all(X[Y] for Y in outs if D[Y] == mn)
        C['some least-deficit outcome extends'] += any(X[Y] for Y in outs if D[Y] == mn)
        C['least deficit <= 0'] += mn <= 0
    for k in sorted(C, key=str): print(k, C[k])
