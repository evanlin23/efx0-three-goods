"""SD-F: is there an order pi such that in SD(pi) no frozen agent (an agent whose pick some other agent prefers to its
own pick) values an unpicked good?  By Theorem DT+ (k4/sdc.md §6) such an SD outcome extends.  Also: the weaker
SD-F': every frozen agent's unpicked goods are worth at most its pick in total (it can never be threatened).

    python3 k4/sdc/sdf.py screen|suite [r1]"""
import sys, os, json, glob, itertools, collections
import _paths
from sdclib import Enc
from sdc_orders import sd, completable


def frozen(E, Y):
    F = set()
    for j in range(E.n):
        vy = E.v[j][Y[j]] if Y[j] is not None else 0
        for x in range(E.n):
            if x != j and Y[x] is not None and E.v[j].get(Y[x], 0) > vy:
                F.add(x)
    return F


def check(E, r1):
    outs = {}
    for order in itertools.permutations(range(E.n)):
        Y = tuple(sd(E, order, r1)[0]); outs.setdefault(Y, order)
    sdf = sdf2 = False
    for Y in outs:
        picked = set(g for g in Y if g is not None)
        F = frozen(E, list(Y))
        junk_of = {x: [g for g in E.R[x] if g not in picked] for x in F}
        if all(not junk_of[x] for x in F): sdf = True
        if all(sum(E.v[x][g] for g in junk_of[x]) <= E.v[x][Y[x]] for x in F): sdf2 = True
    return sdf, sdf2, len(outs)


if __name__ == '__main__':
    src = sys.argv[1]; r1 = len(sys.argv) > 2 and sys.argv[2] == 'r1'; C = collections.Counter()
    print('$ python3 k4/sdc/sdf.py', *sys.argv[1:])
    insts = []
    if src == 'screen':
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from ss_screen import screen_set
        for name, I in screen_set():
            insts.append((name, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m))
        os.chdir(cwd)
    for name, sets, vals, m in insts:
        if len(sets) > 7: continue
        E = Enc(sets, vals, m)
        a, b, k = check(E, r1)
        C['instances'] += 1; C['SD-F holds'] += a; C["SD-F' holds"] += b
        if not b and C['shown'] < 4: C['shown'] += 1; print('NO SD-F\'', name, json.dumps((sets, vals)))
    print(dict(C))
