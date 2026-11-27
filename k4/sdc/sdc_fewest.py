"""Fewest frozen agents among SD outcomes: do all (or some) SD outcomes with the fewest frozen agents extend?  Frozen is
judged on picks (an agent whose pick another agent prefers to its own pick).  Plain orders, or R1 orders.

    python3 k4/sdc/sdc_fewest.py screen|suite [r1]"""
import sys, os, json, glob, itertools, random, collections
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdf import frozen

if __name__ == '__main__':
    src = sys.argv[1]; r1 = len(sys.argv) > 2 and sys.argv[2] == 'r1'; C = collections.Counter()
    print('$ python3 k4/sdc/sdc_fewest.py', *sys.argv[1:])
    insts = []
    if src == 'screen':
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from ss_screen import screen_set
        for name, I in screen_set():
            insts.append((name, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m))
        os.chdir(cwd)
    else:
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'k4/suite/instances/*.json'))):
            d = json.load(open(f))
            if d.get('vals') and d.get('sets') and len(d['sets']) <= 7:
                insts.append((d.get('id'), d['sets'], d['vals'], d.get('m') or 1 + max(max(s) for s in d['sets'])))
    for name, sets, vals, m in insts:
        if len(sets) > 7: continue
        E = Enc(sets, vals, m)
        outs = set(tuple(sd(E, o, r1)[0]) for o in itertools.permutations(range(E.n)))
        F = {Y: len(frozen(E, list(Y))) for Y in outs}; mn = min(F.values())
        X = {Y: completable(E, list(Y)) for Y in outs}
        C['instances'] += 1
        C['all fewest-frozen outcomes extend'] += all(X[Y] for Y in outs if F[Y] == mn)
        C['some fewest-frozen outcome extends'] += any(X[Y] for Y in outs if F[Y] == mn)
        C['fewest frozen = %d' % mn] += 1
        if not any(X[Y] for Y in outs if F[Y] == mn) and C['shown'] < 3:
            C['shown'] += 1; print('NO FEWEST-FROZEN OUTCOME EXTENDS', name, json.dumps((sets, vals)))
    for k in sorted(C, key=str): print(k, C[k])
