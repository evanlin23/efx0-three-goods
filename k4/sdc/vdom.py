"""Value domination of serial-dictatorship picks (k4/sdc.md §28).  For an order pi with picks Y = SD(pi), ask whether
some EFX0 allocation X (complete) has v_i(X_i) >= v_i(Y_i) for every agent i ('Y is value-dominated'); this is weaker
than 'Y extends' (Y_i in X_i; K4.SDC.NOF, refuted by T3) and implied by it.  Tested for the neediest-first order
(need2, plain and R1) and for every order (n <= 5; 40 sampled orders above).

    python3 k4/sdc/vdom.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc, decode
from sdc_need import instances, rule_order
from sdc_orders import sd, completable
from nof_var import SPECIAL
from pysat.solvers import Cadical153


def dominated(E, Y, want=False):
    cl = list(E.cl)
    for g in range(E.m): cl.append([-E.x[g][E.n]])
    for i in range(E.n):
        if Y[i] is None: continue
        t = E.v[i][Y[i]]
        for S, y in E.y[i].items():
            if E.val(i, S) < t: cl.append([-y])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); X = decode(E, S.get_model()) if (ok and want) else None
    S.delete(); return (ok, X) if want else ok


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/vdom.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        n = len(sets)
        if n > 9: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        for r1 in (False, True):
            Y, pi = rule_order(E, 'need2', r1); key = 'neediest-first' + (' R1' if r1 else ' plain')
            ext = completable(E, Y); dom = ext or dominated(E, Y)
            C[key + ': picks extend'] += ext
            C[key + ': picks value-dominated'] += dom
            if not dom: print('NOT DOMINATED', key, name, json.dumps((sets, vals)), 'Y', Y, flush=True)
        orders = list(itertools.permutations(range(n))) if n <= 5 else \
            [tuple(random.Random(t).sample(range(n), n)) for t in range(40)]
        seen = {}; bad = 0
        for o in orders:
            Y = tuple(sd(E, list(o))[0])
            if Y not in seen: seen[Y] = completable(E, Y) or dominated(E, Y)
            bad += not seen[Y]
        C['orders tried'] += len(orders); C['orders whose picks are not value-dominated'] += bad
        C['instances with some order not value-dominated'] += bad > 0
        if bad and C['shown'] < 3:
            C['shown'] += 1; print('SOME ORDER NOT DOMINATED', name, json.dumps((sets, vals)), bad, 'of', len(orders), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
