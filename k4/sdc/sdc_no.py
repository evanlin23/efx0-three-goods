"""Conjecture NO (k4/sdc.md §9): for some agent o, the serial dictatorship "neediest first, o last" has picks that extend
to an EFX0 allocation.  Neediest: at each step, among the unprocessed agents other than o, the agent maximizing
need2 = v(y) - v(y2) - v(y3), where y > y2 > y3 > ... are its remaining goods (missing ones count 0); ties by index.

    python3 k4/sdc/sdc_no.py SRC N SEED      SRC: as k4/sdc/sdc_rand.py (rand, hyper, advt*, bigN, k3_N), or
                                             cores:FILE1,FILE2 (k4 core certificate files, random strict profiles),
                                             or gen:n:m:k (general additive)"""
import sys, os, json, random, gzip, collections, time
import _paths
from sdclib import Enc
from sdc_orders import completable
from sdc_need_owner import order_with_last


def no_holds(sets, vals, m):
    E = Enc(sets, vals, m)
    for o in range(E.n):
        if completable(E, order_with_last(E, 'need2', False, o)[0]):
            return True, o
    return False, None


if __name__ == '__main__':
    src, N, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/sdc_no.py', *sys.argv[1:]); t0 = time.time()
    cwd = os.getcwd(); os.chdir(_paths.DE4)
    import sdc_rand
    from de4lib import random_profile
    os.chdir(cwd)
    cores = None
    if src.startswith('cores:'):
        cores = []
        for f in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', f)))['cores']]
    for t in range(N):
        if cores is not None:
            sets = rng.choice(cores); vals = random_profile(sets, rng)
        elif src.startswith('gen:'):
            _, n, m, k = src.split(':'); n, m, k = int(n), int(m), int(k)
            while True:
                sets = [sorted(rng.sample(range(m), rng.randint(max(1, k - 1), k))) for _ in range(n)]
                if len(set().union(*map(set, sets))) == m: break
            vals = [rng.sample(range(1, 60), len(s)) for s in sets]
        else:
            os.chdir(_paths.DE4); sets, vals = sdc_rand.gen(src, rng); os.chdir(cwd)
        m = 1 + max(max(s) for s in sets)
        ok, o = no_holds(sets, vals, m)
        C['instances'] += 1; C['NO holds'] += ok
        if not ok:
            print('NO-FAIL', json.dumps((sets, vals)), flush=True)
    print(src, dict(C), 'time %.0f' % (time.time() - t0), flush=True)
