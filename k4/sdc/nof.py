"""Conjecture NOF (fixed-order NO): pi = the plain neediest-first order; for some agent o, SD(pi with o moved to the end)
extends to an EFX0 allocation.  By Lemma DC the candidates differ from SD(pi) along single displacement chains.

    python3 k4/sdc/nof.py screen|suite|SRC N SEED [--r1]   (SRC as in sdc_no.py: cores:FILES, rand, hyper, advt*, bigN,
                                                             gen:n:m:k; --r1: neediest first with R1 priority)"""
import sys, os, json, random, gzip, collections, time
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_need import instances, rule_order


def nof(sets, vals, m, r1=False):
    E = Enc(sets, vals, m)
    Y0, pi = rule_order(E, 'need2', r1)
    if completable(E, Y0): return True, pi[-1], 'plain'
    for o in pi:
        if completable(E, sd(E, [i for i in pi if i != o] + [o])[0]): return True, o, 'deferred'
    return False, None, None


if __name__ == '__main__':
    R1 = '--r1' in sys.argv; sys.argv = [a for a in sys.argv if a != '--r1']
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/nof.py', *sys.argv[1:])
    if src in ('screen', 'suite'):
        items = instances(src)
    else:
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        import sdc_rand
        from de4lib import random_profile
        os.chdir(cwd)
        cores = None
        if src.startswith('cores:'):
            cores = []
            for fn in src[6:].split(','):
                cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
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
            items.append(('r%d' % t, sets, vals, 1 + max(max(s) for s in sets)))
    for name, sets, vals, m in items:
        ok, o, how = nof(sets, vals, m, R1)
        C['instances'] += 1; C['NOF holds'] += ok; C[how] += 1
        if not ok:
            C['shown'] += 1
            if C['shown'] <= 3: print('NOF-FAIL', name, json.dumps((sets, vals)), flush=True)
    print(src, dict(C), 'time %.0f' % (time.time() - t0))
