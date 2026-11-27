"""Owner rules for Conjecture NO computed from the plain neediest-first run (no owner): FIRST (its first agent, the
neediest at the start), LAST (its last agent), FIRST-OR-LAST (one of the two works).

    python3 k4/sdc/no_first.py screen|suite|SRC N SEED   (SRC as in sdc_no.py)"""
import sys, os, json, random, gzip, collections
import _paths
from sdclib import Enc
from sdc_orders import completable
from sdc_need import instances, rule_order
from sdc_need_owner import order_with_last


def rules(sets, vals, m):
    E = Enc(sets, vals, m)
    Y0, ord0 = rule_order(E, 'need2', False)
    first, last = ord0[0], ord0[-1]
    f = completable(E, order_with_last(E, 'need2', False, first)[0])
    l = completable(E, Y0)          # the plain run is NO(last)
    return f, l


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); fails = []
    print('$ python3 k4/sdc/no_first.py', *sys.argv[1:])
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
            else:
                os.chdir(_paths.DE4); sets, vals = sdc_rand.gen(src, rng); os.chdir(cwd)
            items.append(('r%d' % t, sets, vals, 1 + max(max(s) for s in sets)))
    for name, sets, vals, m in items:
        f, l = rules(sets, vals, m)
        C['instances'] += 1; C['FIRST works'] += f; C['LAST works'] += l; C['FIRST or LAST works'] += (f or l)
        if not (f or l):
            fails.append(name)
            if len(fails) <= 3: print('FIRST-OR-LAST FAILS', name, json.dumps((sets, vals)), flush=True)
    print(dict(C))
