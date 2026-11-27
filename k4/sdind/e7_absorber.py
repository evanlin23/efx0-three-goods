"""E7: the absorber pi_n of the reverse-SD insertion (k4/sd_induct.md §3).  Per start Y and per possible last agent
o (o not frozen): can o be the absorber of a completion of Y (A(N) has an element whose absorber is o, or one with no
absorber)?  does some order with pi_n = o give a path with steps <= 1?  do all such orders, with steps <= 1, <= 2?

    python3 k4/sdind/e7_absorber.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by
from e1_delete import load
from e2_paths import sub_completions, bottleneck
from e3_suffix import absorber

if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e7_absorber.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        byY = collections.defaultdict(list)
        for o in itertools.permutations(range(I.n)):
            byY[tuple(sd(I, o)[0])].append(o)
        for Y, orders in byY.items():
            Y = list(Y); cache = {}
            try:
                full = sub_completions(I, Y, range(I.n), cache)
            except ValueError:
                continue
            if len(full) == 0: continue
            C['starts'] += 1
            absb = set(absorber(x, I.n) for x in full)
            bylast = collections.defaultdict(list)
            for pi in orders:
                seq = list(pi)[::-1]
                bylast[pi[-1]].append(bottleneck([sub_completions(I, Y, seq[:k], cache) for k in range(1, I.n + 1)]))
            for o, ds in bylast.items():
                can = (o in absb) or (None in absb)
                some1 = any(d is not None and d <= 1 for d in ds)
                all1 = all(d is not None and d <= 1 for d in ds)
                all2 = all(d is not None and d <= 2 for d in ds)
                C['(last o) cases'] += 1
                C['(last o) o absorbs some completion (or none needed): %s; some order <= 1: %s' % (can, some1)] += 1
                if can: C['(last o) can: every order <= 1'] += all1; C['(last o) can: every order <= 2'] += all2
                if can and not some1 and shown['x'] < 3:
                    shown['x'] += 1; print('ABSORBER BUT NO PATH', name, json.dumps((sets, vals)), 'picks', Y, 'o', o, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
