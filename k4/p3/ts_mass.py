"""Conjecture TS2 at scale (k4/p3.md section 4): random (4, 3) cores (k4/p3_run.random_core43) with random strict
balanced types, and the certified (4, 3) core lists with random types; for each instance the least number of rotations
(up to --R) after which the Phase 1 state, under some upgrade policy, has an EFX0 extension of its bases with at most B
bundles of three or more goods (k4/p3/ts.py). Parallel over instances. EVIDENCE only.
    python3 k4/p3/ts_mass.py --n=6,7,8 --count=200 [--cores=1 --per=5] [--R=2] [--B=2] [--jobs=2] [--seed=1]
"""
import sys, os, random, json, time, collections
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *
import ts

def work(task):
    sets, vals, m, R, Bs, name = task
    I = Inst(sets, vals, m, name)
    r = ts.run(I, R, Bs, None)
    return name, I.n, I.m, r, (None if all(x is not None for x in r.values()) else I.as_json())

if __name__ == '__main__':
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1))); R = int(opt.get('R', 2))
    Bs = [int(x) for x in opt.get('B', '2').split(',')]
    print('$ python3 k4/p3/ts_mass.py ' + ' '.join(sys.argv[1:]), flush=True)
    tasks = []
    for n in [int(x) for x in opt.get('n', '').split(',') if x]:
        for c in range(int(opt.get('count', 100))):
            rc = random_core43(rng, n)
            if rc: tasks.append((rc[1], random_types(rng, rc[1], rc[0]), rc[0], R, Bs, f'rand-n{n}-{c}'))
    if opt.get('cores'):
        for f in core_lists_p3():
            for m, sets in cores_from(f):
                for k in range(int(opt.get('per', 3))):
                    tasks.append((sets, random_types(rng, sets, m), m, R, Bs, os.path.basename(f)))
    cnt = collections.Counter(); t0 = time.time(); bad = []
    with Pool(int(opt.get('jobs', 2))) as P:
        for name, n, m, r, inst in P.imap_unordered(work, tasks, chunksize=4):
            for B, x in r.items():
                cnt[(n if not name.startswith('k4_') else name.split('_p3')[0], B, 'fail' if x is None else x)] += 1
            if inst: bad.append(inst); print('FAIL', json.dumps(inst), flush=True)
    for k in sorted(cnt, key=str): print(f'  {k}: {cnt[k]}')
    print(f'{len(tasks)} instances, {len(bad)} failures, {time.time()-t0:.0f}s')
