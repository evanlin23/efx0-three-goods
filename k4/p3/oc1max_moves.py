"""Which improving move repairs the maximum-matching pick vectors that need one (OC1^max, k4/p3.md section 6)? On the
n = 5 core hypergraphs with p <= P (results/k4_certs_5_*.json.gz), R uniform strict order types each (k4/check4), every
order: for every maximum pick vector with no one-absorber completion at the picks, the simplest repairing move
(addition < chain < ring, then by length) by the independent checker k4/p3/oc1max.py. Prints the histogram and one
example of each kind.
    python3 k4/p3/oc1max_moves.py R SEED [--p=2] [--stride=1]
"""
import sys, os, gzip, json, random, itertools, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import Inst, sd, random_types, ROOT
from oc1max import Checker, nu

if __name__ == '__main__':
    R, SEED = int(sys.argv[1]), int(sys.argv[2])
    opt = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--'))
    P, stride = int(opt.get('p', 2)), int(opt.get('stride', 1))
    print('$ python3 k4/p3/oc1max_moves.py ' + ' '.join(sys.argv[1:]), flush=True)
    rng = random.Random(SEED); H = collections.Counter(); ex = {}; t0 = time.time(); nh = 0
    for lst in ('n4_1', 'n4_2', 'n4_3', 'n4_4', 'pure'):
        d = json.load(gzip.open(os.path.join(ROOT, 'results', f'k4_certs_5_{lst}.json.gz'), 'rt'))
        cs = [c for c in d['cores'] if max(sum(g in S for S in c['sets']) for g in range(c['m'])) <= P][::stride]
        for c in cs:
            nh += 1
            for _ in range(R):
                vals = random_types(rng, c['sets'], c['m']); I = Inst(c['sets'], vals, c['m']); K = Checker(I); N = nu(I)
                for pk in set(tuple(sd(I, o)) for o in itertools.permutations(range(I.n))):
                    if sum(x is not None for x in pk) != N: continue
                    base = tuple(frozenset([q]) if q is not None else frozenset() for q in pk)
                    if K.complete(base) is not None: H['picks complete'] += 1; continue
                    tag = K.simplest_repair(pk)
                    key = 'FAILS' if tag is None else f'{tag[2]} (length {tag[1]})'
                    H[key] += 1
                    ex.setdefault(key, {'sets': c['sets'], 'vals': vals, 'picks': pk})
                K.close()
    print(f'{nh} hypergraphs, {R} profiles each, {time.time()-t0:.0f}s')
    for k, v in sorted(H.items()): print(f'  {k}: {v}')
    for k, e in ex.items():
        if k != 'picks complete': print(f'  example, {k}:', json.dumps(e))
