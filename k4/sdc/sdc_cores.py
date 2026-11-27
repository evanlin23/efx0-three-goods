"""SD-C-R1 (and SD-C on failure) on random strict balanced profiles of the enumerated connected k = 4 cores."""
import sys, os, json, gzip, random, time, multiprocessing as mp
import _paths
from de4lib import random_profile
from sdsat_r1 import solve_r1
from sdsat import solve
def job(args):
    sets, per, seed = args
    rng = random.Random(seed); m = 1 + max(max(s) for s in sets); out = []; c = 0
    for _ in range(per):
        vals = random_profile(sets, rng)
        c += 1
        if not solve_r1(sets, vals, m):
            ok, _ = solve(sets, vals, m)
            out.append((sets, vals, ok))
    return c, out
if __name__ == '__main__':
    files, per, seed = sys.argv[1].split(','), int(sys.argv[2]), int(sys.argv[3])
    cores = []
    for f in files:
        cores += [c['sets'] for c in json.load(gzip.open(_paths.ROOT + '/results/' + f))['cores']]
    t0 = time.time(); tot = 0; nf = 0
    print('$ sdc_cores', ' '.join(sys.argv[1:]), len(cores), 'cores', flush=True)
    with mp.Pool(3) as p:
        for c, out in p.imap_unordered(job, [(s, per, seed + k) for k, s in enumerate(cores)], chunksize=4):
            tot += c
            for o in out:
                nf += 1; print('R1-FAIL' if o[2] else 'SDC-FAIL', json.dumps(o[:2]), flush=True)
    print('profiles', tot, 'SD-C-R1 failures', nf, 'time %.0f' % (time.time() - t0), flush=True)
