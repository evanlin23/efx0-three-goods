"""Coordinator's independent spot-check of OC2^max (k4/sdc.md §31, LEDGER K4.SDC.OC2MAX) on the core lists
results/k4_certs_{n}_*.json.gz, random strict profiles (with (C4)), every order: for each maximum-matching start,
the least number of sequential moves (0, 1, 2) after which a one-absorber completion exists (own code:
oc1_mc2_rand.Inst, oc2max_cex_check.oc2).  Random profiles are EVIDENCE only; the certified n = 4 result is the
ordinal CEGAR's (compute/k4-oc1max-cert).

    python3 k4/sdc/oc2max_lists.py N LIST[,LIST...] R SEED [STRIDE]"""
import sys, os, gzip, json, random, itertools, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
from oc1max_n5_lists import profile
from oc2max_cex_check import oc2

RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results')


def job(args):
    lst, idx, sets, R, seed = args
    rng = random.Random(seed); C = collections.Counter(); bad = []
    for _ in range(R):
        vals, _ = profile(sets, rng); I = Inst(sets, vals); N = nu(I)
        for p, c in collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n))).items():
            if sum(x is not None for x in p) != N: continue
            r = oc2(I, p); C[r] += c
            if r is None: bad.append((vals, p))
    return lst, idx, sets, C, bad


if __name__ == '__main__':
    n = int(sys.argv[1]); lists = sys.argv[2].split(','); R = int(sys.argv[3]); SEED = int(sys.argv[4])
    STRIDE = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    print('$ python3 k4/sdc/oc2max_lists.py', *sys.argv[1:], flush=True)
    tasks = []
    for lst in lists:
        d = json.load(gzip.open(os.path.join(RES, 'k4_certs_%d_%s.json.gz' % (n, lst))))
        for c in d['cores'][::STRIDE]: tasks.append((lst, c['idx'], c['sets'], R, SEED * 1000003 + len(tasks)))
    print('hypergraphs', len(tasks), flush=True)
    t0 = time.time(); T = collections.Counter()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for lst, idx, sets, C, bad in pool.imap_unordered(job, tasks, chunksize=4):
            for k, c in C.items(): T['max orders needing %s moves' % k] += c
            for vals, p in bad:
                print('OC2max FAILS', json.dumps({'list': lst, 'idx': idx, 'sets': sets, 'vals': vals, 'picks': p}), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
