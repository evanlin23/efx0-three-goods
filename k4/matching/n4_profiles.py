"""CM, CM2 and the exactness of Lemma EX* on random strict profiles of the 11 n = 4 hypergraphs where OC1^max fails
(k4/matching.md §5; evidence only: sampled profiles, every order).

For each hypergraph of results/k4_matching/data/oc1max_cex_n4.json: R random strict balanced profiles (de4lib.random_profile,
as in k4/sdc/min_frozen.load 'cores:'); every order; every distinct perfect start with no one-absorber completion
(raw).  Recorded per start: CM (one Lemma EX* exchange at the picks), OC1 (raw, every official move); where OC1
fails: CM2 (some first move, then an EX* exchange) and OC2 (raw, every pair of moves), and whether the first moves
admitting an EX* exchange are exactly those after which some second move repairs.

    python3 k4/matching/n4_profiles.py R SEED"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from exchange import ex_star_witness


def job(args):
    t, sets, R, seed = args
    cwd = os.getcwd(); os.chdir(os.path.join(_mpaths.ROOT, 'k4', 'de4'))
    from de4lib import random_profile
    os.chdir(cwd)
    rng = random.Random(seed); C = collections.Counter(); bad = []
    for r in range(R):
        vals = random_profile(sets, rng); I = M(sets, vals)
        for Y in sorted(set(I.sd(o) for o in itertools.permutations(range(I.n))), key=str):
            if any(y is None for y in Y): continue
            base = [[g] for g in Y]
            if I.complete(base, 0, 'oa') is not None: continue
            C['hard perfect starts'] += 1
            first = I.moves(base)
            cm = ex_star_witness(I, base) is not None
            oc1 = any(I.complete(B1, 0, 'oa') is not None for B1 in first)
            C['CM %s, OC1 %s' % (cm, oc1)] += 1
            if cm != oc1: bad.append(('CM != OC1', vals, Y, cm, oc1))
            if oc1: continue
            ex1 = [ex_star_witness(I, B1) is not None for B1 in first]
            oc2 = [e or any(I.complete(B2, 0, 'oa') is not None for B2 in I.moves(B1)) for e, B1 in zip(ex1, first)]
            C['OC1 fails: CM2 %s, OC2 %s' % (any(ex1), any(oc2))] += 1
            C['OC1 fails: EX* exact on the second move %s' % (ex1 == oc2)] += 1
            if not any(ex1) or ex1 != oc2: bad.append(('second move', vals, Y, sum(ex1), sum(oc2)))
    return t, sets, C, bad


if __name__ == '__main__':
    R, SEED = map(int, sys.argv[1:3])
    D = json.load(open(os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'oc1max_cex_n4.json')))['instances']
    print('$ python3 k4/matching/n4_profiles.py', *sys.argv[1:], flush=True)
    tasks = [(t, d['sets'], R, SEED * 1009 + t) for t, d in enumerate(D)]
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for t, sets, C, bad in pool.imap_unordered(job, tasks):
            T.update(C)
            print('hypergraph %d %s:' % (t, json.dumps(sets)), dict(C), flush=True)
            for b in bad: print('   ', b[0], json.dumps({'sets': sets, 'vals': b[1], 'picks': b[2]}), b[3:], flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
