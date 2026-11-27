"""Adversarial climb against HS-MAX and RKMAX (k4/rkmax.md §7).

Seeds: residue starts (Pareto-optimal maximum matchings that are hard and covered by none of Prop. T0, Lemma S',
Lemma RF-B) of the n = 4 export profiles (or random MC2-class cores, RAND=n).  Fix the hypergraph and the matching Y.
A move changes one value of one agent (new random integer in [1, 40]), kept only if the values stay strict and
balanced (as in oc1_mc2_rand.gen) and Y stays a residue start.  Objective (minimized): the number of maximum matchings
whose signature beats sigma(Y), then the lexicographic gap.  Objective 0 means Y is sigma-maximal and a residue start:
a counterexample to HS-MAX; it is then checked for OC1 (a failure there refutes RKMAX).
    python3 rk_climb.py SEEDS STEPS SEED          # seeds from the n = 4 export
    RAND=5 python3 rk_climb.py SEEDS STEPS SEED   # seeds from random n = 5 cores
    MECH=sink1 ...                                # residue = hard and no Lemma SINK1 case (default: no S', no RF-B)
    SEEDFILE=EXPORT ...                           # seeds from the profiles of another failure export (e.g. n = 5)
    SEEDOK=1 ...                                  # only seeds at which OC1 holds (a failing seed cannot reach 0 at n = 4)
    POT=rs ...                                    # climb towards rank-sum optimality instead of sigma-maximality"""
import sys, os, gzip, json, random, itertools, collections, time, multiprocessing as mp
from rklib import Prof
from rk_classes import theta, sprime_cases, rfb_cases, sink1_cases
MECH = os.environ.get('MECH', 'sprime')
POT = os.environ.get('POT', 'sigma')

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def strict_balanced(x):
    if 2 * max(x) >= sum(x): return False
    sums = collections.defaultdict(list)
    for r in range(1, len(x) + 1):
        for T in itertools.combinations(range(len(x)), r): sums[sum(x[k] for k in T)].append(set(T))
    return all(not (a & b) for L in sums.values() for a, b in itertools.combinations(L, 2))


def residue(sets, vals, Y):
    P = Prof(sets, vals); nu, mm = P.max_matchings()
    if sum(g is not None for g in Y) != nu or any(g is None for g in Y) or not P.pareto_optimal(Y): return None
    ro = P.roles(Y)
    if any(not theta(P, Y, ro, z) for z in ro['U']): return None
    if P.one_absorber([frozenset([g]) for g in Y]) is not None: return None
    if MECH == 'sink1':
        if sink1_cases(P, Y, ro): return None
    elif sprime_cases(P, Y, ro) or rfb_cases(P, Y, ro): return None
    if POT == 'rs':                                   # rank-sum form: matchings with a smaller rank sum
        rs = sum(P.ranks(Y)); better = [rs - sum(P.ranks(M)) for M in mm if sum(P.ranks(M)) < rs]
        return (len(better), (max(better) if better else 0,)), P
    sY = P.sigma(Y); better = [P.sigma(M) for M in mm if P.sigma(M) > sY]
    gap = tuple(a - b for a, b in zip(max(better), sY)) if better else (0, 0, 0, 0)
    return (len(better), gap), P


def climb(args):
    sets, vals, Y, steps, seed = args
    rng = random.Random(seed); vals = [list(x) for x in vals]
    cur = residue(sets, vals, Y)
    if cur is None: return None
    best = cur[0]
    for _ in range(steps):
        i = rng.randrange(len(sets)); g = rng.randrange(len(sets[i]))
        nv = [list(x) for x in vals]; nv[i][g] = rng.randint(1, 40)
        if not strict_balanced(nv[i]): continue
        r = residue(sets, nv, Y)
        if r is None: continue
        if r[0] <= cur[0] or rng.random() < 0.05:
            vals, cur = nv, r
            if r[0] < best: best = r[0]
            if r[0][0] == 0:
                oc = r[1].oc1(Y)
                return {'sets': sets, 'vals': vals, 'picks': Y, 'OC1': oc, 'found': True}
    return {'best': best, 'found': False}


def seeds_n4(N, rng, F=None):
    d = json.load(gzip.open(F or os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    prof = [(h['sets'], st['vals']) for h in d['hypergraphs'] for st in h['starts']]
    rng.shuffle(prof); out = []
    only_ok = os.environ.get('SEEDOK', '0') == '1'     # keep only residue starts at which OC1 holds (U0-type seeds)
    for sets, vals in prof:
        P = Prof(sets, vals); nu, mm = P.max_matchings()
        for Y in mm:
            if residue(sets, vals, Y) is not None and (not only_ok or P.oc1(Y) != 'F'):
                out.append((sets, vals, Y)); break
        if len(out) >= N: break
    return out


def seeds_rand(N, n, rng):
    sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc')); from oc1_mc2_rand import gen
    out = []
    while len(out) < N:
        try: sets, vals = gen(n, rng)
        except ValueError: continue
        P = Prof(sets, vals); nu, mm = P.max_matchings()
        for Y in mm:
            if residue(sets, vals, Y) is not None: out.append((sets, vals, Y)); break
    return out


if __name__ == '__main__':
    N, STEPS, SEED = map(int, sys.argv[1:4]); rng = random.Random(SEED)
    RAND = int(os.environ.get('RAND', '0'))
    print('$ POT=%s MECH=%s RAND=%d SEEDFILE=%s python3 k4/rkmax/rk_climb.py' % (POT, MECH, RAND, os.path.basename(os.environ.get('SEEDFILE', '-'))), *sys.argv[1:], flush=True)
    t0 = time.time()
    SEEDFILE = os.environ.get('SEEDFILE')
    S = seeds_rand(N, RAND, rng) if RAND else seeds_n4(N, rng, SEEDFILE)
    print('seeds', len(S), '%.0f s' % (time.time() - t0), flush=True)
    T = collections.Counter()
    with mp.Pool() as pool:
        for res in pool.imap_unordered(climb, [(a, b, c, STEPS, SEED * 7919 + t) for t, (a, b, c) in enumerate(S)]):
            if res is None: T['seed lost'] += 1; continue
            if res['found']:
                T['HS-MAX COUNTEREXAMPLE (OC1 %s)' % res['OC1']] += 1
                print('FOUND', json.dumps(res), flush=True)
            else:
                T['best (#better, gap) %s' % (res['best'],)] += 1
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
