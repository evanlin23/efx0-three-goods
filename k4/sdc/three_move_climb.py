"""Adversarial climb for a start needing three sequential moves (refuting OC2^max).  State: a seed of
three_move_hunt.seeds() extended by EXTRA agents; mutations change one value (+-1..3) or one relevant good of any agent
(new agents more often); kept only if the result is a strict connected k = 4 core.  Score over the maximum-matching
SD starts: 10000 * (# needing >= 3 moves) + 100 * (# needing 2) + (# needing 1).  Accept if the score does not drop.
Coordinator's own code (three_move_hunt.depth / complete, Inst.moves).
    python3 k4/sdc/three_move_climb.py RUNS STEPS SEED EXTRA"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
import oc1max_climb as C
import three_move_hunt as H


def score(sets, vals):
    I = Inst(sets, vals); N = nu(I); cnt = collections.Counter(); bad = []
    for p in {I.sd(o) for o in itertools.permutations(range(I.n))}:
        if sum(x is not None for x in p) != N: continue
        r = H.depth(I, p); cnt[r] += 1
        if r == '>=3': bad.append(p)
    return 10000 * cnt['>=3'] + 100 * cnt[2] + cnt[1], dict(cnt), bad


def mutate(sets, vals, rng, n0):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    i = rng.randrange(n0, len(sets)) if rng.random() < 0.6 else rng.randrange(len(sets))
    m = 1 + max(max(s) for s in sets)
    if rng.random() < 0.7:
        k = rng.randrange(len(vals[i])); vals[i][k] = max(1, vals[i][k] + rng.choice([-3, -2, -1, 1, 2, 3]))
    else:
        k = rng.randrange(len(sets[i])); g = rng.randrange(m + 1)
        if g in sets[i]: return None
        sets[i][k] = g
        used = sorted(set().union(*map(set, sets))); ren = {g: t for t, g in enumerate(used)}
        sets = [[ren[g] for g in s] for s in sets]
    return sets, vals


def run(args):
    steps, seed, extra = args
    rng = random.Random(seed)
    while True:
        r = H.trial((rng.randrange(10 ** 9), extra))[1]
        if r is not None: break
    sets, vals = r[0], r[1]; n0 = len(sets) - extra
    best, cnt, bad = score(sets, vals); found = []
    for _ in range(steps):
        mu = mutate(sets, vals, rng, n0)
        if mu is None or not C.is_core(*mu, False): continue
        sc, c2, b2 = score(*mu)
        if b2: found.append((mu[0], mu[1], b2))
        if sc >= best: (sets, vals), best, cnt = mu, sc, c2
    return seed, best, cnt, sets, vals, found


if __name__ == '__main__':
    RUNS, STEPS, SEED, EXTRA = map(int, sys.argv[1:5])
    print('$ python3 k4/sdc/three_move_climb.py', *sys.argv[1:], flush=True)
    t0 = time.time(); F = 0
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for seed, best, cnt, sets, vals, found in pool.imap_unordered(run, [(STEPS, SEED * 7919 + t, EXTRA) for t in range(RUNS)]):
            print('run', seed, 'score', best, cnt, json.dumps({'sets': sets, 'vals': vals}), '%.0f s' % (time.time() - t0), flush=True)
            for s2, v2, b in found:
                F += 1; print('THREE-MOVE CANDIDATE', json.dumps({'sets': s2, 'vals': v2, 'picks': b}), flush=True)
    print('three-move candidates:', F, 'time %.0f s' % (time.time() - t0))
