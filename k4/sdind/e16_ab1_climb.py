"""E16: adversarial climb against Conjecture AB1 (k4/sd_induct.md §3).

AB1: for every SD outcome Y and every unfrozen agent o that absorbs some one-absorber completion of Y (or none is
needed), some order producing Y with o last gives a reverse-SD insertion path with at most one junk move per step.

Objective (minimized): over all (Y, o) to which AB1 applies, the least number of orders with pi_n = o that work,
as a fraction of the orders with pi_n = o; 0 is a counterexample.  Mutation: re-draw one agent's strict type
(de4lib.random_profile on that agent), or re-draw its goods' ranking; accept if the objective does not increase.
k = 4 cores of n agents from results/k4_certs_*.json.gz.

Refined AB1 (default; AB1_REFINED=0 for the original): o ranges over the agents that hold >= 2 junk goods in some
completion; if no completion has an absorber, the objective is the best fraction over all unfrozen last agents.

    python3 k4/sdind/e16_ab1_climb.py FILES ROUNDS STEPS SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import multiprocessing as mp
import _paths
REFINED = os.environ.get('AB1_REFINED', '1') == '1'
from sdilib import Inst, sd, wanted_by
from e2_paths import sub_completions, bottleneck
from e3_suffix import absorber


def score(sets, vals, m):
    I = Inst(sets, vals, m)
    byY = collections.defaultdict(list)
    for o in itertools.permutations(range(I.n)):
        byY[tuple(sd(I, o)[0])].append(o)
    best = (2.0, None)
    for Y, orders in byY.items():
        Y = list(Y); cache = {}
        full = sub_completions(I, Y, range(I.n), cache)
        if len(full) == 0: continue
        absb = set(absorber(x, I.n) for x in full)
        bylast = collections.defaultdict(list)
        for pi in orders: bylast[pi[-1]].append(pi)
        def frac(o):
            ok = 0
            for pi in bylast[o]:
                seq = list(pi)[::-1]
                d = bottleneck([sub_completions(I, Y, seq[:k], cache) for k in range(1, I.n + 1)])
                ok += (d is not None and d <= 1)
            return ok / len(bylast[o])
        if REFINED and absb == {None}:
            fr = max(frac(o) for o in bylast)          # refined AB1: SOME unfrozen last agent works
            if fr < best[0]: best = (fr, (Y, 'some o'))
            continue
        for o in bylast:
            if not (o in absb or (None in absb and not REFINED)): continue
            fr = frac(o)
            if fr < best[0]: best = (fr, (Y, o))
    return best


def run(args):
    files, steps, seed = args
    rng = random.Random(seed); cwd = os.getcwd(); os.chdir(_paths.DE4)
    from de4lib import random_profile
    os.chdir(cwd)
    cores = []
    for fn in files.split(','):
        cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
    sets = rng.choice(cores); m = 1 + max(max(x) for x in sets)
    vals = random_profile(sets, rng)
    cur = score(sets, vals, m)
    for st in range(steps):
        v2 = [list(x) for x in vals]
        i = rng.randrange(len(sets))
        v2[i] = random_profile([sets[i]], rng)[0]
        sc = score(sets, v2, m)
        if sc[0] <= cur[0]:
            vals, cur = v2, sc
        if cur[0] == 0: break
    return seed, sets, vals, m, cur


if __name__ == '__main__':
    files, R, S, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/sdind/e16_ab1_climb.py', *sys.argv[1:], '(AB1_REFINED=%d)' % REFINED, flush=True)
    t0 = time.time(); C = collections.Counter()
    with mp.Pool(os.cpu_count()) as pool:
        for sd_, sets, vals, m, cur in pool.imap_unordered(run, [(files, S, seed * 1000 + r) for r in range(R)]):
            C['rounds'] += 1; C['final fraction %.2f' % cur[0] if cur[0] <= 1 else 'final: no (Y, o) to test'] += 1
            print('round', sd_, 'final fraction', round(cur[0], 3), 'at', cur[1], json.dumps((sets, vals)), flush=True)
            if cur[0] == 0: print('AB1 COUNTEREXAMPLE', json.dumps((sets, vals)), cur[1], flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
