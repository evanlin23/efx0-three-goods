"""k = 4: for an R1-priority run whose SD outcome does not extend, how far back must the order change?  For each bad run
(screen set, random runs), find the smallest d such that some R1 order agreeing with the run on its first d blocks
... more precisely: keep the prefix of the run before block number (last - d) and let every later choice (insertion
agents and R1 tie order) be free; report the least d for which some free continuation extends (exhaustive over the
continuations, n <= 6).

    python3 k4/sdc/k4_blocks.py RUNS SEED              (screen set)
    python3 k4/sdc/k4_blocks.py random n N SEED        (random k = 4 core-like instances, runs with >= 2 blocks)"""
import sys, os, random, collections, json
import _paths
from sdclib import Enc
from sdc_orders import completable
from k4_leader import run, blocks, instances


def continuations(E, prefix):
    """All distinct SD outcomes of R1 orders extending prefix."""
    out = set()
    def rec(done, left, Y):
        if len(done) == E.n:
            out.add(tuple(Y)); return
        rest = [i for i in range(E.n) if i not in done]
        lost = [i for i in rest if any(g not in left for g in E.R[i])]
        for i in (lost if lost else rest):
            av = [g for g in E.R[i] if g in left]
            g = max(av, key=lambda h: (E.v[i][h], -h)) if av else None
            Y2 = list(Y); Y2[i] = g
            rec(done | {i}, left - {g} if g is not None else left, Y2)
    left = set(range(E.m)); Y = [None] * E.n
    for i in prefix:
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
    rec(frozenset(prefix), left, Y)
    return out


def main_screen():
    R, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/k4_blocks.py', *sys.argv[1:])
    for name, sets, vals, m in instances('screen'):
        if len(sets) > 6: continue
        E = Enc(sets, vals, m); cache = {}
        def ext(Y):
            if Y not in cache: cache[Y] = completable(E, list(Y))
            return cache[Y]
        for t in range(R):
            Y, order = run(E, [], rng.randrange(E.n), rng)
            if ext(tuple(Y)): continue
            C['bad runs'] += 1
            st = blocks(E, order); nb = len(st)
            for d in range(nb):
                cut = st[nb - 1 - d]
                if any(ext(Y2) for Y2 in continuations(E, order[:cut])):
                    C['blocks to reopen: %d of %d' % (d + 1, nb)] += 1; break
            else:
                C['no R1 order works at all'] += 1
    for k in sorted(C, key=str): print(k, C[k])


def random_core4(rng, n):
    from de4lib import random_profile
    while True:
        m = rng.randint(n + 3, 2 * n + 2)
        sets = [sorted(rng.sample(range(m), rng.choice([3, 4, 4]))) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m: break
    return sets, random_profile(sets, rng), m


def main_random(n, N, seed, cap=3):
    rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/k4_blocks.py random', n, N, seed)
    while C['bad runs'] < N:
        sets, vals, m = random_core4(rng, n)
        E = Enc(sets, vals, m); cache = {}
        def ext(Y):
            if Y not in cache: cache[Y] = completable(E, list(Y))
            return cache[Y]
        Y, order = run(E, [], rng.randrange(E.n), rng)
        if ext(tuple(Y)): continue
        st = blocks(E, order); nb = len(st)
        if nb < 2: continue
        C['bad runs'] += 1
        for d in range(min(nb, cap)):
            if any(ext(Y2) for Y2 in continuations(E, order[:st[nb - 1 - d]])):
                C['blocks to reopen: %d (of %d)' % (d + 1, nb)] += 1; break
        else:
            C['more than %d blocks, or none' % cap] += 1
            if C['shown'] < 2: C['shown'] += 1; print('DEEP', json.dumps((sets, vals, order)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])


if __name__ == '__main__':
    if sys.argv[1] == 'random':
        main_random(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    else:
        main_screen()
