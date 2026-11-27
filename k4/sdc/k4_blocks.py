"""k = 4: for an R1-priority run whose SD outcome does not extend, how far back must the order change?  For each bad run
(screen set, random runs), find the smallest d such that some R1 order agreeing with the run on its first d blocks
... more precisely: keep the prefix of the run before block number (last - d) and let every later choice (insertion
agents and R1 tie order) be free; report the least d for which some free continuation extends (exhaustive over the
continuations, n <= 6).

    python3 k4/sdc/k4_blocks.py RUNS SEED              (screen set)
    python3 k4/sdc/k4_blocks.py random n N SEED        (random k = 4 core-like instances, runs with >= 2 blocks)
    python3 k4/sdc/k4_blocks.py adv SRC N SEED         (SRC: advt0..3, advt3x, advt4x, hyper)"""
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


def gen_adv(rng, src):
    import adv_t, adv_t3, adv_t4
    from de4lib import random_profile
    if src == 'hyper':
        cores = json.load(open(os.path.join(_paths.ROOT, 'results/k4_de4/stuck_hypergraphs.json')))['hypergraphs']
        sets = rng.choice(cores); return sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)
    I = None
    while I is None:
        I = adv_t3.make(rng) if src == 'advt3x' else adv_t4.make(rng) if src == 'advt4x' else adv_t.make(rng, int(src[4:]))
    return I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m


def main_random(n, N, seed, cap=3, src=None):
    rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/k4_blocks.py random', n if src is None else src, N, seed)
    tries = 0
    while C['bad runs'] < N and tries < 20000:
        tries += 1
        sets, vals, m = random_core4(rng, n) if src is None else gen_adv(rng, src)
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
    elif sys.argv[1] == 'adv':
        main_random(None, int(sys.argv[3]), int(sys.argv[4]), src=sys.argv[2])
    else:
        main_screen()
