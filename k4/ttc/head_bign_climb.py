"""Adversarial climb for OC1-HD (k4/ttc.md §10) at n = 6..8, adapted from k4/sdc/oc1_bign_climb.py (same generator,
mutations and score shape).  The repairing count of a hard start (picks without a one-absorber completion) is the
number of improving chains of OC1-HD's shape (x_0 dangerous at the start; x_1..x_{t-1} take exactly their
predecessor's pick; the head x_t may add junk; t >= 1) whose result has a one-absorber completion with absorber x_t,
capped at CAPC.  The climb maximises (hard starts * CAPC - least count) * 1000 + (frozen agents whose junk is worth
more than their pick, the soft signal of oc1_bign_climb.py) and prints any start with count 0 (an OC1-HD
counterexample; then plain OC1 is checked too).

    python3 k4/ttc/head_bign_climb.py N_RUNS ROUNDS ORDERS SEED NMIN NMAX [ends]
ends: Conjecture OC1-ED: the same chains, but the absorber may be either endpoint (x_0 or x_t).  (The worker processes
are forked, so the module-level flag set in __main__ reaches them.)"""
import sys, os, json, random, collections, time, multiprocessing as mp
import ttclib as T
from oc1_bign import gen
from oc1_bign_climb import mutate

CAPC = 30
ENDS = False    # 'ends': Conjecture OC1-ED instead: the absorber may be either endpoint, x_0 or the head x_t


def hd_count(E, base, cap=CAPC):
    D = T.dangerous_set(E, base); B = T.bundles(E, base); seen = set(); c = 0
    for b2, path in T.iter_chains_path(E, base):
        if len(path) < 2 or path[0] not in D:
            continue
        B2 = T.bundles(E, b2)
        if any(sorted(B2[path[i]]) != sorted(B[path[i - 1]]) for i in range(1, len(path) - 1)):
            continue
        key = (b2, path[-1])
        if key in seen:
            continue
        seen.add(key)
        if T.extends_owner(E, b2, path[-1]) or (ENDS and T.extends_owner(E, b2, path[0])):
            c += 1
            if c >= cap:
                break
    return c


def evaluate(sets, vals, m, ords):
    E = T.Enc(sets, vals, m); hard = 0; least = CAPC; bad = None; done = {}; danger = 0
    for o in ords:
        Y = tuple(T.sd(E, o)[0])
        if Y in done:
            continue
        base = T.base_of(E, Y)
        # soft signal as in oc1_bign_climb.py: frozen agents whose junk is worth more than their pick
        J = [g for g in range(m) if base[g] < 0]
        for x in T.frozen_set(E, base):
            if T.val(E, x, [g for g in J if E.v[x].get(g, 0) > 0]) > T.val(E, x, [Y[x]]):
                danger += 1
        if T.extends_A(E, base, 1):
            done[Y] = None; continue
        hard += 1; r = hd_count(E, base); done[Y] = r; least = min(least, r)
        if r == 0:
            bad = (o, Y)
    return ((hard * CAPC - least) * 1000 + danger) if hard else danger, hard, least, bad


def run(args):
    n, rounds, norders, seed = args
    rng = random.Random(seed)
    sets, vals, m = gen(n, rng)
    ords = [list(range(n)), list(range(n))[::-1]]
    while len(ords) < norders:
        o = list(range(n)); rng.shuffle(o); ords.append(o)
    best = evaluate(sets, vals, m, ords); found = []
    for r in range(rounds):
        mu = mutate(sets, vals, m, rng)
        if mu is None:
            continue
        ev = evaluate(mu[0], mu[1], m, ords)
        if ev[3] is not None:
            E = T.Enc(mu[0], mu[1], m); base = T.base_of(E, ev[3][1])
            oc1 = any(T.extends_A(E, b2, 1) for b2 in set(T.DF.iter_chains(E, base)))
            found.append((mu[0], mu[1], m, ev[3], oc1))
        if ev[0] >= best[0]:
            sets, vals = mu; best = ev
    return n, seed, best, sets, vals, m, found


if __name__ == '__main__':
    NR, ROUNDS, ORD, SEED, NMIN, NMAX = map(int, sys.argv[1:7])
    ENDS = 'ends' in sys.argv[7:]
    print('$ python3 k4/ttc/head_bign_climb.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter()
    tasks = [(NMIN + t % (NMAX - NMIN + 1), ROUNDS, ORD, SEED * 1009 + t) for t in range(NR)]
    with mp.Pool(max(1, (os.cpu_count() or 2) - 1)) as pool:
        for n, seed, best, sets, vals, m, found in pool.imap_unordered(run, tasks):
            C['runs n=%d' % n] += 1
            print('run n=%d seed=%d score=%d hard=%d least=%d' % (n, seed, best[0], best[1], best[2]),
                  json.dumps((sets, vals)), flush=True)
            for s_, v_, m_, (o, Y), oc1 in found:
                C['OC1-HD failures'] += 1; C['  of which plain OC1 holds'] += oc1
                print('OC1-HD FAILS', json.dumps({'sets': s_, 'vals': v_, 'm': m_, 'order': o, 'picks': Y,
                                                  'OC1 holds': oc1}), flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
