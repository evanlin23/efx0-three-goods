"""Adversarial climb against Conjecture OC1-p (k4/ttc.md §13): OC1 with absorbers counted only among agents holding a
pick (agents without a base may take any number of junk goods; ttclib.extends_A_pickless).  A start is hard when its
picks have no such completion; its repairing count is the number of improving moves of de_free (additions and chains,
de_free.CHAIN_ONLY) whose result has one, capped at CAPC.  Score and mutations as in head_bign_climb.py (values and
incidences, the soft signal of frozen agents with junk worth more than their pick).  Starts: random (oc1_bign's
generator) or, with 'seeded', the 84 OC1 counterexamples of results/k4_ttc/oc1_counterexamples.json.  A start with
count 0 is printed (an OC1-p counterexample; plain OC (free completion after one move) is then checked).

    python3 k4/ttc/oc1p_climb.py N_RUNS ROUNDS ORDERS SEED NMIN NMAX [seeded]"""
import sys, os, json, random, collections, time, multiprocessing as mp
import ttclib as T
from oc1_bign import gen
from oc1_bign_climb import mutate

CAPC = 30
SEEDED = False


def count(E, base, cap=CAPC):
    seen = set(); c = 0
    for b2 in T.DF.iter_chains(E, base):
        if b2 in seen:
            continue
        seen.add(b2)
        if T.extends_A_pickless(E, b2, 1):
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
        J = [g for g in range(m) if base[g] < 0]
        for x in T.frozen_set(E, base):
            if T.val(E, x, [g for g in J if E.v[x].get(g, 0) > 0]) > T.val(E, x, [Y[x]]):
                danger += 1
        if T.extends_A_pickless(E, base, 1):
            done[Y] = None; continue
        hard += 1; r = count(E, base); done[Y] = r; least = min(least, r)
        if r == 0:
            bad = (o, Y)
    return ((hard * CAPC - least) * 1000 + danger) if hard else danger, hard, least, bad


def run(args):
    n, rounds, norders, seed = args
    rng = random.Random(seed)
    if SEEDED:
        ds = json.load(open(os.path.join(T.ROOT, 'results', 'k4_ttc', 'oc1_counterexamples.json')))
        d = ds[seed % len(ds)]; sets, vals, m = [list(x) for x in d['sets']], [list(x) for x in d['vals']], d['m']
        n = len(sets)
    else:
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
            oc = T.DF.extends(E, base) or any(T.DF.extends(E, b2) for b2 in set(T.DF.iter_chains(E, base)))
            found.append((mu[0], mu[1], m, ev[3], oc))
        if ev[0] >= best[0]:
            sets, vals = mu; best = ev
    return n, seed, best, sets, vals, m, found


if __name__ == '__main__':
    NR, ROUNDS, ORD, SEED, NMIN, NMAX = map(int, sys.argv[1:7]); SEEDED = 'seeded' in sys.argv[7:]
    print('$ python3 k4/ttc/oc1p_climb.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter()
    tasks = [(NMIN + t % (NMAX - NMIN + 1), ROUNDS, ORD, SEED * 1009 + t) for t in range(NR)]
    with mp.Pool(max(1, (os.cpu_count() or 2) - 1)) as pool:
        for n, seed, best, sets, vals, m, found in pool.imap_unordered(run, tasks):
            C['runs n=%d' % n] += 1
            print('run n=%d seed=%d score=%d hard=%d least=%d' % (n, seed, best[0], best[1], best[2]),
                  json.dumps((sets, vals)), flush=True)
            for s_, v_, m_, (o, Y), oc in found:
                C['OC1-p failures'] += 1; C['  of which OC (free completion, <= 1 move) holds'] += oc
                print('OC1-p FAILS', json.dumps({'sets': s_, 'vals': v_, 'm': m_, 'order': o, 'picks': Y,
                                                 'OC holds': oc}), flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
