"""Adversarial climb for OC1 (k4/sdc.md §29) at n = 6..8.  oc1_bign.py found random instances easy (24,000 starts,
n = 6-9: 115 need one chain, none more).  Here: start from a random degree-3/4 instance, and hill-climb on the
values (and occasionally on the incidence: swap one relevant good of one agent, keeping degrees <= 4) to maximise

    hardness = (number of sampled starts whose picks have no one-absorber completion,
                minus the number of improving chains that repair the hardest such start, capped)

so the climb is pushed toward starts that need a chain and have few repairing chains.  Every start that needs a
chain is checked fully (all chains, de_free.iter_chains); a start with none is an OC1 counterexample and is printed.

    python3 k4/sdc/oc1_bign_climb.py N_RUNS ROUNDS ORDERS SEED NMIN NMAX"""
import sys, os, json, random, collections, time, multiprocessing as mp
import _paths
import de_free as DF
from oc_absorb import extends_A
from sdclib import Enc
from sdc_orders import sd
from oc1_bign import gen

DF.CHAIN_ONLY = True
CAPC = 30


def repairing(E, base, cap=CAPC):
    seen = set(); c = 0
    for b2 in DF.iter_chains(E, base):
        if b2 in seen: continue
        seen.add(b2)
        if extends_A(E, b2, 1):
            c += 1
            if c >= cap: break
    return c


def evaluate(sets, vals, m, ords):
    E = Enc(sets, vals, m); hard = 0; least = CAPC; bad = None; done = {}; danger = 0
    v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
    for o in ords:
        Y = tuple(sd(E, o)[0])
        if Y in done: continue
        base = [-1] * m
        for i, g in enumerate(Y):
            if g is not None: base[g] = i
        base = tuple(base)
        # soft signal: frozen agents whose junk is worth more than their pick ("truly dangerous", k4/sdc.md §30)
        J = [g for g in range(m) if base[g] < 0]
        for x, gx in enumerate(Y):
            if gx is None: continue
            if any(i != x and v[i].get(gx, 0) > v[i].get(Y[i], 0) for i in range(len(Y))) and \
                    sum(v[x].get(g, 0) for g in J) > v[x][gx]:
                danger += 1
        if extends_A(E, base, 1): done[Y] = None; continue
        hard += 1; r = repairing(E, base); done[Y] = r
        least = min(least, r)
        if r == 0: bad = (o, Y)
    return (hard * CAPC - least) * 1000 + danger if hard else danger, hard, least, bad


def mutate(sets, vals, m, rng):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    i = rng.randrange(len(sets))
    if rng.random() < 0.8:
        j = rng.randrange(len(vals[i])); vals[i][j] = max(1, vals[i][j] + rng.choice([-3, -2, -1, 1, 2, 3]))
        if len(set(vals[i])) < len(vals[i]): return None
    else:
        j = rng.randrange(len(sets[i])); g = rng.randrange(m)
        if g in sets[i]: return None
        sets[i][j] = g
        if len(set().union(*map(set, sets))) < m: return None
    return sets, vals


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
        if mu is None: continue
        s2, v2 = mu
        sc = evaluate(s2, v2, m, ords)
        if sc[3] is not None: found.append((s2, v2, m, sc[3]))
        if sc[0] >= best[0]: sets, vals, best = s2, v2, sc
    return n, seed, best[:3], found, sets, vals, m


if __name__ == '__main__':
    N, R, ORD, SEED, NMIN, NMAX = map(int, sys.argv[1:7])
    print('$ python3 k4/sdc/oc1_bign_climb.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter()
    tasks = [(NMIN + (t % (NMAX - NMIN + 1)), R, ORD, SEED * 7919 + t) for t in range(N)]
    with mp.Pool(max(1, os.cpu_count())) as pool:
        for n, seed, best, found, sets, vals, m in pool.imap_unordered(run, tasks):
            C['runs n=%d' % n] += 1
            C['n=%d final hard starts %d' % (n, best[1])] += 1
            if best[1]: C['n=%d final least repairing chains %d' % (n, best[2])] += 1
            print('run n=%d seed=%d score=%s hard=%d least=%d %s' % (n, seed, best[0], best[1], best[2],
                  json.dumps((sets, vals))), flush=True)
            for s2, v2, mm, (o, Y) in found:
                C['OC1 counterexamples'] += 1
                print('OC1 FAILS', json.dumps({'n': n, 'm': mm, 'sets': s2, 'vals': v2, 'order': o, 'picks': Y}), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
