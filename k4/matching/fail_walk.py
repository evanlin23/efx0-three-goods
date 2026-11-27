"""Value walks near a start with no one-move repair, collecting such starts and testing OC2-REC on each (k4/matching.md
§6; evidence only).

From the given profile, each step changes one value by +-1..3 and keeps the hypergraph. The result is kept only if it
is again a strict connected core (k4/sdc/oc1max_climb.is_core). For every distinct perfect SD start of every order,
the walk tests:
  - hard: no one-absorber completion at the picks or after any official move (raw);
  - for the hard ones, OC2-REC (n5_census.oc2_rec, the multi session's recursion).
A step is accepted when the score does not drop: 1000 * (OC2-REC failures) + (hard starts). The walk therefore stays
in the failure region and climbs towards OC2-REC failures. Every distinct hard (profile, start) is written to DUMP
as {sets, vals, picks, orders}.

    DUMP=out.jsonl python3 k4/matching/fail_walk.py cex5 STEPS SEED [SEED ...]"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from oc1max_climb import is_core
from n5_census import oc2_rec, load

DUMP = os.environ.get('DUMP')


def evaluate(sets, vals):
    I = M(sets, vals); starts = collections.defaultdict(list)
    for o in itertools.permutations(range(I.n)):
        Y = I.sd(o)
        if all(y is not None for y in Y): starts[Y].append(list(o))
    score = 0; rows = []; C = collections.Counter()
    for Y, orders in sorted(starts.items(), key=str):
        base = [[g] for g in Y]
        if I.complete(base, 0, 'oa') is not None: continue
        if any(I.complete(B1, 0, 'oa') is not None for B1 in I.moves(base)): continue
        C['hard'] += 1; score += 1
        ok = oc2_rec(I, base) is not None
        C['OC2-REC %s' % ok] += 1
        if not ok:
            score += 1000; print('OC2-REC FAILS', json.dumps({'sets': sets, 'vals': vals, 'picks': list(Y)}), flush=True)
        rows.append({'sets': sets, 'vals': vals, 'picks': list(Y), 'orders': orders[:3]})
    return score, C, rows


def run(args):
    sets, vals, steps, seed = args
    rng = random.Random(seed); T = collections.Counter(); out = {}
    best, C, rows = evaluate(sets, vals); T.update(C)
    for r in rows: out[json.dumps([r['vals'], r['picks']])] = r
    for _ in range(steps):
        v2 = [list(x) for x in vals]; i = rng.randrange(len(v2)); k = rng.randrange(len(v2[i]))
        v2[i][k] = max(1, v2[i][k] + rng.choice([-3, -2, -1, 1, 2, 3]))
        if not is_core(sets, v2, False): continue
        sc, C, rows = evaluate(sets, v2); T['profiles'] += 1; T.update({'visits: ' + x: c for x, c in C.items()})
        for r in rows: out.setdefault(json.dumps([r['vals'], r['picks']]), r)
        if sc >= best: vals, best = v2, sc
    return seed, T, list(out.values())


if __name__ == '__main__':
    src = load(sys.argv[1])[0]; STEPS = int(sys.argv[2]); SEEDS = list(map(int, sys.argv[3:]))
    print('$ python3 k4/matching/fail_walk.py', *sys.argv[1:], flush=True)
    T = collections.Counter(); t0 = time.time(); allrows = {}
    with mp.Pool(min(len(SEEDS), int(os.environ.get('PROCS', mp.cpu_count())))) as pool:
        for seed, C, rows in pool.imap_unordered(run, [(src['sets'], src['vals'], STEPS, s) for s in SEEDS]):
            T.update(C)
            for r in rows: allrows.setdefault(json.dumps([r['vals'], r['picks']]), r)
            print('seed %d: profiles %d, distinct hard starts %d' % (seed, C['profiles'], len(rows)), flush=True)
    for x in sorted(T): print(x, T[x])
    print('distinct hard (profile, start) pairs over all seeds:', len(allrows))
    if DUMP:
        with open(DUMP, 'w') as f:
            for r in allrows.values(): f.write(json.dumps(r) + '\n')
        print('wrote', DUMP)
    print('time %.0f s' % (time.time() - t0))
