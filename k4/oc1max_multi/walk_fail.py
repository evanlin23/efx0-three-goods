"""Collect OC1 failures at perfect starts near the known ones (k4/oc1max_multi.md §8; evidence only).

From each of the 12 known OC1^max counterexamples (cex_check.instances), a walk in the value neighbourhood: change one
value by +-1..3, keep it positive and the profile strict (disjoint nonempty subsets of R_i have different values);
accept the step if the number of distinct failing perfect starts (no one-absorber completion at the picks or after
one official move; raw enumeration, mmlib) does not drop.  Every distinct failing (profile, start) pair is written as a
JSON line (sets, vals, order, picks) to OUT.  The hypergraph is not changed, and core conditions are not imposed
(Lemma RED makes perfect starts of arbitrary instances the target).

    OUT=file python3 k4/oc1max_multi/walk_fail.py STEPS SEED
"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, oa_absorbers, moves, is_perfect
from cex_check import instances


def strict(vals):
    for x in vals:
        sums = collections.defaultdict(list)
        for r in range(1, len(x) + 1):
            for T in itertools.combinations(range(len(x)), r): sums[sum(x[k] for k in T)].append(set(T))
        for L in sums.values():
            if any(not (a & b) for a, b in itertools.combinations(L, 2)): return False
    return True


def failing_starts(sets, vals):
    I = Inst(sets, vals); out = []
    for od in itertools.permutations(range(I.n)):
        Y = I.sd(od)
        if Y in [y for y, _ in out] or not is_perfect(I, Y): continue
        b = base_from_picks(Y)
        if oa_absorbers(I, b): continue
        if any(oa_absorbers(I, nb) for nb in moves(I, b)): continue
        out.append((Y, od))
    return out


def walk(args):
    x, steps, seed = args
    rng = random.Random(seed); sets = x['sets']; vals = [list(v) for v in x['vals']]
    seen = {}
    cur = failing_starts(sets, vals)
    for Y, od in cur: seen[json.dumps((vals, Y))] = (sets, [list(v) for v in vals], od, Y)
    for _ in range(steps):
        v2 = [list(v) for v in vals]; i = rng.randrange(len(v2)); j = rng.randrange(len(v2[i]))
        v2[i][j] += rng.choice([-3, -2, -1, 1, 2, 3])
        if v2[i][j] < 1 or not strict(v2): continue
        f = failing_starts(sets, v2)
        if len(f) >= len(cur) and f:
            vals, cur = v2, f
            for Y, od in cur:
                k = json.dumps((vals, Y))
                if k not in seen: seen[k] = (sets, [list(v) for v in vals], od, Y)
    return x['name'], list(seen.values())


if __name__ == '__main__':
    steps, seed = int(sys.argv[1]), int(sys.argv[2]); t0 = time.time()
    tasks = [(x, steps, seed * 1000 + i) for i, x in enumerate(instances())]
    out = open(os.environ['OUT'], 'w') if os.environ.get('OUT') else None
    print('$ python3 k4/oc1max_multi/walk_fail.py', steps, seed, flush=True)
    tot = 0
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for name, recs in pool.imap_unordered(walk, tasks):
            print(name, 'distinct failing (profile, start) pairs', len(recs), flush=True); tot += len(recs)
            for sets, vals, od, Y in recs:
                if out: out.write(json.dumps({'name': name, 'sets': sets, 'vals': vals, 'order': od, 'picks': Y}) + '\n')
    print('total', tot, 'time %.0f s' % (time.time() - t0))
