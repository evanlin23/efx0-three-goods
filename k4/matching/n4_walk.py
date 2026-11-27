"""Walks in the value neighbourhood of the 11 n = 4 OC1^max failures (k4/matching.md §5; evidence only).

From each failing profile (results/k4_matching/data/oc1max_cex_n4.json), mutate one value by +-1..3, keeping the
hypergraph; keep the result only if it is again a strict connected core (k4/sdc/oc1max_climb.is_core).  Score:
    10000 * (CM2 failures or EX* inexact on the second move) + 1000 * (starts where one move gives an S* completion
    but no Lemma EX* exchange exists) + (OC1 failures)
over the distinct perfect starts of every order; accept if the score does not drop (so the walk stays in the OC1
failure region while it lasts).  Every start where CM and OC1 disagree, CM2 fails, or EX* is not exact on the second
move is printed.

    python3 k4/matching/n4_walk.py STEPS SEED"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from exchange import ex_star_witness
from oc1max_climb import is_core
DUMP = os.environ.get('DUMP')   # DUMP=file.jsonl: also write every distinct failing (profile, start) pair
DUMP2 = os.environ.get('DUMP2')  # DUMP2=file.jsonl: also write the starts that OC1 repairs only through a non-S* completion


def evaluate(sets, vals, seen):
    I = M(sets, vals); score = 0; C = collections.Counter(); bad = []
    for Y in sorted(set(I.sd(o) for o in itertools.permutations(range(I.n))), key=str):
        if any(y is None for y in Y): continue
        base = [[g] for g in Y]
        if I.complete(base, 0, 'oa') is not None: continue
        key = json.dumps((vals, Y)); C['hard perfect starts'] += 1
        first = I.moves(base)
        cm = ex_star_witness(I, base) is not None
        oc1 = any(I.complete(B1, 0, 'oa') is not None for B1 in first)
        C['CM %s, OC1 %s' % (cm, oc1)] += 1
        if cm != oc1:
            ss1 = any(I.complete(B1, 0, 'ss') is not None for B1 in first)
            C['CM False, OC1 True: some move has an S* completion %s' % ss1] += 1
            if ss1: score += 1000; bad.append(('CM != OC1 although S* repairs', Y))
            elif DUMP2: bad.append(('nonS*', Y))
        if cm: continue
        score += 0 if oc1 else 1
        ex1 = [ex_star_witness(I, B1) is not None for B1 in first]
        if oc1:   # OC1 holds only through a non-S* completion: does CM2 still hold?
            C['CM False, OC1 True: CM2 %s' % any(ex1)] += 1
            if not any(ex1): score += 10000; bad.append(('CM2 fails (OC1 holds)', Y))
            continue
        oc2 = [e or any(I.complete(B2, 0, 'oa') is not None for B2 in I.moves(B1)) for e, B1 in zip(ex1, first)]
        C['OC1 fails: CM2 %s, OC2 %s, EX* exact on the second move %s' % (any(ex1), any(oc2), ex1 == oc2)] += 1
        if not any(ex1) or ex1 != oc2: score += 10000; bad.append(('second move', Y, sum(ex1), sum(oc2)))
        if key not in seen:
            seen.add(key); C['distinct failing (profile, start)'] += 1
            if DUMP: bad.append(('failing', Y))
    return score, C, bad


def run(args):
    t, sets, vals, steps, seed = args
    rng = random.Random(seed); seen = set(); T = collections.Counter(); found = []
    best, C, bad = evaluate(sets, vals, seen); T.update(C); found += [(vals, b) for b in bad]
    for _ in range(steps):
        v2 = [list(x) for x in vals]; i = rng.randrange(len(v2)); k = rng.randrange(len(v2[i]))
        v2[i][k] = max(1, v2[i][k] + rng.choice([-3, -2, -1, 1, 2, 3]))
        if not is_core(sets, v2, False): continue
        sc, C, bad = evaluate(sets, v2, seen); T.update(C); found += [(v2, b) for b in bad]
        if sc >= best: vals, best = v2, sc
    return t, sets, T, found


if __name__ == '__main__':
    STEPS, SEED = map(int, sys.argv[1:3])
    D = json.load(open(os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'oc1max_cex_n4.json')))['instances']
    print('$ python3 k4/matching/n4_walk.py', *sys.argv[1:], flush=True)
    tasks = [(t, d['sets'], d['vals'], STEPS, SEED * 1009 + t) for t, d in enumerate(D)]
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for t, sets, C, found in pool.imap_unordered(run, tasks):
            T.update(C)
            print('hypergraph %d: distinct failing (profile, start) pairs visited %d' % (t, C['distinct failing (profile, start)']), flush=True)
            for vals, b in found:
                if b[0] == 'nonS*':
                    with open(DUMP2, 'a') as fo: fo.write(json.dumps({'sets': sets, 'vals': vals, 'picks': list(b[1])}) + '\n')
                    continue
                if b[0] == 'failing':
                    if not DUMP: continue
                    with open(DUMP, 'a') as fo: fo.write(json.dumps({'sets': sets, 'vals': vals, 'picks': list(b[1])}) + '\n')
                    continue
                print('   ', b[0], json.dumps({'sets': sets, 'vals': vals, 'picks': b[1]}), b[2:], flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
