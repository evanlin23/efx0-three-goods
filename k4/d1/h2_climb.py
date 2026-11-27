"""Climb toward counterexamples to Conjecture D1-H2 (k4/d1.md §7).  Evidence generator.

Score of an instance (max over orders): 1 for a hard all-HEAD start with D = {k}; +10 if no canonical chain repairs
(only the extension can); +100 if D1-H2 fails (printed and recorded).  Seeds: D1H-X, S2-X and random instances with
n = 3-5.

    python3 k4/d1/h2_climb.py TAG SEED SECONDS
"""
import sys, os, random, itertools, json, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from d1lib import Inst, sd_picks, Start, one_absorber, canonical_chains, pool, minimal_improving, obstacles
from crowd_hunt import rand_inst, mutate
from head_hunt import all_head
from h2_check import h2_repairs

SEEDS = [([[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7]], [[26, 3, 25, 27], [19, 17, 25, 30], [9, 14, 7, 29]], 8),
         ([[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7], [8, 6, 7, 3]], [[26, 3, 25, 27], [19, 17, 25, 30], [9, 14, 7, 29], [14, 11, 1, 7]], 9)]


def score(sets, vals, m, C, fo):
    I = Inst(sets, vals, m); best = 0; seen = set()
    if len(set(g for s in sets for g in s)) != I.m: return 0
    for od in itertools.permutations(range(I.n)):
        Y = sd_picks(I, od)
        if Y in seen: continue
        seen.add(Y); S = Start(I, Y)
        if len(S.D) != 1: continue
        k = S.D[0]
        if not all_head(S, k): continue
        if one_absorber(I, S.B): best = max(best, 0.5); continue
        reps = h2_repairs(S, k); sc = 1
        C['hard all-HEAD starts'] += 1
        if not any(r[0] == 'canonical' for r in reps):
            sc += 10; C['  no canonical repair'] += 1
            fo.write(json.dumps(dict(sets=sets, vals=vals, m=m, order=list(od), picks=list(Y), k=k, reps=[list(map(str, r)) for r in reps])) + '\n'); fo.flush()
        if not reps:
            sc += 100; C['  D1-H2 FAILS'] += 1
            print('D1-H2 FAILS', json.dumps((sets, vals)), od, Y, flush=True)
        best = max(best, sc)
    return best


if __name__ == '__main__':
    tag, seed, secs = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    fo = open(os.path.join(ROOT, 'results', 'k4_d1', 'h2climb_%s.jsonl' % tag), 'w')
    print('$ python3 k4/d1/h2_climb.py', *sys.argv[1:], flush=True)
    cur = None; cs = -1; stall = 0; it = 0
    while time.time() - t0 < secs:
        it += 1
        if cur is None or stall > 500:
            cur = rng.choice(SEEDS) if rng.random() < 0.5 else rand_inst(rng, rng.choice([3, 4, 4, 5])); cs = -1; stall = 0
        cand = mutate(rng, *cur) if cs >= 0 else cur
        if max(len(s) for s in cand[0]) > 4 or min(len(s) for s in cand[0]) < 1: stall += 1; continue
        sc = score(*cand, C, fo)
        if sc > cs: cur, cs, stall = cand, sc, 0
        elif sc == cs: cur = cand; stall += 1
        else: stall += 1
        if it % 2000 == 0: print(int(time.time() - t0), it, dict(C), flush=True)
    print('final', int(time.time() - t0), it)
    for key in sorted(C): print(key, C[key])
