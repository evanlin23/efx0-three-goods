"""Probe of Observation S1 (k4/d1.md §7.1): random four-agent instances in which k picks first and its pick a is wanted
by three unfrozen agents.  Counts the starts that are one-absorber-hard and all-HEAD (S1 would fail), and checks D1-H2
on them.  Evidence generator.

    python3 k4/d1/s1_probe.py SEED SECONDS
"""
import sys, os, random, json, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from d1lib import Inst, sd_picks, Start, one_absorber
from head_hunt import all_head
from h2_check import h2_repairs

rng = random.Random(int(sys.argv[1])); secs = float(sys.argv[2]); t0 = time.time(); C = collections.Counter()
print('$ python3 k4/d1/s1_probe.py', *sys.argv[1:], flush=True)
while time.time() - t0 < secs:
    nj = rng.randint(2, 6); junk = list(range(4, 4 + nj))
    # k: a = 0 plus up to 3 junk; wanters 1, 2, 3: a, own pick, up to 2 of junk + other picks
    sets = [[0] + rng.sample(junk, rng.randint(1, min(3, nj)))]
    for u in (1, 2, 3):
        others = junk + [p for p in (1, 2, 3) if p != u]
        sets.append([0, u] + rng.sample(others, rng.randint(1, 2)))
    if any(not any(g in s for s in sets) for g in junk): continue
    vals = []
    top = rng.randint(10, 40); vals.append([top] + rng.sample(range(1, top), len(sets[0]) - 1))
    for u in (1, 2, 3):
        p = rng.randint(5, 30); A = rng.randint(p + 1, 2 * p + 5)
        vals.append([A, p] + [rng.randint(1, p) for _ in sets[u][2:]])
    I = Inst(sets, vals, 4 + nj); C['instances'] += 1
    Y = sd_picks(I, (0, 1, 2, 3))
    if Y != (0, 1, 2, 3): continue
    S = Start(I, Y)
    if S.D != [0] or sorted(S.W[0]) != [1, 2, 3] or any(S.W[j] for j in (1, 2, 3)): continue
    C['three unfrozen wanters of a, D = {k}'] += 1
    if not all_head(S, 0): continue
    C['  all-HEAD'] += 1
    if one_absorber(I, S.B): continue
    C['  all-HEAD and hard (S1 FAILS)'] += 1
    reps = h2_repairs(S, 0)
    C['    D1-H2 holds'] += bool(reps)
    print('S1 FAILS', json.dumps((sets, vals)), 'D1-H2', bool(reps), flush=True)
for k in sorted(C): print(k, C[k])
