"""How the k = 4 counterexample to PHI4 was found (k4/sdc.md §21): start from the k = 5 failure of a random search
(phi_check.py random 72 6000 3 8 6) and zero or perturb values while PHI keeps failing, until every agent values at most
four goods.

    python3 k4/sdc/phi_reduce.py"""
import sys, itertools, random
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phi_check import analyse, strict
base = [[25, 0, 0, 50, 55, 0, 0], [63, 0, 23, 1, 16, 62, 0], [0, 31, 44, 0, 61, 0, 49]]
n, m = 3, 7
def fails(val):
    if not strict(val) or any(all(val[a][h] == 0 for a in range(n)) for h in range(m)): return False
    best, mx, gap = analyse(val, n, m)
    return any(not ok for X, ok in mx)
print('base fails', fails(base))
# try zeroing one of agent 1's values (agent 1 values 5 goods)
for g in range(m):
    if base[1][g] > 0:
        v = [list(r) for r in base]; v[1][g] = 0
        print('zero agent 1 good', g, 'fails', fails(v))
# random local search: keep failure, minimize max number of valued goods per agent
rng = random.Random(1); cur = [list(r) for r in base]
def kmax(v): return max(sum(1 for x in r if x > 0) for r in v)
best = None
for it in range(4000):
    v = [list(r) for r in cur]; i = rng.randrange(n); g = rng.randrange(m)
    if rng.random() < 0.5 and v[i][g] > 0: v[i][g] = max(1, v[i][g] + rng.choice([-9, -5, -2, 2, 5, 9]))
    elif v[i][g] > 0 and rng.random() < 0.7: v[i][g] = 0
    else: v[i][g] = rng.randint(1, 70)
    if fails(v) and kmax(v) <= kmax(cur):
        cur = v
        if kmax(cur) <= 4: print('k <= 4 FAILURE', cur, flush=True); break
print('final kmax', kmax(cur), cur)
