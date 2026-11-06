"""The lexicographic favourite potential (k4/sdc.md §22): for each order pi, the EFX0 allocations maximizing
(v_pi1(F_pi1), v_pi2(F_pi2), ...) lexicographically; is every maximizer SD-consistent, for every pi or for some pi?
Checked on the PHI counterexamples, T3 and random n = 3 instances.

    python3 k4/sdc/phi_lex.py SEED T K"""
import itertools, random, sys, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phi_check import efx0, fav, sd_consistent, strict
def lexfav(val, X, order):
    return tuple((val[i][fav(val[i], X[i])] if fav(val[i], X[i]) is not None else 0) for i in order)
cases = {'PHI4 cex': [[25,0,0,50,55,0,0],[63,0,23,0,16,62,0],[0,31,44,0,61,0,49]],
         'PHI general cex': [[0,0,55,57,0,0,0],[50,1,0,58,76,75,70],[0,11,58,68,41,26,21]],
         'T3': [[38,0,6,0,36,1],[0,22,0,12,30,0],[38,20,0,12,28,0]]}
def test(val):
    n = len(val); m = len(val[0])
    E = []
    for asg in itertools.product(range(n), repeat=m):
        X = [[g for g in range(m) if asg[g] == i] for i in range(n)]
        if efx0(val, X, n): E.append(X)
    res = {}
    for order in itertools.permutations(range(n)):
        best = max(lexfav(val, X, order) for X in E)
        mx = [X for X in E if lexfav(val, X, order) == best]
        res[order] = all(sd_consistent(val, X, n, m) for X in mx)
    return res
print('$ python3 k4/sdc/phi_lex.py', *sys.argv[1:])
for name, val in cases.items():
    r = test(val); print(name, 'every order:', all(r.values()), 'some order:', any(r.values()), r)
rng = random.Random(int(sys.argv[1])); C = collections.Counter()
for t in range(int(sys.argv[2])):
    n = 3; m = rng.randint(4, 7); val = []
    for i in range(n):
        R = rng.sample(range(m), rng.randint(2, int(sys.argv[3]))); vs = rng.sample(range(1, 80), len(R))
        val.append([vs[R.index(g)] if g in R else 0 for g in range(m)])
    if any(all(val[i][g] == 0 for i in range(n)) for g in range(m)): continue
    r = test(val); C['inst'] += 1; C['every order'] += all(r.values()); C['some order'] += any(r.values())
    if not any(r.values()): print('NO ORDER', val)
print(dict(C))
