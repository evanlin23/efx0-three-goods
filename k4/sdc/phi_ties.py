"""Two agents with tied values (k4/sdc.md §20): for several potentials over the EFX0 allocations, is every maximizer
(and some maximizer) SD-consistent?  Phi = "fav-values" (sum of the values of the favourite held goods).

    python3 k4/sdc/phi_ties.py SEED T M"""
import itertools, random, sys, collections, math
def efx0(val, X):
    for i in range(2):
        vi = sum(val[i][g] for g in X[i]); j = 1 - i
        for h in X[j]:
            if sum(val[i][g] for g in X[j] if g != h) > vi: return False
    return True
def rank(v, m): return sorted([g for g in range(m) if v[g] > 0], key=lambda g: (-v[g], g))
def fav(v, S):
    S = [g for g in S if v[g] > 0]
    return max(S, key=lambda g: (v[g], -g)) if S else None
def sdc(val, m, X):
    """Lemma 1 for n = 2: some SD order's picks lie in the bundles"""
    for o in ((0, 1), (1, 0)):
        left = set(range(m)); ok = True
        for i in o:
            y = fav(val[i], left)
            if y is not None:
                if y not in X[i]: ok = False; break
                left.discard(y)
        if ok: return True
    return False
POTS = {
  'utilitarian': lambda val, X: sum(sum(val[i][g] for g in X[i]) for i in range(2)),
  'nash': lambda val, X: (sum(1 for i in range(2) if sum(val[i][g] for g in X[i]) > 0), sum(math.log(sum(val[i][g] for g in X[i])) for i in range(2) if sum(val[i][g] for g in X[i]) > 0)),
  'leximin': lambda val, X: tuple(sorted(sum(val[i][g] for g in X[i]) for i in range(2))),
  'fav-values': lambda val, X: sum((val[i][fav(val[i], X[i])] if fav(val[i], X[i]) is not None else 0) for i in range(2)),
}
print('$ python3 k4/sdc/phi_ties.py', *sys.argv[1:])
rng = random.Random(int(sys.argv[1])); T = int(sys.argv[2]); M = int(sys.argv[3]); C = collections.Counter()
for t in range(T):
    m = rng.randint(2, M)
    val = [[rng.choice([0, 1, 2, 3, 5, 8, 13, rng.randint(1, 30)]) for g in range(m)] for i in range(2)]
    E = []
    for asg in itertools.product(range(2), repeat=m):
        X = [[g for g in range(m) if asg[g] == i] for i in range(2)]
        if efx0(val, X): E.append(X)
    C['instances'] += 1
    for name, f in POTS.items():
        best = max(f(val, X) for X in E)
        mx = [X for X in E if f(val, X) == best]
        if all(sdc(val, m, X) for X in mx): C[name + ': every maximizer SD-consistent'] += 1
        if any(sdc(val, m, X) for X in mx): C[name + ': some maximizer SD-consistent'] += 1
for k in sorted(C): print(k, C[k])
