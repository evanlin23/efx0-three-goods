"""SD-C for two agents (k4/sdc.md §20), brute force: random two-agent additive instances (zeros and ties allowed, up to M
goods); for each, does some serial-dictatorship order's picks extend to an EFX0 allocation (raw definition)?

    python3 k4/sdc/n2_sdc.py SEED T M"""
import itertools, random, sys
def efx0(val, X):
    n = len(X)
    for i in range(n):
        vi = sum(val[i][g] for g in X[i])
        for j in range(n):
            if i != j:
                for h in X[j]:
                    if sum(val[i][g] for g in X[j] if g != h) > vi: return False
    return True
def top(v, S):  # favourite with tie-break by index
    return max(S, key=lambda g: (v[g], -g))
def sd(val, order, m):
    left = set(range(m)); Y = {}
    for i in order:
        av = [g for g in left if val[i][g] > 0]
        Y[i] = top(val[i], av) if av else None
        if Y[i] is not None: left.discard(Y[i])
    return Y
def extends(val, Y, m):
    n = len(val); rest = [g for g in range(m) if g not in Y.values()]
    for a in itertools.product(range(n), repeat=len(rest)):
        X = [[Y[i]] if Y[i] is not None else [] for i in range(n)]
        for g, i in zip(rest, a): X[i].append(g)
        if efx0(val, X): return True
    return False
print('$ python3 k4/sdc/n2_sdc.py', *sys.argv[1:])
rng = random.Random(int(sys.argv[1])); bad = 0; T = int(sys.argv[2]); M = int(sys.argv[3])
for t in range(T):
    m = rng.randint(2, M); n = 2
    val = [[rng.choice([0, 0, 1, 2, 3, 5, 8, 13, rng.randint(1, 30)]) for g in range(m)] for i in range(n)]
    ok = any(extends(val, sd(val, o, m), m) for o in itertools.permutations(range(n)))
    if not ok: bad += 1; print('FAIL', val, flush=True)
print('instances', T, 'SD-C failures', bad)
