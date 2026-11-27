"""Lemma ABS (k4/RFMIN.md §3): at a maximum-matching serial-dictatorship start Y (strict additive values, every agent
at most four relevant goods), if some agent f holds a private good (valued by nobody else) and no frozen agent values
the whole junk set J above its pick, then the picks have a one-absorber EFX0 completion with absorber f:
receivers threatened by the junk left with f take, in turn, their most valuable junk good still free; f takes the rest.
This script (1) builds that completion wherever the hypotheses hold and checks it with the raw EFX0 definition, on
random strict instances (cores or not) and every order; (2) checks on the stored OC1^max-failing starts that no start
satisfies the hypotheses (the lemma says OC1 would hold there).
Usage: absorb.py random N_INSTANCES [SEED] [--kmin=2] [--kmax=4] [--nmax=6] | absorb.py data FILE.json.gz ...
(--kmax=5 is the sensitivity test: the proof uses at most three junk goods per receiver, and fails at k = 5)"""
import sys, gzip, json, random, itertools, collections

def sd(v, order):
    taken, Y = set(), [None] * len(v)
    for a in order:
        best = max((g for g in v[a] if g not in taken), key=lambda g: v[a][g], default=None)
        if best is not None: Y[a] = best; taken.add(best)
    return Y

def nu(v):
    match = {}
    def aug(a, seen):
        for g in v[a]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen): match[g] = a; return True
        return False
    return sum(aug(a, set()) for a in range(len(v)))

def efx0(v, X):
    for i in range(len(v)):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(len(v)):
            if i == j or len(X[j]) < 2: continue
            tot = sum(v[i].get(g, 0) for g in X[j])
            if any(tot - v[i].get(g, 0) > own for g in X[j]): return False
    return True

def frozen(v, Y, a):
    return Y[a] is not None and any(i != a and v[i].get(Y[a], 0) > (v[i].get(Y[i], 0) if Y[i] is not None else 0)
                                    for i in range(len(v)))

def hypotheses(v, Y, m):
    """(f, J) if Lemma ABS applies at Y, else None."""
    n = len(v)
    J = set(range(m)) - {g for g in Y if g is not None}
    privs = [f for f in range(n) if Y[f] is not None and all(Y[f] not in v[i] for i in range(n) if i != f)]
    if not privs: return None
    for i in range(n):
        if frozen(v, Y, i) and sum(v[i].get(g, 0) for g in J) > v[i][Y[i]]: return None
    return privs[0], J

def construct(v, Y, f, J):
    n = len(v)
    X = [[Y[a]] if Y[a] is not None else [] for a in range(n)]
    free = set(J)
    for r in range(n):
        if r == f or Y[r] is None or frozen(v, Y, r): continue
        if sum(v[r].get(g, 0) for g in free) > v[r][Y[r]]:
            g = max((g for g in free if g in v[r]), key=lambda g: v[r][g], default=None)
            if g is not None: X[r].append(g); free.discard(g)
    X[f] += sorted(free)
    return X

def random_instance(rng, n, m, kmax=4, kmin=2):
    while True:
        v = []
        for a in range(n):
            k = rng.randint(min(kmin, m), min(kmax, m))
            gs = rng.sample(range(m), k)
            vals = rng.sample(range(1, 60), k)
            v.append(dict(zip(gs, vals)))
        if set().union(*[set(x) for x in v]) == set(range(m)): return v

def run_random(N, seed=1, kmax=4, kmin=2, nmax=6):
    rng = random.Random(seed)
    C = collections.Counter()
    for t in range(N):
        n = rng.randint(3, nmax); m = rng.randint(max(n, 4), 2 * n + 1)
        v = random_instance(rng, n, m, kmax, kmin)
        N0 = nu(v); seen = set()
        for order in itertools.permutations(range(n)):
            Y = tuple(sd(v, order))
            if Y in seen: continue
            seen.add(Y)
            if sum(g is not None for g in Y) != N0: continue
            C['maximum-matching starts'] += 1
            h = hypotheses(v, list(Y), m)
            if h is None: continue
            C['hypotheses hold'] += 1
            X = construct(v, list(Y), *h)
            assert sorted(g for B in X for g in B) == list(range(m))
            assert sum(len([g for g in B if g not in Y]) >= 2 for B in X) <= 1
            if efx0(v, X): C['completion EFX0'] += 1
            else:
                C['COUNTEREXAMPLE'] += 1
                print('COUNTEREXAMPLE', json.dumps({'v': [{str(k): x for k, x in d.items()} for d in v], 'Y': Y, 'X': X}))
    return C

def run_data(paths):
    C = collections.Counter()
    for path in paths:
        d = json.load(gzip.open(path))
        for H in d['hypergraphs']:
            sets = H['sets']; m = 1 + max(g for S in sets for g in S)
            for s in H['starts']:
                v = [dict(zip(S, vals)) for S, vals in zip(sets, s['vals'])]
                C['failing starts'] += 1
                Y = list(s['picks'])
                if any(Y[f] is not None and all(Y[f] not in v[i] for i in range(len(v)) if i != f) for f in range(len(v))):
                    C['with an agent holding a private good'] += 1
                if hypotheses(v, Y, m) is not None:
                    C['LEMMA ABS HYPOTHESES HOLD (would contradict the lemma)'] += 1
    return C

if __name__ == '__main__':
    if sys.argv[1] == 'random':
        opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
        args = [a for a in sys.argv[2:] if not a.startswith('--')]
        C = run_random(int(args[0]), int(args[1]) if len(args) > 1 else 1, int(opt.get('kmax', 4)), int(opt.get('kmin', 2)),
                       int(opt.get('nmax', 6)))
    else:
        C = run_data(sys.argv[2:])
    for k, x in sorted(C.items()): print('  %-58s %d' % (k, x))
    print('RESULT:', 'OK' if not any('COUNTER' in k or 'WOULD' in k.upper() and 'CONTRADICT' in k for k in C) else 'FAILED')
