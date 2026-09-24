"""SAT-free certificate checker, independent of frontier.py. For every core hypergraph in a certificate file:
  1. checks it is a valid connected core (3 distinct goods per agent, every good used, <= 1 private good per agent);
  2. for each stored allocation, decides from the raw EFX0 definition which rankings keep each agent safe, under three
     balanced realizations of a > b > c (they must agree, since EFX0 in a core is ordinal);
  3. checks that every one of the 6^n ranking profiles is covered by some stored allocation;
  4. if the record names one of frontier.py's models, checks that every stored allocation has its shape (C2: all
     bundles <= 2 goods; C3s3: at most one bundle of more than 2 goods, and it has 3; C3: at most one bundle of more
     than 2 goods; G: any). Other labels (e.g. from a construction) impose no shape.
--require-d: also checks that every stored allocation has at most one bundle of more than 2 goods, whatever its label,
so an accepted file certifies conjecture D for its hypergraphs.
Usage: check_certs.py certs.json.gz [--expect n:m:count ...] [--jobs N] [--require-d]
Hypergraphs are checked in parallel (--jobs, default: all CPUs). Earlier versions: archive/v1-python-enumeration/,
archive/v2-certs-without-shape-check/."""
import sys, json, gzip, itertools, collections, os, multiprocessing
import numpy as np
PERMS = list(itertools.permutations(range(3)))
REAL = [(2.0, 1.5, 1.0), (10.0, 9.0, 2.0), (5.0, 3.0, 2.5)]
SHAPE = {'C2': (0, 2), 'C3s3': (1, 3), 'C3': (1, None), 'G': (None, None)}  # (max bundles of > 2 goods, max bundle size)

def fits(shape, X):
    nbig, cap = shape; size = collections.Counter(X).values()
    return (nbig is None or sum(s > 2 for s in size) <= nbig) and (cap is None or max(size) <= cap)

def safe(val, bundles, i):
    own = sum(val.get(g, 0.0) for g in bundles[i])
    for j, B in enumerate(bundles):
        if j != i and len(B) >= 2:
            vs = [val.get(g, 0.0) for g in B]
            if sum(vs) - min(vs) > own + 1e-9: return False
    return True

def valid_core(n, m, sets):
    if len(sets) != n or any(len(set(S)) != 3 or not all(0 <= g < m for g in S) for S in sets): return False
    deg = collections.Counter(g for S in sets for g in S)
    if set(deg) != set(range(m)) or any(sum(deg[g] == 1 for g in S) > 1 for S in sets): return False
    seen, stack = {0}, [0]
    while stack:
        i = stack.pop()
        for j in range(n):
            if j not in seen and set(sets[i]) & set(sets[j]): seen.add(j); stack.append(j)
    return len(seen) == n

def uncovered(rec):
    """Profiles are indexed by an n-dimensional array whose axis i is agent i's ranking (one of the 6 PERMS)."""
    n, m, sets = rec['n'], rec['m'], [tuple(S) for S in rec['sets']]
    axis = lambda i: (1,) * i + (6,) + (1,) * (n - i - 1)
    cov = np.zeros((6,) * n, dtype=bool)
    for X in rec['allocations']:
        if len(X) != m or not all(0 <= o < n for o in X): raise SystemExit("invalid allocation")
        bundles = [[g for g in range(m) if X[g] == j] for j in range(n)]
        c = np.ones((6,) * n, dtype=bool)
        for i, S in enumerate(sets):
            mask = []
            for p in PERMS:
                res = {safe(dict(zip((S[p[0]], S[p[1]], S[p[2]]), r)), bundles, i) for r in REAL}
                if len(res) != 1: raise SystemExit("realizations disagree: ordinality violated")
                mask.append(res.pop())
            c &= np.array(mask).reshape(axis(i))
        cov |= c
    return int((~cov).sum())

def check(r):
    return valid_core(r['n'], r['m'], r['sets']), uncovered(r)

if __name__ == '__main__':
    args = sys.argv[1:]; jobs = os.cpu_count()
    if '--jobs' in args: k = args.index('--jobs'); jobs = int(args[k + 1]); del args[k:k + 2]
    require_d = '--require-d' in args; args = [a for a in args if a != '--require-d']
    recs = json.load(gzip.open(args[0], 'rt'))
    expect = {tuple(map(int, e.split(':')[:2])): int(e.split(':')[2]) for e in args[2:]} if '--expect' in args else {}
    count, models, problems = collections.Counter(), collections.Counter(), 0
    with multiprocessing.Pool(jobs) as pool:
        for r, (valid, u) in zip(recs, pool.imap(check, recs, chunksize=4)):
            count[(r['n'], r['m'])] += 1; md = r.get('mode'); models[md] += 1
            if not valid: print("not a valid connected core:", r['sets']); problems += 1
            if u: print(f"UNCOVERED profiles: {u} for {r['sets']}"); problems += 1
            bad = sum(not fits(SHAPE[md], X) for X in r['allocations']) if md in SHAPE else 0
            if bad: print(f"{bad} allocations outside model {md} for {r['sets']}"); problems += 1
            bad = sum(not fits(SHAPE['C3'], X) for X in r['allocations']) if require_d else 0
            if bad: print(f"{bad} allocations with two bundles of more than 2 goods (not D) for {r['sets']}"); problems += 1
    for k, v in expect.items():
        if count[k] != v: print(f"expected {v} hypergraphs at (n,m)={k}, found {count[k]}"); problems += 1
    print(f"checked {len(recs)} hypergraphs {dict(count)}, models {dict(models)}; problems: {problems}")
    sys.exit(1 if problems else 0)
