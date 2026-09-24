"""SAT-free certificate checker, independent of frontier.py. For every core hypergraph in a certificate file:
  1. checks it is a valid connected core (3 distinct goods per agent, every good used, <= 1 private good per agent);
  2. for each stored allocation, decides from the raw EFX0 definition which rankings keep each agent safe, under three
     balanced realizations of a > b > c (they must agree, since EFX0 in a core is ordinal);
  3. checks that every one of the 6^n ranking profiles is covered by some stored allocation.
Usage: check_certs.py certs.json.gz [--expect n:m:count ...]"""
import sys, json, gzip, itertools, collections
import numpy as np
PERMS = list(itertools.permutations(range(3)))
REAL = [(2.0, 1.5, 1.0), (10.0, 9.0, 2.0), (5.0, 3.0, 2.5)]

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
    n, m, sets = rec['n'], rec['m'], [tuple(S) for S in rec['sets']]
    idx = np.arange(6 ** n, dtype=np.int64); digits = [(idx // 6 ** i) % 6 for i in range(n)]
    cov = np.zeros(6 ** n, dtype=bool)
    for X in rec['allocations']:
        if len(X) != m or not all(0 <= o < n for o in X): raise SystemExit("invalid allocation")
        bundles = [[g for g in range(m) if X[g] == j] for j in range(n)]
        c = np.ones(6 ** n, dtype=bool)
        for i, S in enumerate(sets):
            mask = []
            for p in PERMS:
                res = {safe(dict(zip((S[p[0]], S[p[1]], S[p[2]]), r)), bundles, i) for r in REAL}
                if len(res) != 1: raise SystemExit("realizations disagree: ordinality violated")
                mask.append(res.pop())
            c &= np.array(mask)[digits[i]]
        cov |= c
    return int((~cov).sum())

if __name__ == '__main__':
    recs = json.load(gzip.open(sys.argv[1], 'rt'))
    expect = {tuple(map(int, e.split(':')[:2])): int(e.split(':')[2]) for e in sys.argv[3:]} if '--expect' in sys.argv else {}
    count, problems = collections.Counter(), 0
    for r in recs:
        count[(r['n'], r['m'])] += 1
        if not valid_core(r['n'], r['m'], r['sets']): print("not a valid connected core:", r['sets']); problems += 1
        u = uncovered(r)
        if u: print(f"UNCOVERED profiles: {u} for {r['sets']}"); problems += 1
    for k, v in expect.items():
        if count[k] != v: print(f"expected {v} hypergraphs at (n,m)={k}, found {count[k]}"); problems += 1
    print(f"checked {len(recs)} hypergraphs {dict(count)}; problems: {problems}"); sys.exit(1 if problems else 0)
