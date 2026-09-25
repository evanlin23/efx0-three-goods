"""Independent brute-force check of small k = 4 claims (second implementation for UNSAT-type claims, AGENTS.md §5).
No SAT, no order types, no search4.py: explicit integer values, every allocation (n^m), the raw EFX₀ definition
    v_i(X_i) >= v_i(X_j minus {h})   for all agents i != j and every good h in X_j (goods worth 0 to i included).
For each instance prints: number of EFX₀ allocations; the fewest bundles with > 2 and with > 3 goods among them;
the smallest largest bundle; and, among EFX₀ allocations with at most one bundle of > 2 goods, the smallest size of
that bundle. Instances: k4/small_claims.json (list of {name, sets, values}; values[i] lists agent i's integer values
on sets[i] in order).  Usage: verify_small.py [file]"""
import itertools, json, os, sys

def efx0(bundles, vals):
    n = len(bundles)
    for i in range(n):
        own = sum(vals[i].get(g, 0) for g in bundles[i])
        for j in range(n):
            if j == i: continue
            tot = sum(vals[i].get(g, 0) for g in bundles[j])
            for h in bundles[j]:
                if own < tot - vals[i].get(h, 0): return False
    return True

def analyse(sets, values):
    n, m = len(sets), 1 + max(g for S in sets for g in S)
    vals = [dict(zip(S, v)) for S, v in zip(sets, values)]
    count, best = 0, {'big2': None, 'big3': None, 'maxsize': None, 'D2_large': None}
    for owner in itertools.product(range(n), repeat=m):
        bundles = [[g for g in range(m) if owner[g] == j] for j in range(n)]
        if not efx0(bundles, vals): continue
        count += 1
        sizes = sorted((len(B) for B in bundles), reverse=True)
        cand = {'big2': sum(s > 2 for s in sizes), 'big3': sum(s > 3 for s in sizes), 'maxsize': sizes[0],
                'D2_large': sizes[0] if sizes[1] <= 2 else None}
        for k, v in cand.items():
            if v is not None and (best[k] is None or v < best[k]): best[k] = v
    return count, best

if __name__ == '__main__':
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'small_claims.json')
    for inst in json.load(open(path)):
        count, best = analyse(inst['sets'], inst['values'])
        print(f"{inst['name']}: sets={inst['sets']} values={inst['values']}: {count} EFX0 allocations; fewest bundles "
              f"with >2 goods {best['big2']}, with >3 goods {best['big3']}; smallest largest bundle {best['maxsize']}; "
              f"smallest large bundle with <=1 bundle of >2 goods: {best['D2_large']}", flush=True)
