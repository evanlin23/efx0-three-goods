"""Lemma T (kgen/n3.md §9): canonical improving exchanges.  States X = (A, B) with t_a in A, t_b in B, b not strongly
envying A, a strongly envying B.  Candidates (rho = v_a/v_b, v_b = 0 counts as infinite; ties by index):
  C1 add the good g* of B - t_b with the largest rho (a-positive goods only);
  C2 swap g* with the good x* of A - t_a with the smallest rho;
  C3 bulk-1: a takes B - {t_b, h} plus t_a, b takes A - t_a plus t_b, h, where h = the a-cheapest good of B - t_b;
  C3' bulk-1 with h = the b-cheapest good of B - t_b.
An exchange works if b still does not strongly envy a and v_a(A) rises.  Which canonical combination always works?

    python3 kgen/n2_canon.py SEED N MMAX"""
import sys, random, itertools, collections, json


def sat(v, X, i):
    j = 1 - i; o = [v[i][g] for g in X[j]]
    return len(X[j]) < 2 or sum(v[i][g] for g in X[i]) >= sum(o) - min(o)


if __name__ == '__main__':
    seed, N, hi = map(int, sys.argv[1:4]); rng = random.Random(seed); C = collections.Counter(); ex = {}
    print('$ python3 kgen/n2_canon.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(3, hi); mode = ['generic', 'small', 'zeros'][t % 3]
        if mode == 'generic': v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        elif mode == 'small': v = [[rng.randint(1, 9) for _ in range(m)] for _ in range(2)]
        else:
            v = [[x if rng.random() < 0.7 else 0 for x in rng.sample(range(1, 10 ** 6), m)] for _ in range(2)]
            if not all(v[0][g] or v[1][g] for g in range(m)) or not any(v[0]) or not any(v[1]): continue
        ta = max(range(m), key=lambda g: (v[0][g], -g)); tb = max(range(m), key=lambda g: (v[1][g], -g))
        if ta == tb: continue
        rho = lambda g: (v[0][g] / v[1][g]) if v[1][g] > 0 else float('inf')
        va = lambda X: sum(v[0][g] for g in X[0])
        for q in itertools.product(range(2), repeat=m):
            if q[ta] != 0 or q[tb] != 1: continue
            X = [frozenset(g for g in range(m) if q[g] == i) for i in range(2)]
            if not sat(v, X, 1) or sat(v, X, 0): continue
            A, B = X; Bt = sorted(B - {tb}); At = sorted(A - {ta})
            good = lambda Y: sat(v, Y, 1) and va(Y) > va(X)
            C['states (%s)' % mode] += 1
            r = {}
            pos = [g for g in Bt if v[0][g] > 0]
            gs = max(pos, key=lambda g: (rho(g), -g)) if pos else None
            r['C1'] = gs is not None and good([A | {gs}, B - {gs}])
            if gs is not None and At:
                xs = min(At, key=lambda g: (rho(g), g)); r['C2'] = good([(A - {xs}) | {gs}, (B - {gs}) | {xs}])
            else: r['C2'] = False
            if Bt:
                h = min(Bt, key=lambda g: (v[0][g], g)); r['C3'] = good([frozenset({ta}) | (frozenset(Bt) - {h}), frozenset({tb, h}) | frozenset(At)])
                h2 = min(Bt, key=lambda g: (v[1][g], g)); r["C3'"] = good([frozenset({ta}) | (frozenset(Bt) - {h2}), frozenset({tb, h2}) | frozenset(At)])
            else: r['C3'] = r["C3'"] = False
            for k, x in r.items(): C['%s (%s)' % (k, mode)] += x
            for combo in ['C1|C2', 'C1|C3', 'C2|C3', 'C1|C2|C3', "C1|C3'", "C1|C2|C3'", "C1|C2|C3|C3'"]:
                ok = any(r[c] for c in combo.split('|')); C['%s (%s)' % (combo, mode)] += ok
                if not ok and (combo, mode) not in ex: ex[(combo, mode)] = (v, [sorted(A), sorted(B)])
    for k in sorted(C): print(C[k], k)
    for k, e in ex.items(): print('uncovered', k, json.dumps(e))
