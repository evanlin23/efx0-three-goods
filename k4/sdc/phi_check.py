"""Conjecture PHI (k4/sdc.md §20): with strict valuations, every EFX0 allocation maximizing
    Phi(X) = sum_i v_i(F_i(X)),   F_i(X) = agent i's favourite good in its own bundle,
among all EFX0 allocations is SD-consistent: some serial-dictatorship order's picks lie in the bundles (Y_i in X_i).
By Lemma 1 this is (U) + (A).  If PHI holds, SD-C is equivalent to the existence of an EFX0 allocation.
Exhaustive over all n^m allocations (small instances only), raw EFX0 definition.

    python3 k4/sdc/phi_check.py random SEED T n M K     (T random instances, m <= M goods, <= K valued goods per agent)
    python3 k4/sdc/phi_check.py special|screen LIMIT     (instances with n^m <= LIMIT)
    python3 k4/sdc/phi_check.py climb SEED n ROUNDS STEPS K   (maximize gap = best Phi of an SD-inconsistent EFX0
                                                           allocation minus best Phi of an SD-consistent one; >= 0 refutes)"""
import itertools, random, sys, collections


def efx0(val, X, n):
    for i in range(n):
        vi = sum(val[i][g] for g in X[i])
        for j in range(n):
            if i != j and X[j] and sum(val[i][g] for g in X[j]) - min(val[i][g] for g in X[j]) > vi:
                return False
    return True


def fav(v, S):
    S = [g for g in S if v[g] > 0]
    return max(S, key=lambda g: (v[g], -g)) if S else None


def sd_consistent(val, X, n, m):
    for o in itertools.permutations(range(n)):
        left = set(range(m)); ok = True
        for i in o:
            y = fav(val[i], left)
            if y is not None:
                if y not in X[i]: ok = False; break
                left.discard(y)
        if ok: return True
    return False


def Phi(val, X, n):
    return sum(val[i][f] for i in range(n) for f in [fav(val[i], X[i])] if f is not None)


def strict(val):
    return all(len(set(v for v in r if v > 0)) == len([v for v in r if v > 0]) for r in val)


def analyse(val, n, m):
    """(best Phi, [maximizers], gap)"""
    best = None; mx = []; bc = bi = None
    for asg in itertools.product(range(n), repeat=m):
        X = [[g for g in range(m) if asg[g] == i] for i in range(n)]
        if not efx0(val, X, n): continue
        p = Phi(val, X, n); ok = sd_consistent(val, X, n, m)
        if ok: bc = p if bc is None else max(bc, p)
        else: bi = p if bi is None else max(bi, p)
        if best is None or p > best: best, mx = p, [(X, ok)]
        elif p == best: mx.append((X, ok))
    gap = -1000 if bi is None else (1000 if bc is None else bi - bc)
    return best, mx, gap


if __name__ == '__main__':
    mode = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/phi_check.py', *sys.argv[1:], flush=True)
    if mode == 'random':
        seed, T, n, M, K = map(int, sys.argv[2:7]); rng = random.Random(seed)
        for t in range(T):
            m = rng.randint(n, M); val = []
            for i in range(n):
                R = rng.sample(range(m), min(m, rng.randint(2, K))); vs = rng.sample(range(1, 80), len(R))
                val.append([vs[R.index(g)] if g in R else 0 for g in range(m)])
            if any(all(val[i][g] == 0 for i in range(n)) for g in range(m)): continue
            best, mx, gap = analyse(val, n, m); C['instances'] += 1
            if best is None: C['no EFX0 allocation'] += 1; continue
            bad = [X for X, ok in mx if not ok]
            C['every Phi-maximizer SD-consistent'] += not bad
            if bad: print('PHI FAILS', val, bad[0], flush=True)
    elif mode in ('special', 'screen', 'suite'):
        import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import _paths
        from nof_var import SPECIAL
        from sdc_need import instances
        LIM = int(sys.argv[2]); items = SPECIAL if mode == 'special' else instances(mode)
        for name, sets, vals, m in items:
            n = len(sets)
            if n ** m > LIM: C['skipped (n^m > %d)' % LIM] += 1; continue
            val = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(sets[i], vals[i]): val[i][g] = x
            best, mx, gap = analyse(val, n, m); C['tested'] += 1; C['strict' if strict(val) else 'ties'] += 1
            bad = [X for X, ok in mx if not ok]
            C['every Phi-maximizer SD-consistent'] += not bad
            if bad: print('PHI FAILS', name, bad[0], flush=True)
    elif mode == 'climb':
        seed, n, rounds, steps, K = map(int, sys.argv[2:7]); rng = random.Random(seed)
        for r in range(rounds):
            m = rng.randint(n + 1, 9 if n == 2 else 7); val = []
            for i in range(n):
                R = rng.sample(range(m), min(m, rng.randint(2, K)))
                val.append([rng.randint(1, 60) if g in R else 0 for g in range(m)])
            c = analyse(val, n, m)[2] if strict(val) else -2000
            for s in range(steps):
                v2 = [list(x) for x in val]; i = rng.randrange(n); g = rng.randrange(m)
                if rng.random() < 0.8 and v2[i][g] > 0: v2[i][g] = max(1, v2[i][g] + rng.choice([-7, -3, -1, 1, 3, 7]))
                else: v2[i][g] = 0 if v2[i][g] > 0 else rng.randint(1, 60)
                if not strict(v2) or any(all(v2[a][h] == 0 for a in range(n)) for h in range(m)) or \
                        sum(1 for h in range(m) if v2[i][h] > 0) > K: continue
                c2 = analyse(v2, n, m)[2]
                if c2 >= c or rng.random() < 0.03:
                    val, c = v2, c2
                    if c >= 0: print('PHI COUNTEREXAMPLE gap', c, val, flush=True); break
            C['round gap %d' % c if c > -10 else 'round gap <= -10'] += 1
    for k in sorted(C): print(k, C[k])
