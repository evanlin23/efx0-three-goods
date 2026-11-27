"""Lemma T (conjectured, kgen/n3.md §9): two agents with distinct top goods t_a, t_b.  Among the allocations with
t_a in X_a and t_b in X_b in which b does not strongly envy a, every one maximizing v_a(X_a) is EFX0.  A proof by
local improvement needs: from every such allocation in which a strongly envies b, some exchange keeps b satisfied and
raises v_a(X_a).  This script tests which exchange types always provide one:
  add:   move one good h of b's bundle (not t_b) to a;
  swap:  exchange one good h of b's bundle (not t_b) with one good x of a's bundle (not t_a);
  bulk:  exchange the non-top parts entirely; bulk-1: the same keeping one of b's goods with b.
Brute force over all allocations; values generic, small integers, or with zeros.

    python3 kgen/n2_lemmaT.py SEED N MMIN MMAX"""
import sys, random, itertools, collections, json


def sat(v, X, i):
    j = 1 - i; o = [v[i][g] for g in X[j]]
    return len(X[j]) < 2 or sum(v[i][g] for g in X[i]) >= sum(o) - min(o)


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = {}
    print('$ python3 kgen/n2_lemmaT.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(2, hi); mode = t % 3
        if mode == 0: v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        elif mode == 1: v = [[rng.randint(1, 9) for _ in range(m)] for _ in range(2)]
        else:
            v = [[x if rng.random() < 0.7 else 0 for x in rng.sample(range(1, 10 ** 6), m)] for _ in range(2)]
            if not all(v[0][g] or v[1][g] for g in range(m)) or not any(v[0]) or not any(v[1]): continue
        ta = max(range(m), key=lambda g: (v[0][g], -g)); tb = max(range(m), key=lambda g: (v[1][g], -g))
        if ta == tb: continue
        mode_s = ['generic', 'small', 'zeros'][mode]
        va = lambda X: sum(v[0][g] for g in X[0])
        Xs = []
        for q in itertools.product(range(2), repeat=m):
            if q[ta] != 0 or q[tb] != 1: continue
            Xs.append([frozenset(g for g in range(m) if q[g] == i) for i in range(2)])
        Fb = [X for X in Xs if sat(v, X, 1)]
        C['instances (%s)' % mode_s] += 1
        best = max(va(X) for X in Fb)
        C['maximizers EFX0 (%s)' % mode_s] += all(sat(v, X, 0) for X in Fb if va(X) == best)
        for X in Fb:
            if sat(v, X, 0): continue
            C['states: b satisfied, a strongly envies (%s)' % mode_s] += 1
            A, B = X; Bt = B - {tb}; At = A - {ta}
            def good(Y): return sat(v, Y, 1) and va(Y) > va(X)
            res = {}
            res['add'] = any(good([A | {h}, B - {h}]) for h in Bt)
            res['swap'] = any(good([(A - {x}) | {h}, (B - {h}) | {x}]) for h in Bt for x in At)
            res['bulk'] = good([At | {ta} | Bt, frozenset({tb}) | At]) if True else False
            res['bulk'] = good([frozenset({ta}) | Bt, frozenset({tb}) | At])
            res['bulk-1'] = any(good([frozenset({ta}) | (Bt - {h}), frozenset({tb, h}) | At]) for h in Bt)
            for k, r in res.items(): C['%s (%s)' % (k, mode_s)] += r
            C['add or swap (%s)' % mode_s] += res['add'] or res['swap']
            C['any of them (%s)' % mode_s] += any(res.values())
            if not any(res.values()) and mode_s not in ex: ex[mode_s] = (v, [sorted(A), sorted(B)])
    for k in sorted(C): print(C[k], k)
    for k, e in ex.items(): print('no simple improvement', k, json.dumps(e))
