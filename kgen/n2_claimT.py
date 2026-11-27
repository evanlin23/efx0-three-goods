"""Claim T and Lemma T (kgen/n3.md §9), two agents with distinct top goods t_a != t_b (ties broken by index):
  Claim T: some EFX0 allocation gives t_a to a and t_b to b;
  Lemma T: among allocations with t_a in X_a, t_b in X_b in which b does not strongly envy a, every one maximizing
           v_a(X_a) is EFX0; and one of them gives a no good it values at 0 (so shape A1 of the two-agent OC1).
Brute force over all allocations.  Values: generic, small integers (ties), with zeros.

    python3 kgen/n2_claimT.py SEED N MMAX"""
import sys, random, itertools, collections, json


def sat(v, X, i):
    j = 1 - i; o = [v[i][g] for g in X[j]]
    return len(X[j]) < 2 or sum(v[i][g] for g in X[i]) >= sum(o) - min(o)


if __name__ == '__main__':
    seed, N, hi = map(int, sys.argv[1:4]); rng = random.Random(seed); C = collections.Counter(); ex = []
    print('$ python3 kgen/n2_claimT.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(2, hi); mode = ['generic', 'small', 'zeros'][t % 3]
        if mode == 'generic': v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        elif mode == 'small': v = [[rng.randint(1, 9) for _ in range(m)] for _ in range(2)]
        else:
            v = [[x if rng.random() < 0.7 else 0 for x in rng.sample(range(1, 10 ** 6), m)] for _ in range(2)]
            if not all(v[0][g] or v[1][g] for g in range(m)) or not any(v[0]) or not any(v[1]): continue
        ta = max(range(m), key=lambda g: (v[0][g], -g)); tb = max(range(m), key=lambda g: (v[1][g], -g))
        if ta == tb: continue
        Xs = []
        for q in itertools.product(range(2), repeat=m):
            if q[ta] == 0 and q[tb] == 1: Xs.append([frozenset(g for g in range(m) if q[g] == i) for i in range(2)])
        Fb = [X for X in Xs if sat(v, X, 1)]
        va = lambda X: sum(v[0][g] for g in X[0])
        best = max(va(X) for X in Fb); arg = [X for X in Fb if va(X) == best]
        C['instances (%s)' % mode] += 1
        C['Claim T (%s)' % mode] += any(sat(v, X, 0) for X in Xs)
        C['Lemma T: every maximizer EFX0 (%s)' % mode] += all(sat(v, X, 0) for X in arg)
        C['Lemma T: a maximizer with no a-worthless good in X_a (%s)' % mode] += any(all(v[0][g] > 0 for g in X[0]) for X in arg)
        if not all(sat(v, X, 0) for X in arg) and len(ex) < 3: ex.append(v)
    for k in sorted(C): print(C[k], k)
    for e in ex: print('Lemma T fails', json.dumps(e))
