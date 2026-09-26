"""Replay for attempts/k3-owner-test-no-shared-good.md: LB+'s owner test without the shared good is wrong.

Runs algorithm K3ALG (k3/k3algo.py, `fast`) on the smallest failing instance found, once with the exact owner test
and once with the naive test |E_r| <= S - cap(r) (`naive_owner_test=True`). It prints the owner-test state and checks
both outputs against the raw EFX0 definition; for the naive output it prints a violated inequality.
With --search, it repeats the random search that found the instance.

Usage: python3 attempts/k3_owner_test.py [--search [N] [SEED]]
"""
import sys, os, random, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k3'))
from k3algo import fast, raw_efx0, raw_efx0_naive, random_core, random_hard

# agent -> {good: value}; good 4 is valued by nobody
V = [{2: 5, 6: 4, 5: 2}, {0: 3, 5: 3, 6: 2}, {0: 3, 1: 3, 7: 2}, {3: 2, 1: 2, 0: 2}]
N_AG, M_GD = 4, 8

def violation(n, m, v, X):
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in range(m) if X[g] == i)
        for j in range(n):
            if j == i: continue
            B = [g for g in range(m) if X[g] == j]
            for g in B:
                rest = [h for h in B if h != g]
                if sum(v[i].get(h, 0) for h in rest) > own:
                    return i, j, g, own, sum(v[i].get(h, 0) for h in rest), B
    return None

def replay():
    for naive in (False, True):
        X, info = fast(N_AG, M_GD, V, naive_owner_test=naive)
        name = 'naive test' if naive else 'exact test'
        print(f"{name}: branch {info['branch']}; order {info['order']}, picks {info['picks']}, junk {info['junk']}, "
              f"r = {info['r']}, exposed E_r = {info['E']}, free slots S - cap(r) = {info['free_slots']}, "
              f"hitSet = {info['H']}")
        bundles = {j: [g for g in range(M_GD) if X[g] == j] for j in range(N_AG)}
        ok = raw_efx0(N_AG, M_GD, V, X) and raw_efx0_naive(N_AG, M_GD, V, X)
        print(f"  allocation (owner of each good) {X}, bundles {bundles}: raw EFX0 {ok}")
        w = violation(N_AG, M_GD, V, X)
        if w:
            i, j, g, own, other, B = w
            print(f"  agent {i} values its bundle at {own} but agent {j}'s bundle {B} without good {g} at {other}")
        assert ok == (not naive), "unexpected outcome"
    print("replay: the exact test gives an EFX0 allocation; the naive test does not")

def search(N, seed):
    rng = random.Random(seed); cnt = collections.Counter(); best = None
    for t in range(N):
        n = rng.randint(3, 4); m = rng.randint(3, 2 * n + 1)
        v = random_hard(n, m, rng) if t % 2 else random_core(n, m, rng)
        X, info = fast(n, m, v)
        if 'E' not in info or not (len(info['E']) > info['free_slots'] >= len(info['H'])):
            continue                                     # only the runs where the shared good decides the test
        Xn, infon = fast(n, m, v, naive_owner_test=True)
        ok = raw_efx0(n, m, v, Xn)
        cnt[(infon['branch'], ok)] += 1
        if not ok and (best is None or (n, m) < best[0]): best = ((n, m), v)
    print(f"search: {N} random instances with n in 3..4 (seed {seed}); runs where the shared good decides the exact "
          f"test, by the naive variant's (branch, raw EFX0): {dict(cnt)}; smallest failure {best}")

if __name__ == '__main__':
    if '--search' in sys.argv:
        rest = [a for a in sys.argv[1:] if a != '--search']
        search(int(rest[0]) if rest else 3000000, int(rest[1]) if len(rest) > 1 else 3)
    else:
        replay()
