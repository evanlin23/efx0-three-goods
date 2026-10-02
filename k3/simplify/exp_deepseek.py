"""The greedy-plus-cleanup algorithm proposed by DeepSeek (pasted by the user): serial dictatorship in index order,
then each leftover good goes to the first agent that values it (else to the last agent). Checked against raw EFX0."""
import sys, os, collections
sys.path.insert(0, os.path.dirname(__file__))
from k3s import efx0
from test_k3s import gen_small
from lbx import core_profiles

def deepseek(n, m, v):
    rk = [sorted(v[i], key=lambda g: (-v[i][g], g)) for i in range(n)]
    free = set(range(m)); X = [None] * m
    for i in range(n):                                   # step 2
        g = next((g for g in rk[i] if g in free), None)
        if g is not None: X[g] = i; free.discard(g)
    for h in sorted(free):                               # step 4
        X[h] = next((i for i in range(n) if h in v[i]), n - 1)
    return X

def bundles(n, m, X): return [sorted(g for g in range(m) if X[g] == i) for i in range(n)]

if __name__ == '__main__':
    for rank, m in [([(0, 1, 2), (0, 1, 2)], 3), ([(0, 1, 2), (0, 1, 2)], 4)]:
        n = len(rank); v = [dict(zip(r, (3, 2, 2) if m == 4 else (4, 3, 2))) for r in rank]
        X = deepseek(n, m, v); print("instance", rank, "m =", m, "values", v, "->", bundles(n, m, X), "EFX0:", efx0(n, m, v, X))
    for n, m in [(2, 3), (2, 4), (3, 5), (3, 6), (4, 6)]:
        tot = bad = 0
        for _, _, rank in gen_small(n, m):
            v = [dict(zip(r, (4, 3, 2))) for r in rank]; tot += 1; bad += not efx0(n, m, v, deepseek(n, m, v))
        print(f"every ranking profile n={n} m={m}: {bad} of {tot} outputs are not EFX0")
    tot = bad = 0
    for n, m, rank in core_profiles(5):
        v = [dict(zip(r, (4, 3, 2))) for r in rank]; tot += 1; bad += not efx0(n, m, v, deepseek(n, m, v))
    print(f"every profile of every core n <= 5: {bad} of {tot} outputs are not EFX0")
