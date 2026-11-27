"""Proposition H2 (k4/p3.md section 2.4): on H_t (k4/c4.md section 7, p = 4) and on H3_t (variant A of k4/p3/ht3.py,
p = 3), for every t, the picks of index-order serial dictatorship (= LB4's Phase 1 there) extend to an EFX0 allocation
with two large bundles and no rotation:
  l   gets g_1, u, u', every c_{1,i}, and every b_{j,i} with j >= 2;
  y_1 gets its pick e_1 (g_2, or z if t = 1), every b_{1,i}, and every c_{j,i} with j >= 2;
  every other agent gets exactly its pick.
Checks, for t = 1..T: the picks (index-order serial dictatorship), the allocation, and EFX0 by the raw definition
(k4/p3/p3lib.efx0 and, independently, k4/c4_chain.efx0).
    python3 k4/p3/h2_explicit.py T
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
from p3lib import *
import c4_chain, ht3

def allocation(sets, t, nx):
    """agents: 0 = l, then per gadget nx x's and one y; goods as built by c4_chain.build / ht3.build"""
    n = len(sets); own = {}
    l = 0; ys = [1 + (nx + 1) * j + nx for j in range(t)]
    xs = [[1 + (nx + 1) * j + i for i in range(nx)] for j in range(t)]
    pk = sd(Inst(sets, [[1] * len(S) for S in sets]), range(n)) if False else None
    for j in range(t):
        for x in xs[j]:
            a, b, c, g = sets[x]
            own[a] = x
            own[c if j == 0 else b] = l
            own[b if j == 0 else c] = ys[0]
        own[sets[ys[j]][-1]] = ys[j]          # e_j: y_j's pick
    for g in sets[l]:
        own.setdefault(g, l)                  # g_1, u, u' (z is y_t's pick)
    m = 1 + max(max(S) for S in sets)
    assert len(own) == m and all(g in own for g in range(m))
    return [own[g] for g in range(m)]

if __name__ == '__main__':
    T = int(sys.argv[1]); allok = True
    for t in range(1, T + 1):
        for name, (sets, vals, m), nx in ((f'H_{t}', c4_chain.build(t), 3), (f'H3A_{t}', ht3.build(t, 'A'), 2)):
            I = Inst(sets, vals, m, name)
            pk = sd(I, range(I.n))
            exp = [S[0] for S in sets]; exp[0] = sets[0][0]
            for j in range(t): exp[1 + (nx + 1) * j + nx] = sets[1 + (nx + 1) * j + nx][-1]
            own = allocation(sets, t, nx); X = bundles(I, own)
            keeps = all(pk[i] in X[i] for i in range(I.n))
            big = sum(len(B) > 2 for B in X)
            ok = pk == exp and keeps and efx0(I, X) and c4_chain.efx0(sets, vals, X) and big == 2
            allok &= ok
            print(f'{name}: n = {I.n}, m = {m}, p = {I.p()}; picks as described: {pk == exp}; allocation keeps the picks: '
                  f'{keeps}; EFX0 (two checkers): {efx0(I, X)}, {c4_chain.efx0(sets, vals, X)}; bundles > 2 goods: {big}', flush=True)
    print('all checks pass' if allok else 'SOME CHECK FAILED')
