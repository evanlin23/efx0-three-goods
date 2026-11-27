"""Cross-check of kgen/opb_n4.py's EFX0 predicate (kgen/n3.md §14.1): on every allocation of the three n = 4
instances, it must equal EFX0 straight from the definition (remove every good of the other bundle, including goods
worth 0 to the envier). Ordinary EFX (remove only positively valued goods) is counted for contrast.

    python3 kgen/opb_n4_xcheck.py"""
import itertools
from opb_n4 import INST, picks, efx0


def efx0_def(v, X):
    n = len(v)
    for i in range(n):
        own = sum(v[i][h] for h in X[i])
        for j in range(n):
            if j != i:
                for g in X[j]:
                    if own < sum(v[i][h] for h in X[j] if h != g): return False
    return True


def efx_pos(v, X):
    n = len(v)
    for i in range(n):
        own = sum(v[i][h] for h in X[i])
        for j in range(n):
            if j != i:
                for g in X[j]:
                    if v[i][g] > 0 and own < sum(v[i][h] for h in X[j] if h != g): return False
    return True


if __name__ == '__main__':
    print('$ python3 kgen/opb_n4_xcheck.py')
    for v, o in INST:
        m = len(v[0]); a = c = 0
        for q in itertools.product(range(4), repeat=m):
            X = [{g for g in range(m) if q[g] == i} for i in range(4)]
            e1 = efx0(v, X); assert e1 == efx0_def(v, X)
            a += e1; c += efx_pos(v, X)
        print('m = %d, order %s, picks %s: EFX0 allocations %d (opb_n4.efx0 = definition on all %d allocations); ordinary EFX %d'
              % (m, o, picks(v, o), a, 4 ** m, c))
