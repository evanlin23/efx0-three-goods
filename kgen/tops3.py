"""The Tops construction of Theorem 2 (kgen/n3.md §9, case 2) at n = 3: keeping every pick is not enough.

Instance family: v_i(g) = 10 for every good, except v_i(i) = 11, so goods 0, 1, 2 are distinct tops and the picks of
every order. With m = 9 there is no EFX0 allocation that keeps all three picks and leaves some agent with at most one
good outside its pick. That is what the shapes "picks" and "t = 0 at one agent" (one absorber) need. So every OC1
completion moves a pick (a t >= 1 chain).
  check 1: kgen/oc3.c's shapes() (which move shapes have an EFX0 completion)
  check 2: plain Python, from the definitions, over all 3^m allocations

    python3 kgen/tops3.py"""
import itertools
from oc3lib import shapes, ORD


def inst(m):
    v = [[10] * m for _ in range(3)]
    for i in range(3): v[i][i] = 11
    return v


def efx0(v, X):
    for i in range(3):
        own = sum(v[i][g] for g in X[i])
        for j in range(3):
            if j != i and any(own < sum(v[i][h] for h in X[j] if h != g) for g in X[j]): return False
    return True


if __name__ == '__main__':
    print('$ python3 kgen/tops3.py')
    for m in (6, 7, 8, 9, 10):
        v = inst(m)
        fam = sorted(set(s[0] for S in shapes(v) for s, a in S))
        keep = 0
        for q in itertools.product(range(3), repeat=m):
            X = [{g for g in range(m) if q[g] == i} for i in range(3)]
            if all(i in X[i] for i in range(3)) and min(len(X[i]) - 1 for i in range(3)) <= 1 and efx0(v, X): keep += 1
        print('m = %2d: shape families with an EFX0 completion (oc3.c, all 6 orders): %s;'
              ' EFX0 allocations keeping all picks with some agent at <= 1 extra good (Python): %d' % (m, fam, keep))
