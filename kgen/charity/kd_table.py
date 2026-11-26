"""The bounds of Theorem CH-KD (kgen/charity.md §8) as a table: for k and d, part 2 gives (k - 2)d - 1 and part 3
gives the largest p with p! <= d^(p-1) (Sivashankar's packing inequality with equal part sizes d, AM-GM); the
theorem's bound is the minimum (and 0 for k <= 2).  Exact integer arithmetic.

    python3 kgen/charity/kd_table.py KMAX DMAX"""
import sys
from math import factorial


def packing(d):
    p = 1
    while factorial(p + 1) <= d ** p:
        p += 1
    return p


if __name__ == '__main__':
    KMAX, DMAX = map(int, sys.argv[1:3])
    print('$ python3 kgen/charity/kd_table.py', KMAX, DMAX)
    print('d: packing bound (largest p with p! <= d^(p-1))  ' + '  '.join('k=%d' % k for k in range(3, KMAX + 1)))
    for d in range(1, DMAX + 1):
        pk = packing(d)
        row = ['%4d' % min(pk, (k - 2) * d - 1) for k in range(3, KMAX + 1)]
        print('d=%-2d packing %2d   ' % (d, pk) + '  '.join(row))
