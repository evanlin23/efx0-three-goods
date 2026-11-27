"""Brute-force check of the leximin maxima of GM4-E, GM4-G and the k = 3 cut of GM4-G (kgen/charity.md §6): all
(n + 1)^m partial allocations, raw EFX0 (refute_pm.efx0); the leximin-largest sorted value vector and the fewest
unallocated goods attaining it.  No SAT.

    python3 kgen/charity/lex_brute.py"""
import itertools
from refute_pm import value, efx0
from w_brute import GM4G, GM4G3, GM4E

if __name__ == '__main__':
    print('$ python3 kgen/charity/lex_brute.py')
    for name, vals in (('GM4-E', GM4E), ('GM4-G', GM4G), ('GM4-G cut to three goods (k = 3)', GM4G3)):
        n, m = len(vals), 7; best = {}
        for asg in itertools.product(range(n + 1), repeat=m):
            Y = [set(g for g in range(m) if asg[g] == a) for a in range(n)]
            if efx0(vals, Y):
                vec = tuple(sorted(value(vals, a, Y[a]) for a in range(n)))
                p = sum(1 for x in asg if x == n)
                best[vec] = min(p, best.get(vec, m))
        top = max(best)
        comp = max(v for v, p in best.items() if p == 0)
        print('%s: leximin maximum %s with fewest unallocated %d; leximin-best complete EFX0 vector %s' % (
            name, top, best[top], comp), flush=True)
