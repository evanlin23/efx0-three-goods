"""Brute-force check of the welfare maxima of GM4-G, GM4-G cut to three goods per agent, GM4-E and S'(2, 3) (kgen/charity.md §6,
attempts/kgen-charity-welfare-complete.md): enumerate all (n + 1)^m partial allocations, keep the EFX0 ones (raw
definition, refute_pm.efx0), and report the largest total value, the (value vector, unallocated count) pairs attaining
it, and the largest total of a complete EFX0 allocation.  Standalone: no SAT.

    python3 kgen/charity/w_brute.py"""
import itertools, collections
from refute_pm import build, value, efx0

GM4G = [{0: 3, 2: 6, 5: 2, 6: 10}, {1: 1, 4: 6, 5: 8, 6: 4}, {2: 3, 3: 6, 5: 8, 6: 4}, {3: 6, 4: 3, 5: 4, 6: 8}]
GM4G3 = [{0: 3, 2: 6, 6: 10}, {1: 1, 4: 6, 5: 8}, {2: 3, 3: 6, 5: 8}, {3: 6, 4: 3, 6: 8}]
GM4E = [{0: 3, 2: 10, 4: 6, 6: 2}, {1: 3, 3: 4, 5: 8, 6: 2}, {2: 4, 3: 2, 6: 3}, {4: 2, 5: 4, 6: 3}]

if __name__ == '__main__':
    print('$ python3 kgen/charity/w_brute.py')
    sp = build(2, 3)
    for name, vals, m in (('GM4-G', GM4G, 7), ('GM4-G cut to three goods (k = 3)', GM4G3, 7), ('GM4-E', GM4E, 7),
                          ("S'(2, 3)", sp[0], sp[2])):
        n = len(vals); byw = collections.defaultdict(set)
        for asg in itertools.product(range(n + 1), repeat=m):
            Y = [set(g for g in range(m) if asg[g] == a) for a in range(n)]
            if efx0(vals, Y):
                vv = tuple(value(vals, a, Y[a]) for a in range(n))
                byw[sum(vv)].add((vv, sum(1 for x in asg if x == n)))
        W = max(byw)
        Wc = max(w for w in byw if any(p == 0 for _, p in byw[w]))
        print('%s: largest total %d, attained by (values, unallocated) %s; fewest unallocated there %d; largest '
              'total of a complete EFX0 allocation %d' % (name, W, sorted(byw[W]), min(p for _, p in byw[W]), Wc),
              flush=True)
