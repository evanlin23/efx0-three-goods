"""Question W at k = 3 (kgen/charity.md §6): GM4-G with every agent cut to three goods keeps GM4-G's blocking pattern
(sources 0, 1 hold two goods; the pool good 3 is blocked at source 0 by agent 2 and at source 1 by agent 3).  Sample
random values on this hypergraph (and on the S'(2, 3) hypergraph) and test whether the welfare maximum, among those
with the fewest unallocated goods, strands a good (chlib.welfare_max).

    python3 kgen/charity/w_gm4g3.py SEED T"""
import sys, random, json, collections
from chlib import Inst, welfare_max, pool_of, efx0

H = {'gm4g-3': [[0, 2, 6], [1, 4, 5], [2, 3, 5], [3, 4, 6]],
     "S'(2,3)": [[5, 0, 4], [6, 2, 4], [6, 0, 1], [5, 2, 3]]}

if __name__ == '__main__':
    seed, T = map(int, sys.argv[1:3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/charity/w_gm4g3.py', *sys.argv[1:], flush=True)
    base = Inst(4, 7, [{0: 3, 2: 6, 6: 10}, {1: 1, 4: 6, 5: 8}, {2: 3, 3: 6, 5: 8}, {3: 6, 4: 3, 6: 8}])
    W, p, X = welfare_max(base)
    print('gm4g-3 with GM4-G values: welfare max %d, fewest unallocated %d' % (W, p), flush=True)
    for t in range(T):
        name = rng.choice(sorted(H)); sets = H[name]
        I = Inst(4, 7, [{g: rng.randint(1, 12) for g in S} for S in sets])
        W, p, X = welfare_max(I)
        C['%s: welfare maximum leaves %d out' % (name, p)] += 1
        if p:
            assert efx0(I, X)
            print('STRANDED', name, json.dumps({'inst': I.to_json(), 'X': [sorted(B) for B in X],
                                                 'pool': sorted(pool_of(I, X)), 'welfare': W}), flush=True)
    for k in sorted(C):
        print(k, C[k])
