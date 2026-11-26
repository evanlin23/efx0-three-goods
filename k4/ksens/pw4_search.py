"""Structured search for OC1 failures at k = 4 in the design space of PW (k4/ksens.md §5): f frozen agents x_j, each
valuing its pick p_j (20) and a 3-subset P_j of a pool D (|D| = d), every pair of P_j worth more than 20; W wanters,
each valuing a random nonempty subset of the p's (at most 3, so k <= 4) above its own good q; optionally E extra
agents valuing random goods (up to 4).  Test OC1 and OC from the natural order (x's, wanters, extras) and from R random
orders.

    python3 k4/ksens/pw4_search.py SEED T [R]"""
import sys, json, random, collections, time
import _paths
import ocsat


def make(rng):
    f = rng.randint(2, 4); W = rng.randint(1, 3); d = rng.randint(3, 5); E = rng.choice([0, 0, 1])
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + d)); nxt = f + W + d
    sets, vals = [], []
    for j in range(f):
        pool = sorted(rng.sample(D, 3))
        sets.append([j] + pool); vals.append([20] + rng.sample(range(11, 20), 3))
    for i in range(W):
        ps = rng.sample(P, rng.randint(1, min(3, f)))
        sets.append(ps + [Q[i]]); vals.append(rng.sample(range(3, 15), len(ps)) + [rng.randint(1, 2)])
    for e in range(E):
        S = rng.sample(range(nxt + 1), rng.randint(2, 4))
        sets.append(S); vals.append(rng.sample(range(1, 25), len(S)))
    used = sorted(set(g for s in sets for g in s)); ren = {g: k for k, g in enumerate(used)}
    return [[ren[g] for g in s] for s in sets], vals, len(used)


if __name__ == '__main__':
    seed, T = int(sys.argv[1]), int(sys.argv[2]); R = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/ksens/pw4_search.py', *sys.argv[1:], flush=True)
    for t in range(T):
        sets, vals, m = make(rng); n = len(sets)
        if max(len(s) for s in sets) > 4: continue
        orders = [tuple(range(n))] + [tuple(rng.sample(range(n), n)) for _ in range(R)]
        O = ocsat.OC(sets, vals, m); C['instances'] += 1
        for Y, o in ocsat.starts(sets, vals, m, orders).items():
            b = ocsat.bases_of(Y, n); C['starts'] += 1
            if O.holds(b, chain='none', A=1): continue
            C['starts needing a chain'] += 1
            ok1 = O.holds(b, chain='need', A=1)
            if not ok1:
                okf = O.holds(b, chain='none') or O.holds(b, chain='need')
                C['OC1 FAILS'] += 1; C['OC fails'] += not okf
                print('OC1 FAILS', json.dumps((sets, vals)), 'order', o, 'picks', Y, 'OC', okf, flush=True)
        O.close()
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
