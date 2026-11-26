"""The n = 4 counterexamples to OC1 (attempts/kgen-n4-oc1.md) seen through "one pick per bundle" (kgen/n3.md §14).
For each failing order: the EFX0 allocations with exactly one pick per bundle, the permutation sigma (agent i holds
the pick of agent sigma(i)), its cycle type, whether every non-trivial cycle is an improving ring (each agent values
its new pick plus its unpicked goods above its own pick), and how many fixed agents hold two or more goods besides
their pick.  A permutation with c non-trivial cycles is c disjoint rings, i.e. c chains.

    python3 kgen/opb_n4.py"""
import itertools, collections

INST = [([[34, 0, 0, 0, 38, 35, 37, 33], [0, 10, 5, 0, 0, 4, 2, 0], [0, 2, 0, 0, 3, 0, 1, 0], [52, 54, 53, 4, 0, 0, 0, 51]], (0, 3, 1, 2)),
        ([[0, 155, 1, 0, 0, 155, 0], [0, 75, 2, 74, 0, 74, 77], [0, 0, 0, 2, 133, 0, 134], [1, 4, 0, 2, 0, 0, 0]], (0, 2, 1, 3))]


def picks(v, order):
    left = set(range(len(v[0]))); y = [None] * len(v)
    for i in order:
        av = [g for g in left if v[i][g] > 0]
        if av:
            g = max(av, key=lambda h: (v[i][h], -h)); y[i] = g; left.discard(g)
    return y


def efx0(v, X):
    n = len(v)
    for i in range(n):
        own = sum(v[i][g] for g in X[i])
        for j in range(n):
            if j != i and X[j] and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > own: return False
    return True


def cycles(sig):
    seen, out = set(), []
    for s in range(len(sig)):
        if s in seen: continue
        c = [s]; seen.add(s); t = sig[s]
        while t != s: c.append(t); seen.add(t); t = sig[t]
        out.append(c)
    return out


if __name__ == '__main__':
    print('$ python3 kgen/opb_n4.py')
    for v, o in INST:
        n, m = len(v), len(v[0]); y = picks(v, o); P = set(y); pos = {g: i for i, g in enumerate(y)}
        J = set(range(m)) - P
        C = collections.Counter(); ex = {}
        for q in itertools.product(range(n), repeat=m):
            X = [{g for g in range(m) if q[g] == i} for i in range(n)]
            if not efx0(v, X): continue
            C['EFX0 allocations'] += 1
            if not all(len(B & P) == 1 for B in X): continue
            sig = [pos[next(iter(X[i] & P))] for i in range(n)]
            cyc = cycles(sig); nontriv = [c for c in cyc if len(c) > 1]
            gains = all(v[i][y[sig[i]]] + sum(v[i][g] for g in X[i] & J if v[i][g] > 0) > v[i][y[i]] for c in nontriv for i in c)
            fixed_big = sum(1 for c in cyc if len(c) == 1 for i in c if len(X[i] - {y[i]}) >= 2)
            zero_out = sum(1 for c in nontriv for i in c if any(v[i][g] == 0 for g in X[i] - P))
            typ = '+'.join(str(len(c)) for c in sorted(cyc, key=len, reverse=True))
            key = 'one pick per bundle, cycle type %s, rings improving: %s, fixed agents with 2+ extra goods: %d' % (typ, gains, fixed_big)
            C[key] += 1; ex.setdefault(key, [sorted(b) for b in X])
        print('instance', v, 'order', o, 'picks', y)
        for k in sorted(C): print('  %5d  %s' % (C[k], k), '  e.g.', ex.get(k, ''))
