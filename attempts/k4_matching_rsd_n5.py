"""Iterated reduction with the lift condition at the step (RSD, Conjecture RSD-IND) fails at n = 5, k = 4
(attempts/k4-matching-rsd-lstar.md).  Self-contained: raw definitions only; it imports nothing from k4/.

Instances: two of compute/k4-oc1max-cert's sampled n = 5 two-move starts (chunk 5_pure_s5o0; list 5_pure, m = 10 idx
419 and m = 11 idx 447).  For each, by brute force:
  1. the picks are SD picks, every agent picks, and no assignment of the junk at the picks is EFX0;
  2. no RSD sequence repairs it.  A sequence is any number of reduction steps:
     - a canonical chain from an agent dangerous in the current instance (each later agent wants its predecessor's
       single good and takes it);
     - its head k takes any improving T inside junk + the end's good;
     - (L*): T threatens no other present agent at its value after the chain;
     - k and T are deleted, and the rest must be a perfect SD outcome of the smaller instance;
     The sequence ends in any assignment of the remaining junk to present agents (deleted agents receive nothing),
     EFX0 in the full instance.  This is broader than the one-absorber completion of k4/matching/rsd.py.
  3. without (L*) at the steps (deferred to the final EFX0 test) two steps do repair it;
  4. the two steps' chains are vertex-disjoint and both are official moves of the start, so one round of two
     simultaneous moves also repairs it.

    python3 attempts/k4_matching_rsd_n5.py"""
import itertools

CASES = {
    '5_pure m=10 idx 419': dict(sets=[[0, 2, 6, 7], [1, 4, 8, 9], [3, 5, 8, 9], [4, 5, 7, 9], [6, 7, 8, 9]],
                                vals=[[6, 3, 10, 8], [4, 8, 2, 3], [2, 8, 4, 3], [6, 7, 5, 3], [10, 7, 2, 6]],
                                picks=[6, 4, 5, 9, 7]),
    '5_pure m=11 idx 447': dict(sets=[[0, 2, 5, 8], [1, 6, 7, 8], [3, 6, 9, 10], [4, 7, 9, 10], [5, 8, 9, 10]],
                                vals=[[3, 4, 8, 6], [1, 6, 8, 4], [2, 10, 6, 3], [2, 8, 3, 4], [10, 8, 3, 6]],
                                picks=[5, 1, 6, 7, 8]),
}


class Inst:
    def __init__(self, sets, vals):
        self.n = len(sets); self.m = 1 + max(max(s) for s in sets)
        self.v = [dict(zip(s, x)) for s, x in zip(sets, vals)]

    def V(self, i, S): return sum(self.v[i].get(g, 0) for g in S)

    def threat(self, i, S, t): return bool(S) and self.V(i, S) - min(self.v[i].get(g, 0) for g in S) > t

    def efx0(self, X):
        return not any(self.threat(i, X[j], self.V(i, X[i])) for i in range(self.n) for j in range(self.n) if j != i)

    def sd(self, order, goods):
        taken = set(); Y = {}
        for i in order:
            av = [g for g in self.v[i] if g in goods and g not in taken]
            if av: g = max(av, key=lambda h: (self.v[i][h], -h)); Y[i] = g; taken.add(g)
        return Y


def completes(I, B, alive):
    """Some assignment of the junk to present agents (any number each) is EFX0 in I."""
    J = [g for g in range(I.m) if all(g not in b for b in B)]
    for lab in itertools.product(alive, repeat=len(J)):
        X = [list(b) for b in B]
        for g, a in zip(J, lab): X[a].append(g)
        if I.efx0(X): return X
    return None


def steps(I, B, alive, goods, lstar):
    J = [g for g in goods if all(g not in B[i] for i in alive)]
    wants = lambda i, g: g not in B[i] and I.v[i].get(g, 0) > I.V(i, B[i])
    D = [k for k in alive if len(B[k]) == 1 and any(i != k and wants(i, B[k][0]) for i in alive)
         and any(g in I.v[k] for g in J)]
    for k in D:
        chains = []

        def ext(P):
            for w in alive:
                if w not in P and len(B[w]) == 1 and wants(w, B[P[-1]][0]): chains.append(P + [w]); ext(P + [w])
        ext([k])
        for P in chains:
            pool = [g for g in J + list(B[P[-1]]) if g in I.v[k]]
            for r in range(1, len(pool) + 1):
                for T in itertools.combinations(pool, r):
                    if I.V(k, T) <= I.V(k, B[k]): continue
                    nb = [list(b) for b in B]; nb[k] = list(T)
                    for a in range(1, len(P)): nb[P[a]] = list(B[P[a - 1]])
                    if lstar and any(I.threat(i, list(T), I.V(i, nb[i])) for i in alive if i != k): continue
                    al2 = [a for a in alive if a != k]; g2 = goods - set(T)
                    if any(len(nb[i]) != 1 for i in al2): continue
                    tgt = {i: nb[i][0] for i in al2}
                    if not any(I.sd(o, g2) == tgt for o in itertools.permutations(al2)): continue
                    yield k, list(T), P, nb, al2, g2


def rsd(I, B, alive, goods, lstar, depth, seq):
    X = completes(I, B, alive)
    if X is not None: return seq, X
    if depth == 0: return None
    for k, T, P, nb, al2, g2 in steps(I, B, alive, goods, lstar):
        r = rsd(I, nb, al2, g2, lstar, depth - 1, seq + [(k, T, P)])
        if r is not None: return r
    return None


if __name__ == '__main__':
    print('$ python3 attempts/k4_matching_rsd_n5.py')
    for name, c in CASES.items():
        I = Inst(c['sets'], c['vals']); n = I.n; allg = set(range(I.m)); B = [[g] for g in c['picks']]
        orders = [o for o in itertools.permutations(range(n)) if [I.sd(o, allg).get(i) for i in range(n)] == c['picks']]
        print('==', name, '| picks', c['picks'], 'from', len(orders), 'orders; junk',
              [g for g in range(I.m) if all(g not in b for b in B)])
        assert orders and completes(I, B, list(range(n))) is None
        print('1. no completion at the picks: True')
        r = rsd(I, B, list(range(n)), allg, True, n, [])
        print('2. an RSD sequence with (L*) at every step, any depth:', r)
        r2 = rsd(I, B, list(range(n)), allg, False, n, [])
        print('3. with (L*) deferred:', r2)
        (k1, T1, P1), (k2, T2, P2) = r2[0]
        print('4. the two chains', P1, P2, 'vertex-disjoint:', not set(P1) & set(P2))
        assert r is None and r2 is not None and len(r2[0]) == 2 and not set(P1) & set(P2)
        # the second chain is already a step at the picks (the moves commute)
        assert any(k == k2 and sorted(T) == sorted(T2) and P == P2 for k, T, P, *_ in steps(I, B, list(range(n)), allg, False))
        print('   the second chain is also a move at the picks: True')
    print('RSD with (L*) at the step refuted at n = 5, k = 4; deferred, it repairs both')
