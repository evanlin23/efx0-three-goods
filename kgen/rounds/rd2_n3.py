"""RD² at n = 3, every k (kgen/rounds.md §6.1): which MD EFX0 allocations are reachable by at most two rounds of
vertex-disjoint improving chains (verify_k4zero.one_round, zeros allowed: H inside relevant goods, rings, t = 0
additions) followed by a one-absorber completion?  For every maximum-matching SD start of random n = 3 instances
(k = number of valued goods per agent, zeros elsewhere; or all positive), compare
  MD    the complete EFX0 allocations that value-dominate the picks;
  R2    the complete EFX0 allocations that extend a state reachable in <= 2 rounds, with <= 1 agent receiving >= 2
        goods outside its base (R2 is inside MD, since rounds only raise values).
Reports per start whether R2 is non-empty (RD² holds) and whether R2 = MD, and for MD allocations outside R2 their
pick-graph shape.
    python3 kgen/rounds/rd2_n3.py COUNT SEED MMIN MMAX KMIN KMAX"""
import sys, os, json, random, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import verify_k4zero as VZ
import rndlib


def max_matching(V):
    n, m = len(V), len(V[0]); best = 0
    for perm in itertools.permutations(range(m), n):
        best = max(best, sum(1 for a in range(n) if V[a][perm[a]] > 0))
        if best == n: return n
    return best


def states2(V, b0):
    S1 = VZ.one_round(V, b0, False); S2 = set(S1)
    for s in S1: S2 |= VZ.one_round(V, list(s), False)
    return S2


def extends(X, s):
    n = len(X)
    if not all(set(s[i]) <= set(X[i]) for i in range(n)): return False
    return sum(1 for i in range(n) if len(set(X[i]) - set(s[i])) >= 2) <= 1


def shape(o, y):
    n = len(y); f = [o[y[a]] for a in range(n)]; indeg = [0] * n
    for a in range(n): indeg[f[a]] += 1
    return tuple(sorted(indeg)), 'perm' if sorted(indeg) == [1] * n else 'non-perm'


if __name__ == '__main__':
    cnt, seed, mmin, mmax, kmin, kmax = map(int, sys.argv[1:7]); rng = random.Random(seed); n = 3
    C = collections.Counter(); ex = []; t0 = time.time()
    print('$ python3 kgen/rounds/rd2_n3.py', *sys.argv[1:], flush=True)
    for t in range(cnt):
        m = rng.randint(mmin, mmax); k = rng.randint(kmin, min(kmax, m))
        V = []
        for i in range(n):
            S = rng.sample(range(m), k); V.append([rng.randint(1, 60) if g in S else 0 for g in range(m)])
        if any(all(V[i][g] == 0 for i in range(n)) for g in range(m)): continue
        nu = max_matching(V); alls, _ = rndlib.list_efx(V); seen = set()
        for order in itertools.permutations(range(n)):
            y = tuple(VZ.sd(V, order))
            if y in seen: continue
            seen.add(y)
            if sum(1 for g in y if g is not None) < nu: continue
            p = [V[a][y[a]] if y[a] is not None else 0 for a in range(n)]
            md = [o for o in alls if all(sum(V[a][g] for g in range(m) if o[g] == a) >= p[a] for a in range(n))]
            b0 = [frozenset([g]) if g is not None else frozenset() for g in y]
            S = states2(V, b0)
            r2 = [o for o in md if any(extends([[g for g in range(m) if o[g] == i] for i in range(n)], s) for s in S)]
            C['starts'] += 1; C[('k', k, 'RD2 holds' if r2 else 'RD2 FAILS')] += 1
            if not md: C['starts without MD'] += 1
            if md and not r2:
                C['RD2 FAILS WITH MD'] += 1; print('RD2 FAILS', json.dumps(V), order, y, flush=True)
            C[('MD allocations', 'reachable in 2 rounds')] += len(r2); C[('MD allocations', 'NOT reachable')] += len(md) - len(r2)
            if None not in y:
                for o in md:
                    if o not in r2:
                        C[('unreachable MD shape',) + shape(o, y)] += 1
                        if len(ex) < 5: ex.append({'V': V, 'order': order, 'picks': y, 'X': [[g for g in range(m) if o[g] == i] for i in range(n)]})
    for k_ in sorted(C, key=str): print(k_, C[k_])
    for e in ex: print('UNREACHABLE MD', json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
