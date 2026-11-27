"""Does the two-agent Lemma T (kgen/n3.md §9) lift to three agents?  For an order with picker sequence (p1, p2, p3) and a
chosen agent z: among the complete allocations that are OC1(t >= 0)-reachable from the picks (Lemma R, ported from
kgen/oc3.c) and in which every agent other than z is EFX0-satisfied, take one maximizing v_z(X_z).  Is it EFX0?
z = the first picker (the two-agent Lemma T's role), or the last.  Reports the first failures found, k-limited
instances (k = 3, 4, 5) and general ones.

    python3 kgen/lemmaT3.py SEED N MMIN MMAX [kinds]"""
import sys, random, itertools, collections, json
from gen3 import gen
from oc3lib import picks, ORD


def satisfied(v, X, i):
    own = sum(v[i][g] for g in X[i])
    for j in range(3):
        if j != i and len(X[j]) >= 2 and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > own: return False
    return True


def reachable(v, y, X):
    """Lemma R (kgen/n3.md §2) for three agents: OC1 with chains t >= 0 and a one-absorber completion"""
    m = len(v[0]); R = [{g for g in range(m) if v[i][g] > 0} for i in range(3)]
    J = set(range(m)) - {g for g in y if g is not None}
    val = lambda i, S: sum(v[i][g] for g in S)
    vy = lambda i, g: v[i][g] if g is not None else 0
    def absorb(B): return sum(1 for i in range(3) if len(X[i] - B[i]) >= 2) <= 1
    own = [y[i] is None or y[i] in X[i] for i in range(3)]
    pk = [{y[i]} if y[i] is not None else set() for i in range(3)]
    if all(own):
        if absorb(pk): return True
        for x in range(3):
            H0 = X[x] & J & R[x]
            if y[x] is not None and H0:
                B = [set(b) for b in pk]; B[x] = pk[x] | H0
                if absorb(B): return True
    for path in [p for t in (2, 3) for p in itertools.permutations(range(3), t)]:
        t = len(path) - 1
        if any(y[path[i]] is None for i in range(t)): continue
        off = [a for a in range(3) if a not in path]
        if any(not own[a] for a in off): continue
        B = [set(b) for b in pk]; ok = True
        for i in range(1, t + 1):
            xi, xp = path[i], path[i - 1]
            if y[xp] not in X[xi]: ok = False; break
            Hi = X[xi] & J & R[xi]
            if v[xi][y[xp]] + val(xi, Hi) <= vy(xi, y[xi]): ok = False; break
            B[xi] = {y[xp]} | Hi
        if not ok: continue
        x0, xt = path[0], path[-1]
        H0 = X[x0] & (J | ({y[xt]} if y[xt] is not None else set())) & R[x0]
        if val(x0, H0) <= vy(x0, y[x0]): continue
        B[x0] = H0
        if absorb(B): return True
    return False


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); shown = collections.Counter()
    print('$ python3 kgen/lemmaT3.py', *sys.argv[1:], flush=True)
    kinds = sys.argv[5].split(',') if len(sys.argv) > 5 else ['klim:3', 'klim:4', 'klim:5', 'general', 'zeros']
    for t in range(N):
        kind = kinds[t % len(kinds)]; m = rng.randint(lo, hi)
        if kind.startswith('klim'): m = min(m, 3 * int(kind[5:]))
        v = gen(kind, m, rng)
        allX = [[{g for g in range(m) if q[g] == i} for i in range(3)] for q in itertools.product(range(3), repeat=m)]
        for o in ORD:
            y = picks(v, o)
            R_ = [X for X in allX if reachable(v, y, X)]
            if not R_: C['%s: no reachable allocation at all' % kind] += 1; continue
            for role, z in (('first', o[0]), ('last', o[2])):
                F = [X for X in R_ if all(satisfied(v, X, i) for i in range(3) if i != z)]
                C['%s %s: starts' % (kind, role)] += 1
                if not F: C['%s %s: no allocation with the others satisfied' % (kind, role)] += 1; continue
                best = max(sum(v[z][g] for g in X[z]) for X in F)
                arg = [X for X in F if sum(v[z][g] for g in X[z]) == best]
                okk = all(satisfied(v, X, z) for X in arg); C['%s %s: every maximizer EFX0' % (kind, role)] += okk
                C['%s %s: some maximizer EFX0' % (kind, role)] += any(satisfied(v, X, z) for X in arg)
                others = [i for i in o if i != z]
                key2 = lambda X: tuple(sum(v[i][g] for g in X[i]) for i in others)
                b2 = max(key2(X) for X in arg)
                C['%s %s: maximizer, then others lexicographically in picking order, EFX0' % (kind, role)] += all(satisfied(v, X, z) for X in arg if key2(X) == b2)
                key3 = lambda X: -sum(1 for i in others for g in X[i] if v[z][g] == 0)
                b3 = max(key3(X) for X in arg)
                C['%s %s: maximizer, then fewest z-worthless goods with the others, EFX0' % (kind, role)] += all(satisfied(v, X, z) for X in arg if key3(X) == b3)
                if not okk and shown[(kind, role)] < 2:
                    shown[(kind, role)] += 1
                    bad = [X for X in arg if not satisfied(v, X, z)][0]
                    print('LIFT FAILS', kind, role, json.dumps(v), 'order', o, 'picks', y, 'maximizer', [sorted(b) for b in bad], flush=True)
    for k in sorted(C): print(C[k], k)
