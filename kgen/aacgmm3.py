"""The three-agent EFX algorithm of Akrami, Alon, Chaudhury, Garg, Mehlhorn, Mehta (arXiv 2205.07638v2, Section
"EFX Existence beyond Additivity"), implemented for additive non-degenerate values, and the question: is its output an
OC1(t >= 0) completion of the serial-dictatorship picks (Lemma R, kgen/lemmaT3.py's reachable)?

Algorithm (as read in the paper's source):
  PR(v, X): while the partition X is not EFX under the single valuation v, move a good g from a bundle X_j with
    v(X_j - g) > v(X_l) to the v-poorest bundle X_l (Plaut-Roughgarden; min value strictly increases).
  Invariants on a partition (X1, X2, X3): X1, X2 EFX-feasible for agent 1 (A), X3 EFX-feasible for agent 2 or 3.
  Start: PR(v_A) on (M, {}, {}), then agent B takes its favourite bundle as X3.  Potential phi = min(v_A(X1), v_A(X2)).
  Step: if some assignment of the three bundles makes everyone EFX-feasible, stop.  Otherwise (X1 <_A X2), with
    g_i = i's cheapest good of X3:
    case 1, some i in {B, C} has X3 - g_i >_i X1 + g_i: X1' = an inclusion-minimal subset of X1 + g_i beating X1 for A,
      X3' = (X3 - g_i) + the rest; if X1', X2 are not both EFX-feasible for A, run PR(v_A) and let B choose X3.
    case 2: (Y2, Y3) = PR(v_B) on (X1 + g_B, X3 - g_B), C chooses; A takes X2.  If A strongly envies both, PR(v_A) on
      (X2, Y2, Y3) and B chooses; if one, compress it to a minimal subset beating X2 for A, the rest to the other bundle,
      then PR(v_A) if needed.
Non-degeneracy: v'(g_j) = v(g_j) * 2^(m+1) + 2^j (exact integers, distinct subset sums; the paper's Appendix lemma).

    python3 kgen/aacgmm3.py SEED N MMIN MMAX"""
import sys, random, itertools, collections, json
from lemmaT3 import reachable
from oc3lib import picks, ORD


def val(v, S): return sum(v[g] for g in S)


def feasible(v, X, k):
    """bundle X[k] is EFX-feasible for valuation v in partition X (all goods, zeros included)"""
    best = max((val(v, B) - min(v[g] for g in B) for B in X if B), default=0)
    return val(v, X[k]) >= best


def pr(v, X):
    X = [set(B) for B in X]
    while True:
        l = min(range(len(X)), key=lambda k: val(v, X[k]))
        mv = None
        for j in range(len(X)):
            if X[j] and j != l:
                g = min(X[j], key=lambda h: (v[h], h))
                if val(v, X[j]) - v[g] > val(v, X[l]): mv = (j, g); break
        if mv is None: return X
        j, g = mv; X[j].discard(g); X[l].add(g)


def minimal_beating(v, S, target):
    """an inclusion-minimal subset T of S with v(T) > target (S itself beats target)"""
    T = set(S)
    for h in sorted(S, key=lambda h: (v[h], h)):
        if val(v, T - {h}) > target: T.discard(h)
    return T


def efx0(V, X):
    for i in range(3):
        own = val(V[i], X[i])
        for j in range(3):
            if j != i and X[j] and val(V[i], X[j]) - min(V[i][g] for g in X[j]) > own: return False
    return True


def aacgmm(V, roles):
    """roles = (A, B, C): A plays the paper's agent 1, B agent 2, C agent 3.  Returns X indexed by real agent."""
    A, B, C = roles; m = len(V[0]); it = 0
    def choose(P, who):                          # who takes its favourite bundle; it becomes index 2
        k = max(range(3), key=lambda q: val(V[who], P[q])); return [P[q] for q in range(3) if q != k] + [P[k]]
    X = choose(pr(V[A], [set(range(m)), set(), set()]), B)
    phi = None
    while True:
        it += 1; assert it < 10000
        for perm in itertools.permutations(range(3)):           # perm[agent position] = bundle
            if all(feasible(V[a], X, perm[p]) for p, a in enumerate((A, B, C))):
                out = [None] * 3
                for p, a in enumerate((A, B, C)): out[a] = X[perm[p]]
                return out, it
        assert feasible(V[A], X, 0) and feasible(V[A], X, 1) and (feasible(V[B], X, 2) or feasible(V[C], X, 2))
        newphi = min(val(V[A], X[0]), val(V[A], X[1])); assert phi is None or newphi > phi; phi = newphi
        if val(V[A], X[0]) > val(V[A], X[1]): X = [X[1], X[0], X[2]]
        X1, X2, X3 = X
        g = {i: min(X3, key=lambda h: (V[i][h], h)) for i in (B, C)}
        case1 = [i for i in (B, C) if val(V[i], X3 - {g[i]}) > val(V[i], X1 | {g[i]})]
        if case1:
            i = case1[0]; S = X1 | {g[i]}; X1p = minimal_beating(V[A], S, val(V[A], X1))
            Xp = [X1p, set(X2), (X3 - {g[i]}) | (S - X1p)]
            if feasible(V[A], Xp, 0) and feasible(V[A], Xp, 1): X = Xp
            else: X = choose(pr(V[A], Xp), B)
            continue
        Y = pr(V[B], [X1 | {g[B]}, X3 - {g[B]}])
        if val(V[C], Y[0]) > val(V[C], Y[1]): Y = [Y[1], Y[0]]       # C takes Y[1]
        Y2, Y3 = Y; Xp = [X2, Y2, Y3]
        env = [k for k in (1, 2) if Xp[k] and val(V[A], Xp[k]) - min(V[A][h] for h in Xp[k]) > val(V[A], X2)]
        if not env:
            out = [None] * 3; out[A], out[B], out[C] = X2, Y2, Y3; return out, it
        if len(env) == 2: X = choose(pr(V[A], Xp), B); continue
        k = env[0]; o = 3 - k; Yb = minimal_beating(V[A], Xp[k], val(V[A], X2))
        Xpp = [X2, Yb, Xp[o] | (Xp[k] - Yb)]
        if feasible(V[A], Xpp, 0) and feasible(V[A], Xpp, 1): X = Xpp
        else: X = choose(pr(V[A], Xpp), B)


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/aacgmm3.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); kind = ['general', 'ident', 'zeros'][t % 3]
        if kind == 'general': raw = [[rng.randint(1, 99) for _ in range(m)] for _ in range(3)]
        elif kind == 'ident':
            base = [rng.randint(5, 60) for _ in range(m)]; raw = [[max(1, b * 4 + rng.randint(-6, 6)) for b in base] for _ in range(3)]
        else: raw = [[rng.choice([0, 0, rng.randint(1, 99)]) for _ in range(m)] for _ in range(3)]
        V = [[raw[i][j] * 2 ** (m + 1) + 2 ** j for j in range(m)] for i in range(3)]
        outs = {}
        for roles in ORD:
            X, it = aacgmm(V, roles); assert efx0(V, X); outs[roles] = X; C['iterations max'] = max(C['iterations max'], it)
        for o in ORD:
            y = picks(V, o); C[kind + ': starts'] += 1
            C[kind + ': output with roles = order is OC1-reachable'] += reachable(V, y, outs[o])
            C[kind + ': output for some role assignment is OC1-reachable'] += any(reachable(V, y, X) for X in outs.values())
            C[kind + ': picks all kept by the output (roles = order)'] += all(y[i] in outs[o][i] for i in range(3) if y[i] is not None)
            if not any(reachable(V, y, X) for X in outs.values()) and C['shown'] < 3:
                C['shown'] += 1
                print('NO ROLE ASSIGNMENT GIVES OC1', json.dumps(raw), 'order', o, 'picks', y,
                      'outputs', {''.join(map(str, r)): [sorted(b) for b in X] for r, X in outs.items()}, flush=True)
    for k in sorted(C):
        if k != 'shown': print(C[k], k)
