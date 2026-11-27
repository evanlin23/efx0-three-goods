"""Exact (SMT) check of Conjecture D1-HJ on the three-agent core (k4/d1.md §6).  Encoding E1.

The core: agents k, z, w; k picks first and takes a (= Y_k); z and w both want a and are unfrozen; k is the only frozen
agent and values a junk good.  Every good is relevant to some agent.  Goods: a = 0, y_z = 1, y_w = 2 (z picks before
w; the order of z and w is the only asymmetry, and both orders are covered by relabelling), junk 3, 4, ....

For every combinatorial structure (which goods each agent values, |R_i| <= 4), the solver looks for positive real
values such that
  - the order (k, z, w) gives the picks (a, y_z, y_w) (ties broken by index, as in k4/sdc);
  - z and w want a, nobody wants y_z or y_w;
  - both canonical chains (k, z), (k, w) have HEAD;
  - the picks have no one-absorber completion (every placement listed and refuted);
  - D1-HJ fails: for each chain (k, u), each head option (u takes a alone, or a plus one junk good g), and each
    inclusion-minimal improving H0 inside (Pi_u - g) & R_k, the resulting state has no S* completion owned by k.
UNSAT for every structure means D1-HJ holds on every three-agent core (all real values, ties included).
A SAT model is printed and re-checked with the raw checker k4/d1/d1lib.py.

    python3 k4/d1/core3_smt.py [max_junk]
"""
import sys, os, itertools, collections, json, time
from fractions import Fraction
import z3
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

K, Z, W = 0, 1, 2
A, YZ, YW = 0, 1, 2


def structures(max_junk=7):
    """yield (R_k, R_z, R_w, junk) up to isomorphism of junk goods (junk goods are distinguished only by their valuers;
    within a type they are interchangeable, so a multiset of types suffices)"""
    types = [t for r in range(1, 4) for t in itertools.combinations((K, Z, W), r)]
    for kyz, kyw, zyw, wyz in itertools.product((0, 1), repeat=4):
        capk = 3 - kyz - kyw; capz = 2 - zyw; capw = 2 - wyz
        def rec(i, counts, ck, cz, cw):
            if i == len(types):
                yield dict(counts); return
            t = types[i]
            for c in range(0, 4):
                nk = ck + c * (K in t); nz = cz + c * (Z in t); nw = cw + c * (W in t)
                if nk > capk or nz > capz or nw > capw: break
                counts[t] = c
                yield from rec(i + 1, counts, nk, nz, nw)
            counts[t] = 0
        for counts in rec(0, {}, 0, 0, 0):
            nj = sum(counts.values())
            if nj == 0 or nj > max_junk: continue
            junk = []; g = 3
            for t in types:
                for _ in range(counts.get(t, 0)): junk.append((g, t)); g += 1
            Rk = {A} | ({YZ} if kyz else set()) | ({YW} if kyw else set()) | {g for g, t in junk if K in t}
            Rz = {A, YZ} | ({YW} if zyw else set()) | {g for g, t in junk if Z in t}
            Rw = {A, YW} | ({YZ} if wyz else set()) | {g for g, t in junk if W in t}
            if not any(K in t for g, t in junk): continue          # k must be dangerous
            if os.environ.get('MC2', '0') == '1':
                Rs = [Rk, Rz, Rw]
                if any(len(r) < 3 for r in Rs): continue           # core agents value 3 or 4 goods
                priv = [sum(1 for g in Rs[i] if all(g not in Rs[j] for j in range(3) if j != i)) for i in range(3)]
                if max(priv) >= 2: continue                         # K4.MC2: no agent with two private goods
            yield [sorted(Rk), sorted(Rz), sorted(Rw)], [g for g, t in junk]


MODE = os.environ.get('MODE', 'HJ')   # HJ: D1-HJ fails; CANON: only canonical chains fail; NONE: no repair constraint


def encode(R, junk):
    n = 3; m = 3 + len(junk)
    v = [{g: z3.Real('v%d_%d' % (i, g)) for g in R[i]} for i in range(n)]
    s = z3.Solver()
    for i in range(n):
        for g in R[i]: s.add(v[i][g] > 0)
    if os.environ.get('MC2', '0') == '1':      # strictly balanced: 2 v_i(g) < v_i(R_i)
        for i in range(n):
            tot = z3.Sum([v[i][g] for g in R[i]])
            for g in R[i]: s.add(2 * v[i][g] < tot)
    STRICT = os.environ.get('STRICT', '0')
    if STRICT in ('1', '2'):            # 1: distinct values per agent; 2: distinct subset sums per agent (generic)
        for i in range(n):
            gs = sorted(R[i])
            if STRICT == '1':
                for g, h in itertools.combinations(gs, 2): s.add(v[i][g] != v[i][h])
            else:
                subs = [S for r in range(1, len(gs) + 1) for S in itertools.combinations(gs, r)]
                for S, T in itertools.combinations(subs, 2):
                    if set(S) & set(T): continue
                    s.add(z3.Sum([v[i][g] for g in S]) != z3.Sum([v[i][g] for g in T]))
    def val(i, S): return z3.Sum([v[i][g] for g in S if g in v[i]]) if any(g in v[i] for g in S) else z3.RealVal(0)
    def better_or_tie_lower(i, g, h):   # i ranks g above h: (v(g), -g) > (v(h), -h)
        return z3.Or(v[i][g] > v[i][h], z3.And(v[i][g] == v[i][h], g < h))
    # picks of the order (k, z, w): each picks its top available relevant good
    for g in R[K]:
        if g != A: s.add(better_or_tie_lower(K, A, g))
    for g in R[Z]:
        if g not in (A, YZ): s.add(better_or_tie_lower(Z, YZ, g))
    for g in R[W]:
        if g not in (A, YZ, YW): s.add(better_or_tie_lower(W, YW, g))
    p = [v[K][A], v[Z][YZ], v[W][YW]]
    # wants: z, w want a; nobody wants y_z, y_w
    s.add(v[Z][A] > p[Z], v[W][A] > p[W])
    if YZ in v[W]: s.add(v[W][YZ] <= p[W])
    if YW in v[Z]: s.add(v[Z][YW] <= p[Z])
    if YZ in v[K]: s.add(v[K][YZ] <= p[K])
    if YW in v[K]: s.add(v[K][YW] <= p[K])
    def threat(i, t, S):
        S = list(S)
        if len(S) < 2: return z3.BoolVal(False)
        return z3.Or([val(i, [x for x in S if x != h]) > t for h in S])
    def efx0(X):
        cl = []
        for j in range(n):
            if len(X[j]) < 2: continue
            for i in range(n):
                if i != j: cl.append(z3.Not(threat(i, val(i, X[i]), X[j])))
        return z3.And(cl) if cl else z3.BoolVal(True)
    J = list(junk)
    # HEAD for both chains
    for u, yu in ((Z, YZ), (W, YW)):
        Pi = J + [yu]
        s.add(threat(u, v[u][A], Pi))
    # hard: no one-absorber completion of the picks
    base = [[A], [YZ], [YW]]
    for o in range(n):
        others = [i for i in range(n) if i != o]
        for r in range(0, len(others) + 1):
            for who in itertools.combinations(others, r):
                for goods in itertools.permutations(J, r):
                    X = [list(b) for b in base]
                    for i, g in zip(who, goods): X[i].append(g)
                    X[o] += [g for g in J if g not in goods]
                    s.add(z3.Not(efx0(X)))
    # D1-HJ fails
    for u, yu, up, yup in (((Z, YZ, W, YW), (W, YW, Z, YZ)) if MODE != 'NONE' else ()):
        Pi = J + [yu]
        for g in [None] + (J if MODE == 'HJ' else []):
            Pi2 = [x for x in Pi if x != g]
            Pk = [x for x in Pi2 if x in v[K]]
            for r in range(1, len(Pk) + 1):
                for H0 in itertools.combinations(Pk, r):
                    minimal = z3.And([val(K, H0) > p[K]] + [val(K, [x for x in H0 if x != h]) <= p[K] for h in H0])
                    Jp = [x for x in Pi2 if x not in H0]
                    comps = []
                    for e in [None] + Jp:
                        X = [None] * 3
                        X[u] = [A] + ([g] if g is not None else [])
                        X[up] = [yup] + ([e] if e is not None else [])
                        X[K] = list(H0) + [x for x in Jp if x != e]
                        comps.append(efx0(X))
                    s.add(z3.Implies(minimal, z3.Not(z3.Or(comps))))
    return s, v


def model_values(m, v, R):
    sets, vals = [], []
    for i in range(3):
        sets.append(list(R[i])); row = []
        for g in R[i]:
            x = m.eval(v[i][g], model_completion=True)
            row.append(Fraction(x.numerator_as_long(), x.denominator_as_long()))
        vals.append(row)
    # scale to integers
    import math
    den = 1
    for row in vals:
        for x in row: den = den * x.denominator // math.gcd(den, x.denominator)
    return sets, [[int(x * den) for x in row] for row in vals]


if __name__ == '__main__':
    maxj = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/d1/core3_smt.py', *sys.argv[1:], flush=True)
    for R, junk in structures(maxj):
        s, v = encode(R, junk)
        r = s.check(); C['structures'] += 1; C[str(r)] += 1
        if r == z3.sat:
            sets, vals = model_values(s.model(), v, R)
            print('SAT', json.dumps((sets, vals)), flush=True)
            from d1lib import Inst, sd_picks, Start, one_absorber
            I = Inst(sets, vals, 3 + len(junk)); Y = sd_picks(I, (0, 1, 2)); S = Start(I, Y)
            print('   raw: picks', Y, 'hard', not one_absorber(I, S.B), 'D', S.D, flush=True)
        if C['structures'] % 50 == 0: print(C['structures'], dict(C), '%.0f s' % (time.time() - t0), flush=True)
    for kk in sorted(C): print(kk, C[kk])
    print('time %.0f s' % (time.time() - t0))
