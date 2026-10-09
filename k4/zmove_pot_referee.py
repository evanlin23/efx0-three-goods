#!/usr/bin/env python3
"""Referee checks of the written proofs of k4/zmove_pot.md (Lemmas Z0, R0, Theorem AR with Lemmas S, S', C0-C3,
Proposition R, the fragility lemma of §4, Lemma S+ and the exposure claim of §5). EVIDENCE tooling, written by the
PR #87 referee from the definitions of k4/c4x.md §1 and k4/dl2.md §4 (Lemma H1); it imports nothing from the repository
and shares no code with k4/zmove_pot.py or k4/suite/model.py.

For every input profile with f >= 1 and omega >= 1 (every state of every key, not only keys with def* > 0):
  - its own enumeration of the valid pre-allocations (bases of at most two goods inside R_i, disjoint, (V1), (V2)), the
    min-frozen states, keys, and the deficit both by Lemma H1 (omega + 2 - max |X| + u_o(X)) and by the raw removal-only
    definition of k4/c4x.md §1 (min |C| - S_o(C)); the two are asserted equal at every state;
  - Lemma Z0 (any f): (a), (b) at every (r', Lambda')-maximal state, and (c): the configurations of the key (enumerated
    from k4/c4min.md §1) that maximize (r', Lambda') are exactly the fillings of the (r', Lambda')-maximal states;
  - Lemma R0: at every state, a robust free agent is not threatened by W_o for any other free o;
  - at f = 1, at every state with def(P) >= 1 satisfying (H_AR): (F1), and every lemma of §4 whose hypotheses hold, with
    the owner and the bundle the lemma names (every admissible A, every choice of c, w, o the lemma allows): the bundle is
    a bundle of the owner in P', safe in P', and |Y| + u'(Y) >= omega + 2 (the certificate the proof gives), and
    def(P') <= 0 by the exact deficit; Lemma S's bound theta_t(J + B_t) <= v_t(g) at every terminal that is not theta-b;
    Proposition R's conclusions where no lemma applies (counted as the residual (E) / (R3));
  - the fragility lemma of §4 wherever its hypotheses hold: the state P* and the bundle it names, def(P*) <= 0;
  - Lemma S+ at every f = 1 state with def(P) >= 1 (any robustness), and the exposure claim of §5 (Lemma H3 of
    k4/hall.md under (U), (U2) only): at every state where every free agent is locally optimal, every free agent is
    exposed by at most one free agent.

usage: python3 k4/zmove_pot_referee.py random SEED COUNT [--n=3,4] [--bias=top|theta|design] [--terms=K] [--time=S]
       python3 k4/zmove_pot_referee.py FILE.jsonl.gz|inst:FILE.json ... [--every=E] [--max=N] [--time=S]"""
import collections, gzip, itertools, json, random, sys, time

CNT = collections.Counter()
EX = {}


def subsets(S, kmax=None):
    S = list(S)
    for k in range(0, (len(S) if kmax is None else min(kmax, len(S))) + 1):
        for c in itertools.combinations(S, k):
            yield frozenset(c)


class Prof:
    def __init__(self, sets, vals, m):
        self.n = len(sets); self.m = m
        self.R = [frozenset(S) for S in sets]
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.M = frozenset(range(m))

    def val(self, i, S): return sum(self.v[i].get(h, 0) for h in S)

    def needs(self, i, B):
        b = self.val(i, B)
        return frozenset(h for h in self.R[i] if h not in B and self.v[i][h] > b)

    def theta(self, i, Z):
        return max(self.val(i, Z - {h}) for h in Z) if Z else None

    def threatens(self, Z, i, B):
        return bool(Z) and self.theta(i, Z) > self.val(i, B)

    def level(self, i, S):
        s = self.val(i, S)
        return sum(1 for T in subsets(self.R[i]) if self.val(i, T) < s)


class State:
    def __init__(self, pr, Bs):
        self.pr = pr; self.B = tuple(Bs)
        self.N = [pr.needs(i, B) for i, B in enumerate(Bs)]
        self.NA = frozenset().union(*self.N)
        used = frozenset().union(*Bs)
        self.J = pr.M - used
        self.F = [i for i, B in enumerate(Bs) if len(B) == 1 and B <= self.NA]
        self.free = [i for i in range(pr.n) if i not in self.F]
        self.S = sum(2 - len(Bs[i]) for i in self.free)

    def valid(self):
        if self.J & self.NA: return False
        return not any(len(B) == 2 and B & self.NA for B in self.B)

    def key(self): return tuple(sorted((i, next(iter(self.B[i]))) for i in self.F))

    def u(self, o, X):
        """frozen agents whose good misses N_o(X) and the needs of the agents other than o"""
        other = frozenset().union(*(self.N[i] for i in range(self.pr.n) if i != o))
        No = self.pr.needs(o, X)
        return sum(1 for x in self.F if not (self.B[x] & (No | other)))

    def safe(self, o, X):
        return not any(self.pr.threatens(X, w, self.B[w]) for w in range(self.pr.n) if w != o)

    def def_h1(self, om):
        best = None
        for o in self.free:
            for K in subsets(self.J):
                X = self.B[o] | K
                if self.safe(o, X):
                    val = len(X) + self.u(o, X)
                    best = val if best is None or val > best else best
        return om + 2 - best

    def def_raw(self):
        """k4/c4x.md §1: |J| - S if <= 0; else min |C| - S_o(C) over free owners o and C in J leaving nobody threatened"""
        if len(self.J) - self.S <= 0: return len(self.J) - self.S
        best = None
        pr = self.pr
        for o in self.free:
            for C in subsets(self.J):
                X = self.B[o] | (self.J - C)
                if not self.safe(o, X): continue
                NAo = pr.needs(o, X).union(*(self.N[i] for i in range(pr.n) if i != o))
                Fo = [i for i in range(pr.n) if i != o and len(self.B[i]) == 1 and self.B[i] <= NAo]
                So = sum(2 - len(self.B[i]) for i in range(pr.n) if i != o and i not in Fo)
                d = len(C) - So
                best = d if best is None or d < best else best
        return best


def analyse(pr):
    opts = [list(subsets(R, 2)) for R in pr.R]
    allP = []

    def rec(i, used, cur):
        if i == pr.n:
            allP.append(tuple(cur)); return
        for B in opts[i]:
            if B & used: continue
            rec(i + 1, used | B, cur + [B])
    rec(0, frozenset(), [])
    V = [st for st in (State(pr, b) for b in allP) if st.valid()]
    f = min(len(st.F) for st in V)
    om = f - (2 * pr.n - pr.m)
    mf = [st for st in V if len(st.F) == f]
    for st in mf: assert len(st.J) - st.S == om, 'omega identity'
    return V, f, om, mf


def U(pr, y, Nm): return pr.R[y] - Nm


def robust(pr, st, y, Nm): return pr.val(y, st.B[y]) >= pr.val(y, U(pr, y, Nm) - st.B[y])


def locopt(pr, st, y):
    pool = (st.B[y] | st.J) & pr.R[y]
    b = pr.val(y, st.B[y])
    return not any(pr.val(y, S) > b for S in subsets(pool, 2))


def admissible(pr, i, A, Nm):
    return len(A) <= 2 and A <= pr.R[i] - Nm and pr.needs(i, A) <= Nm and (A or not (pr.R[i] - Nm))


def note(name, ok, info):
    CNT[name + (': ok' if ok else ': VIOLATED')] += 1
    if not ok:
        EX.setdefault(name, info)
        print('VIOLATION', name, json.dumps(info, default=list), flush=True)


# ---------------------------------------------------------------------------------------------- Lemma Z0 (c)
def configs(pr, st0, Nm):
    """k4/c4min.md §1 at the key of st0: frozen agents on their goods; free agents disjoint pairs of M' = M - Nm whose
    part in U_y is admissible; pool of omega goods"""
    free = st0.free
    Mp = sorted(pr.M - Nm)
    pairs = {y: [frozenset(c) for c in itertools.combinations(Mp, 2)
                 if admissible(pr, y, frozenset(c) & U(pr, y, Nm), Nm)] for y in free}
    out = []

    def rec(j, used, Q):
        if j == len(free):
            out.append(dict(Q)); return
        y = free[j]
        for c in pairs[y]:
            if c & used: continue
            Q[y] = c; rec(j + 1, used | c, Q); del Q[y]
    rec(0, frozenset(), {})
    return out


def check_z0c(pr, sts, Nm, om):
    st0 = sts[0]
    cs = configs(pr, st0, Nm)
    def phi_c(Q):
        r = sum(1 for y in st0.free if pr.val(y, Q[y]) >= pr.val(y, U(pr, y, Nm) - Q[y]))
        return (r, sum(pr.level(y, Q[y] & pr.R[y]) for y in st0.free))
    def phi_s(st):
        return (sum(1 for y in st.free if robust(pr, st, y, Nm)), sum(pr.level(y, st.B[y]) for y in st.free))
    best_c = max(phi_c(Q) for Q in cs)
    best_s = max(phi_s(st) for st in sts)
    note('Z0(c) max over configurations = max over states', best_c == best_s, [best_c, best_s])
    zc = set(tuple(sorted((y, tuple(sorted(Q[y]))) for y in Q)) for Q in cs if phi_c(Q) == best_c)
    built = set()
    for st in sts:
        if phi_s(st) != best_s: continue
        fr = [y for y in st.free]
        need = [2 - len(st.B[y]) for y in fr]
        J = sorted(st.J)

        def rec(j, used, Q):
            if j == len(fr):
                built.add(tuple(sorted(Q.items()))); return
            y = fr[j]
            for c in itertools.combinations([h for h in J if h not in used], need[j]):
                Q[y] = tuple(sorted(st.B[y] | frozenset(c))); rec(j + 1, used | frozenset(c), Q); del Q[y]
        rec(0, frozenset(), {})
    note('Z0(c) Z\'-maxima = fillings of the (r\', Lam\')-maximal states', zc == built, [len(zc), len(built)])


# ---------------------------------------------------------------------------------------------- Theorem AR
def swap(pr, st, x, g, t, A):
    Bs = list(st.B); Bs[t] = frozenset([g]); Bs[x] = A
    st2 = State(pr, Bs)
    return st2


def cert(pr, st2, om, o, Y, need, name, info):
    """Y is a bundle of o in st2, safe in st2, and |Y| + u'(Y) >= need; and def(st2) <= 0 exactly"""
    ok = (st2.valid() and o in st2.free and st2.B[o] <= Y <= st2.B[o] | st2.J and st2.safe(o, Y)
          and len(Y) + st2.u(o, Y) >= need)
    d2 = st2.def_h1(om) if st2.valid() else None
    note(name + ' certificate', ok, info + [sorted(Y), o])
    note(name + ' def(P\') <= 0', d2 is not None and d2 <= 0, info + [d2])
    return ok


def theorem_ar(pr, st, om, x, g, D_, tag):
    Nm = frozenset([g])
    free = st.free
    J = st.J
    Ux = U(pr, x, Nm)
    T = [z for z in free if g in st.N[z]]
    note('Lemma T: a terminal exists', bool(T), tag)
    order = sorted(Ux, key=lambda h: -pr.v[x][h]); p = order[0]
    info = tag + [[sorted(B) for B in st.B]]
    # (F1)
    for o in free:
        W = st.B[o] | J
        note('(F1) W_o threatens x', pr.threatens(W, x, Nm), info + [o])
        note('(F1) W_o meets U_x in an admissible set',
             any(admissible(pr, x, A, Nm) for A in subsets(W & Ux, 2)), info + [o])

    def uu(t):
        return sorted(U(pr, t, Nm), key=lambda h: -pr.v[t][h])

    def thb(t):
        u = uu(t)
        return len(pr.R[t]) == 4 and st.B[t] == frozenset(u[:2]) and u[2] in J and len(J) >= 2

    def adm(G): return [A for A in subsets(G & Ux, 2) if admissible(pr, x, A, Nm)]

    def sigma(t, A):
        st2 = swap(pr, st, x, g, t, A)
        note('(F2) the swap is a state of the key (g, t)', st2.valid() and st2.F == [t] and st2.NA == Nm, info + [t, sorted(A)])
        return st2

    nonthb = [t for t in T if not thb(t)]
    for t in T:
        if thb(t):
            u = uu(t)
            note('theta-b: big-top', pr.v[t][g] > pr.v[t][u[0]] + pr.v[t][u[1]], info + [t])
    # Lemma S at every non-theta-b terminal
    for t in nonthb:
        G = J | st.B[t]
        note('Lemma S: theta_t(J + B_t) <= v_t(g)', pr.theta(t, G) <= pr.v[t][g], info + [t])
        for A in adm(G):
            cert(pr, sigma(t, A), om, x, G, om + 2, 'Lemma S', info + [t, sorted(A)])
    if nonthb:
        return 'S'
    if st.S >= 1:
        for t in T:
            G = J | st.B[t]
            for A in adm(G):
                for c in U(pr, t, Nm) - A:
                    cert(pr, sigma(t, A), om, x, G - {c}, om + 2, "Lemma S'", info + [t, sorted(A), c])
        return "S'"
    note('S = 0 implies omega >= 2', om >= 2 and len(J) == om, info)
    D = J & Ux
    if len(T) == 1:
        t = T[0]; Ut = U(pr, t, Nm); G = J | st.B[t]
        if not Ut <= Ux:
            for A in adm(G):
                for c in Ut - Ux:
                    st2 = sigma(t, A)
                    cert(pr, st2, om, x, G - {c}, om + 2, 'Lemma C0(a)', info + [t, sorted(A), c])
                    note('Lemma C0(a): |Y| = omega + 1 and t counted', len(G - {c}) == om + 1 and st2.u(x, G - {c}) >= 1, info)
            return 'C0a'
        A = frozenset(order[:2])
        note('Lemma C0(b): n >= 3', pr.n >= 3, info)
        for o in free:
            if o == t: continue
            st2 = sigma(t, A)
            cert(pr, st2, om, o, st2.B[o] | st2.J, om + 2, 'Lemma C0(b)', info + [t, o])
        return 'C0b'
    applied = []
    # C1
    for t in T:
        G = J | st.B[t]; Ut = U(pr, t, Nm)
        for A in adm(G):
            if pr.val(x, A) < pr.val(x, Ux - A): continue
            if not (A & Ut) and len(A) != 1: continue
            Cs = [frozenset()] if A & Ut else [frozenset([c]) for c in Ut]
            for o in free:
                if o == t: continue
                for C in Cs:
                    st2 = sigma(t, A)
                    cert(pr, st2, om, o, st2.B[o] | (st2.J - C), om + 2, 'Lemma C1', info + [t, sorted(A), o, sorted(C)])
            applied.append('C1')
    disj = all(not (Ux & U(pr, t, Nm)) for t in T)
    if len(T) == 2 and disj:
        for t, t2 in (T, T[::-1]):
            u2 = uu(t2)
            for A in subsets(D, 2):
                if len(A) != 2 or pr.val(x, A) <= pr.v[x][g]: continue
                for w in U(pr, t, Nm) - {u2[2]}:
                    st2 = sigma(t, A)
                    Y = st2.B[t2] | (st2.J - {w})
                    cert(pr, st2, om, t2, Y, om + 2, "Lemma C2", info + [t, sorted(A), w])
                    note("Lemma C2: |Y| = omega + 1, U_t2 in Y, t counted",
                         len(Y) == om + 1 and U(pr, t2, Nm) <= Y and st2.u(t2, Y) >= 1, info + [t, sorted(A), w])
                applied.append('C2')
    if len(T) >= 3 and disj and p in J and pr.val(x, D - {p}) <= pr.v[x][p]:
        for t in T:
            for t2 in T:
                if t2 == t: continue
                for c in U(pr, t, Nm):
                    st2 = sigma(t, frozenset([p]))
                    cert(pr, st2, om, t2, st2.B[t2] | (st2.J - {c}), om + 2, 'Lemma C3', info + [t, t2, c])
        applied.append('C3')
    if applied:
        return '+'.join(sorted(set(applied)))
    # Proposition R
    note('Prop R: U_x misses every U_t', disj, info)
    note('Prop R: v_x(D) > v_x(g)', pr.val(x, D) > pr.v[x][g], info)
    note('Prop R: |U_x| = 3', len(Ux) == 3, info)
    if len(Ux) == 3:
        q, r = order[1], order[2]
        vx = pr.v[x]
        if len(T) == 2:
            note('Prop R (E)', Ux <= J and vx[p] + vx[q] < vx[g] and vx[p] < vx[q] + vx[r], info)
            EX.setdefault('residual (E)', info)
            return 'E'
        ok = (p not in J and D == frozenset([q, r]) and vx[q] + vx[r] > vx[g]) or (Ux <= J and vx[q] + vx[r] > vx[p])
        note('Prop R (R3)', ok, info)
        EX.setdefault('residual (R3)', info)
        return 'R3'
    return 'R?'


def fragility(pr, st, om, x, g, info):
    """the last lemma of k4/zmove_pot.md §4, wherever its hypotheses hold (S = 0, every terminal theta-b, |T| >= 2,
    U_x disjoint from every U_t, a terminal t with v(u1) > v(u2) + v(u3), e in D with v_x(D - e) <= v_x(g))"""
    Nm = frozenset([g]); J = st.J; Ux = U(pr, x, Nm)
    T = [z for z in st.free if g in st.N[z]]
    if st.S or len(T) < 2: return
    uu = {t: sorted(U(pr, t, Nm), key=lambda h: -pr.v[t][h]) for t in T}
    if not all(len(pr.R[t]) == 4 and st.B[t] == frozenset(uu[t][:2]) and uu[t][2] in J and len(J) >= 2 for t in T): return
    if any(Ux & U(pr, t, Nm) for t in T): return
    D = J & Ux
    for t in T:
        u1, u2, u3 = uu[t]
        if pr.v[t][u1] < pr.v[t][u2] + pr.v[t][u3]: continue
        for e in D:
            if pr.val(x, D - {e}) > pr.v[x][g]: continue
            Bs = list(st.B); Bs[t] = frozenset([u1]); st2 = State(pr, Bs)
            note('fragility lemma: P* is a state of the key', st2.valid() and st2.F == [x], info + [t])
            for t2 in T:
                if t2 == t: continue
                Y = st2.B[t2] | (st2.J - {e})
                ok = len(Y) == om + 2 and st2.B[t2] <= Y <= st2.B[t2] | st2.J and st2.safe(t2, Y)
                note('fragility lemma certificate', ok, info + [t, t2, e])
                note('fragility lemma: def(P*) <= 0', st2.def_h1(om) <= 0, info + [t, t2, e])


def lemma_splus(pr, st, om, x, g, info):
    Nm = frozenset([g]); J = st.J; Ux = U(pr, x, Nm)
    T = [z for z in st.free if g in st.N[z]]
    for t in T:
        if not locopt(pr, st, t): continue
        u = sorted(U(pr, t, Nm), key=lambda h: -pr.v[t][h])
        if len(pr.R[t]) == 4 and st.B[t] == frozenset(u[:2]) and u[2] in J and len(J) >= 2: continue
        W = st.B[t] | J
        if any(pr.threatens(W, w, st.B[w]) for w in st.free if w != t): continue
        As = [A for A in subsets(W & Ux, 2) if admissible(pr, x, A, Nm)]
        note('Lemma S+: an admissible A exists', bool(As), info + [t])
        for A in As:
            st2 = swap(pr, st, x, g, t, A)
            cert(pr, st2, om, x, W, om + 2, 'Lemma S+', info + [t, sorted(A)])


def run(d):
    pr = Prof(d['sets'], d['vals'], d['m'])
    V, f, om, mf = analyse(pr)
    if f < 1 or om < 1: CNT['profiles skipped (f = 0 or omega <= 0)'] += 1; return
    CNT['profiles f=%d' % f] += 1
    keys = collections.defaultdict(list)
    for st in mf: keys[st.key()].append(st)
    D = {}
    for st in mf:
        a, b = st.def_h1(om), st.def_raw()
        if a != b: note('deficit: Lemma H1 = raw removal-only', False, [d, [sorted(B) for B in st.B], a, b])
        D[st.B] = a
    CNT['states (deficit by H1 = raw)'] += len(mf)
    for k, sts in keys.items():
        Nm = frozenset(g for _, g in k)
        CNT['keys f=%d' % f] += 1
        dstar = min(D[st.B] for st in sts)
        if dstar > 0: CNT['keys f=%d with def* > 0' % f] += 1
        phi = {st.B: (sum(1 for y in st.free if robust(pr, st, y, Nm)), sum(pr.level(y, st.B[y]) for y in st.free)) for st in sts}
        best = max(phi.values())
        tag = [d, list(k)]
        for st in sts:
            # Lemma R0, any f: robust free agents are threatened by no W_o
            for y in st.free:
                if not robust(pr, st, y, Nm): continue
                for o in st.free:
                    if o != y:
                        note('Lemma R0', not pr.threatens(st.B[o] | st.J, y, st.B[y]), tag)
            if phi[st.B] == best:
                for y in st.free:
                    if len(st.B[y]) == 1: note('Z0(a)', not (st.J & pr.R[y]), tag)
                    if len(st.B[y]) == 2: note('Z0(b)', locopt(pr, st, y), tag)
                    if len(st.B[y]) == 0: note('Z0(c): empty base => U_y empty', not U(pr, y, Nm), tag)
            # exposure (Lemma H3 under (U), (U2)): every free agent exposed by at most one free agent
            if all(locopt(pr, st, y) for y in st.free):
                for y in st.free:
                    exp = [o for o in st.free if o != y and pr.threatens(st.B[o] | st.J, y, st.B[y])]
                    note('H3 under (U), (U2): exposed by at most one free agent', len(exp) <= 1, tag)
        if len(sts[0].free) <= 3 and len(pr.M - Nm) <= 11:
            check_z0c(pr, sts, Nm, om)
        if f != 1: continue
        (x, g), = k
        for st in sts:
            if D[st.B] < 1: continue
            info = tag + [[sorted(B) for B in st.B], D[st.B]]
            lemma_splus(pr, st, om, x, g, info)
            allrob = all(robust(pr, st, y, Nm) for y in st.free)
            T = [z for z in st.free if g in st.N[z]]
            if not allrob or not all(locopt(pr, st, t) for t in T): continue
            fragility(pr, st, om, x, g, info)      # its setting is Proposition R's, which assumes (H_AR)
            case = theorem_ar(pr, st, om, x, g, D, tag)
            CNT['AR states: case %s%s' % (case, ', def* > 0' if dstar > 0 else '')] += 1


# ---------------------------------------------------------------------------------------------- random profiles
def rand_vals(rng, k, bigtop):
    """k strictly balanced values (top < sum of the others), all subset sums distinct; top first. bigtop: the top
    beats the next two together (4 goods)"""
    while True:
        vs = sorted(rng.sample(range(1, 4 * k + 9), k), reverse=True)
        if not vs[0] < sum(vs[1:]): continue
        if bigtop and not vs[0] > vs[1] + vs[2]: continue
        sums = [sum(c) for r in range(1, k + 1) for c in itertools.combinations(vs, r)]
        if len(sums) == len(set(sums)): return vs


def rand_profile(rng, n, bias):
    """a random profile biased toward many agents with the same top g = 0 and big-top 4-good agents. bias 'theta': every
    agent but at most one has top g, mostly big-top with four goods, omega >= 2 (the S = 0, theta-b cases of §4)"""
    om = rng.choice([1, 2, 2, 3]) if bias != 'theta' else rng.choice([2, 2, 3])
    m = 2 * n - 1 + om
    while True:
        sets, vals = [], []
        ntop = rng.randint(2, n) if bias != 'theta' else rng.choice([n, n - 1])
        for i in range(n):
            k = 4 if rng.random() < (0.8 if bias != 'theta' else 0.9) else 3
            if i < ntop:
                rest = rng.sample(range(1, m), k - 1)
                vs = rand_vals(rng, k, k == 4 and rng.random() < (0.7 if bias != 'theta' else 0.85))
                sets.append([0] + rest); vals.append(vs)
            else:
                S = rng.sample(range(1, m), k)
                vs = rand_vals(rng, k, False); rng.shuffle(vs)
                sets.append(S); vals.append(vs)
        if set().union(*map(set, sets)) == set(range(m)):
            # normalize: sets sorted, values aligned
            out_s, out_v = [], []
            for S, V in zip(sets, vals):
                pr = sorted(zip(S, V)); out_s.append([a for a, _ in pr]); out_v.append([b for _, b in pr])
            return {'sets': out_s, 'vals': out_v, 'm': m}


def vals_for(rng, goods, pred):
    """values for the goods (a list), strictly balanced and strict, with pred(dict good -> value) true"""
    for _ in range(20000):
        vs = rng.sample(range(1, 31), len(goods))
        if not max(vs) < sum(vs) - max(vs): continue
        sums = [sum(c) for r in range(1, len(vs) + 1) for c in itertools.combinations(vs, r)]
        if len(sums) != len(set(sums)): continue
        v = dict(zip(goods, vs))
        if pred(v): return v
    return None


def design_profile(rng, n, terms=None):
    """a profile built around a designed state of §4's case S = 0 (or one robust single-good non-terminal): x = agent 0
    frozen on g = 0, k terminals (big-top with probability 0.85) holding their two best lower goods with the third in
    the junk, robust non-terminals holding pairs; the analysis then runs on every state of the profile"""
    while True:
        om = rng.choice([2, 2, 3]); m = 2 * n - 1 + om
        k = rng.randint(1, n - 1) if terms is None else min(terms, n - 1)
        slot = k < n - 1 and rng.random() < 0.3
        goods = list(range(1, m)); rng.shuffle(goods)
        B = {}
        for i in range(1, n):
            sz = 1 if (slot and i == n - 1) else 2
            B[i] = [goods.pop() for _ in range(sz)]
        J = goods[:]
        sets = {}; vals = {}
        ok = True
        for i in range(1, k + 1):           # terminals
            u3 = rng.choice(J)
            R = [0] + B[i] + [u3]
            bt = rng.random() < 0.85
            def pred(v, i=i, bt=bt, u3=u3, R=R):
                lo = sorted((v[h] for h in R[1:]), reverse=True)
                return (v[0] > max(lo) and v[0] > v[B[i][0]] + v[B[i][1]] and min(v[B[i][0]], v[B[i][1]]) > v[u3]
                        and (not bt or v[0] > lo[0] + lo[1]))
            v = vals_for(rng, R, pred)
            if v is None: ok = False; break
            sets[i] = R; vals[i] = v
        if not ok: continue
        pool = [h for h in range(1, m)]
        Ux = rng.sample(pool, min(rng.choice([2, 3, 3]), len(pool)))
        Rx = [0] + Ux
        v = vals_for(rng, Rx, lambda v: v[0] == max(v.values()))
        if v is None: continue
        sets[0] = Rx; vals[0] = v
        for i in range(k + 1, n):           # robust non-terminals; g possibly relevant but not needed
            cand = [h for h in range(0, m) if h not in B[i]]
            if len(B[i]) == 1:
                ex = [0] + rng.sample([h for h in cand if h != 0], 1)
            else:
                ex = rng.sample(cand, rng.choice([1, 2]))
            R = B[i] + ex
            def pred(v, i=i, R=R):
                b = sum(v[h] for h in B[i])
                Ui = [h for h in R if h != 0]
                needs = [h for h in R if h not in B[i] and v[h] > b]
                return not needs and b >= sum(v[h] for h in Ui if h not in B[i])
            v = vals_for(rng, R, pred)
            if v is None: ok = False; break
            sets[i] = R; vals[i] = v
        if not ok: continue
        if set().union(*(set(sets[i]) for i in sets)) != set(range(m)): continue
        out_s, out_v = [], []
        for i in range(n):
            R = sorted(sets[i]); out_s.append(R); out_v.append([vals[i][h] for h in R])
        return {'sets': out_s, 'vals': out_v, 'm': m}


def read(args):
    for a in args:
        if a.startswith('inst:'):
            fn = a[5:]
            L = json.load(gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))
            for e in L:
                yield {'sets': e['sets'], 'vals': e['vals'], 'm': e.get('m') or 1 + max(map(max, e['sets']))}
        else:
            for line in gzip.open(a, 'rt'):
                r = json.loads(line)
                yield {'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}


def main(argv):
    if not argv: print(__doc__); return
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    args = [a for a in argv if not a.startswith('--')]
    tmax = float(opt.get('time', 1e12)); t0 = time.time()
    print('# command: python3 k4/zmove_pot_referee.py ' + ' '.join(argv), flush=True)
    if args[0] == 'random':
        rng = random.Random(int(args[1])); cnt = int(args[2])
        ns = [int(v) for v in opt.get('n', '3,4').split(',')]
        for j in range(cnt):
            if time.time() - t0 > tmax: CNT['STOPPED at --time'] += 1; break
            bias = opt.get('bias', 'top')
            terms = int(opt['terms']) if 'terms' in opt else None
            d = design_profile(rng, rng.choice(ns), terms) if bias == 'design' else rand_profile(rng, rng.choice(ns), bias)
            CNT['profiles generated'] += 1
            run(d)
    else:
        every = int(opt.get('every', 1)); mx = int(opt.get('max', 10 ** 9)); seen = set(); j = 0
        for d in read(args):
            kk = json.dumps([d['sets'], d['vals'], d['m']])
            if kk in seen: continue
            seen.add(kk); j += 1
            if (j - 1) % every: continue
            if CNT['profiles read'] >= mx or time.time() - t0 > tmax: break
            CNT['profiles read'] += 1
            run(d)
    for k in sorted(CNT): print('%-80s %d' % (k, CNT[k]))
    for k, v in sorted(EX.items()): print('EX %s %s' % (k, json.dumps(v, default=list)[:600]))
    bad = sum(v for k, v in CNT.items() if k.endswith('VIOLATED'))
    print('VIOLATIONS', bad)
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
