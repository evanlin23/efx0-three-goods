#!/usr/bin/env python3
"""DL2 repair classification (workstream proof/k4-dl2-k1; k4/dl2.md, k4/strategy.md §3 "Next steps" step 2).

For every min-frozen P in the space 𝒫 of k4/c4x.md §1 with removal-only deficit def(P) > 0, record
  * the obstruction at P: the best owners o (free agents attaining def(P) in Lemma H1 of k4/hall.md §1:
    def(P) = omega + 2 - max(|X| + u_o(X)) over free o and safe X, B_o ⊆ X ⊆ W_o = B_o ∪ J), an optimal X and its
    removed set C = J \\ X (a minimum hitting set of o's threat hypergraph in the Lemma H1 sense), and for every agent x
    exposed w.r.t. o (W_o threatens x holding B_x) its class:
      free x:   e1 / e2 / e3 (the exact shapes of Lemma H3), or fU (x violates (U): at most one base good and a junk
                good of R_x), fU2 (x violates (U2): a better pair in B_x ∪ (R_x ∩ J)), fO (none of these);
      frozen x: G / G1 / L (Lemma H7, with the plain G test and the chain-end test of k4/gap.md §0), or O (none);
      a frozen x exposed w.r.t. two or more free agents is also tagged '2' (the double threat of Lemma D,
      k4/c4min_reduce.md §3);
  * the minimal repairs: every min-frozen P' with def(P') < def(P) at the least distance k(P) (number of agents whose
    base changes), each with a type string (which agents change, their roles at P, how their bases change).
Everything is computed with k4/suite/model.py (the suite's own transcription of k4/c4x.md §1); the deficit of every
min-frozen P is recomputed here from Lemma H1 and asserted equal to model.Inst.deficit.

usage:
  python3 k4/dl2_classify.py suite [--out=FILE]                     every suite instance with omega >= 1, n <= 6
  python3 k4/dl2_classify.py catalog FILE [--every=E] [--max=N] [--jobs=J] [--out=FILE]
  python3 k4/dl2_classify.py one '{"sets": ..., "vals": ...}'        one profile, verbose
Output: one JSON line per def > 0 state (gzip if FILE ends in .gz); the table is made by k4/dl2_table.py."""
import gzip, itertools, json, os, sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask

INF = 10 ** 9


# ------------------------------------------------------------------ basic objects of a pre-allocation
class PA:
    """a pre-allocation P (bases Bs) of instance I with its needs, junk, frozen agents and slots"""

    def __init__(self, I, Bs):
        self.I, self.Bs, n = I, tuple(Bs), I.n
        self.N = [I.needs(i, Bs[i]) for i in range(n)]
        NA = 0
        for x in self.N: NA |= x
        self.NA = NA
        used = 0
        for B in Bs: used |= B
        self.J = I.ALL & ~used
        self.frozen = [pc(Bs[i]) == 1 and bool(Bs[i] & NA) for i in range(n)]
        self.free = [i for i in range(n) if not self.frozen[i]]
        self.S = sum(0 if self.frozen[i] else 2 - pc(Bs[i]) for i in range(n))
        self.bv = [I.val(i, Bs[i]) for i in range(n)]

    def safe(self, o, X):
        I = self.I
        return not any(I.threat(x, X, self.bv[x]) for x in range(I.n) if x != o)

    def u(self, o, X):
        """agents frozen in P that are not frozen once o's needs are taken from X (Lemma H1)"""
        I = self.I
        NA2 = I.needs(o, X)
        for j in range(I.n):
            if j != o: NA2 |= self.N[j]
        return sum(1 for j in range(I.n) if j != o and self.frozen[j] and not (self.Bs[j] & NA2))

    def owner_best(self, o):
        """max over safe X (B_o ⊆ X ⊆ B_o ∪ J) of |X| + u_o(X), and the optimal X's (maximal by inclusion first)"""
        Jl = list(bits(self.J)); B = self.Bs[o]
        best, arg = -1, []
        for k in range(len(Jl), -1, -1):
            for K in itertools.combinations(Jl, k):
                X = B | mask(K)
                if not self.safe(o, X): continue
                val = pc(X) + self.u(o, X)
                if val > best: best, arg = val, [X]
                elif val == best: arg.append(X)
        return best, arg

    def deficit(self):
        """(def, {o: (best, [X...])}); def = omega + 2 - max(|X| + u) by Lemma H1 (INF if no free agent)"""
        omega = pc(self.J) - self.S
        if omega <= 0: return omega, {}
        res = {o: self.owner_best(o) for o in self.free}
        if not res: return INF, res
        mx = max(b for b, _ in res.values())
        return omega + 2 - mx, res

    def W(self, o): return self.Bs[o] | self.J


# ------------------------------------------------------------------ classes of exposures
def sorted_goods(I, i):
    return sorted(I.sets[i], key=lambda g: -I.v[i][g])


def chain_ends(P, x):
    """free agents reached from frozen x along need edges (y -> z when B_y = {g}, g ∈ N_z) through frozen agents"""
    I = P.I; seen = {x}; stack = [x]; ends = set()
    while stack:
        y = stack.pop()
        if pc(P.Bs[y]) != 1: continue
        for z in range(I.n):
            if z in seen or not (P.N[z] & P.Bs[y]): continue
            seen.add(z)
            if P.frozen[z]: stack.append(z)
            else: ends.add(z)
    return ends


def bigtop(I, x):
    if len(I.sets[x]) != 4: return False
    a, b, c, d = [I.v[x][g] for g in sorted_goods(I, x)]
    return a > b + c


def violates_U(P, x):
    """(U) / (U2) of Lemma H2 for a free agent x: 'fU', 'fU2' or None"""
    I = P.I; B = P.Bs[x]; RJ = I.R[x] & P.J
    if pc(B) <= 1:
        return 'fU' if RJ else None
    v = P.bv[x]
    for A in itertools.combinations(list(bits(B | RJ)), 2):
        if I.val(x, mask(A)) > v: return 'fU2'
    return None


def exposure_class(P, o, x):
    """class of the exposure of x w.r.t. owner o (W_o threatens x holding B_x)"""
    I = P.I; B = P.Bs[x]; Bo = P.Bs[o]; J = P.J; R = I.R[x]
    if not P.frozen[x]:
        if pc(B) == 1 and not (R & J) and pc(Bo) == 2 and not (Bo & ~(R & ~B)):
            return 'e1'
        if len(I.sets[x]) == 4 and pc(B) == 2:
            a, b, c, d = sorted_goods(I, x)
            va = I.v[x]
            if B == mask([b, c]) and (Bo >> a) & 1 and (J >> d) & 1 and va[a] + va[d] > va[b] + va[c]:
                return 'e2'
            if not (R & J) and (R & ~B) == Bo:
                return 'e3'
        return violates_U(P, x) or 'fO'
    g = next(bits(B)); vg = I.v[x][g]
    RJ = R & J
    if pc(RJ) >= 2 and I.val(x, RJ) > vg:
        return 'G'
    ce = chain_ends(P, x)
    if o in ce:
        a = sorted_goods(I, x)[0]
        if bigtop(I, x) and g == a and not (R & ~(1 << a) & ~(J | Bo)):
            return 'G1'
        return 'O'
    if I.val(x, R & J) <= vg:
        return 'L'
    return 'O'


def labels(P, o, x):
    """least number of junk goods whose removal from W_o protects x, and whether x is unhittable (only by keeping
    at most two goods, i.e. |X| <= 2)"""
    I = P.I; W = P.W(o); Jl = list(bits(P.J)); Bo = P.Bs[o]
    for k in range(len(Jl) + 1):
        for K in itertools.combinations(Jl, k):
            X = W & ~mask(K)
            if not I.threat(x, X, P.bv[x]):
                return k, pc(X) <= 2
    return None, True


# ------------------------------------------------------------------ the profile
def roles(P, o, exposed):
    """role letter of each agent at P w.r.t. owner o"""
    I = P.I; out = []
    for i in range(I.n):
        if i == o: out.append('o')
        elif P.frozen[i]: out.append('X' if i in exposed else 'F')
        elif i in exposed: out.append('x')
        elif P.N[i] & P.NA: out.append('n')      # a free needer (terminal) of a frozen good
        else: out.append('-')
    return out


def change(P, P2, i, other):
    """how agent i's base changes from P to P2: e.g. 'f>f:+J-J^' ; other = the set of other changed agents"""
    B, B2 = P.Bs[i], P2.Bs[i]
    add, drop = B2 & ~B, B & ~B2
    src = ''
    for g in bits(add):
        if P.J >> g & 1: src += '+J'
        elif any(P.Bs[j] >> g & 1 for j in other): src += '+T'
        else: src += '+?'
    for g in bits(drop):
        if P2.J >> g & 1: src += '-J'
        elif any(P2.Bs[j] >> g & 1 for j in other): src += '-T'
        else: src += '-?'
    st = ('F' if P.frozen[i] else 'f') + '>' + ('F' if P2.frozen[i] else 'f')
    v, v2 = P.bv[i], P2.bv[i]
    arrow = '^' if v2 > v else ('v' if v2 < v else '=')
    return st + ':' + (src or '0') + arrow


def repair_type(P, P2, o, exposed):
    ch = [i for i in range(P.I.n) if P.Bs[i] != P2.Bs[i]]
    rl = roles(P, o, exposed)
    parts = []
    for i in ch:
        oth = [j for j in ch if j != i]
        parts.append(rl[i] + '[' + change(P, P2, i, oth) + ']')
    for i in range(P.I.n):          # agents whose base is unchanged but whose frozen status changes
        if i not in ch and P.frozen[i] != P2.frozen[i]:
            parts.append(rl[i] + '[' + ('F>f' if P.frozen[i] else 'f>F') + ':same base]')
    return ' '.join(sorted(parts))


def best_owners(res):
    if not res: return []
    mx = max(b for b, _ in res.values())
    return sorted(o for o, (b, _) in res.items() if b == mx)


def repair_kind(P, P2, res2):
    """coarse kind of a repair P -> P2 (res2: the owner table of P2):
    R1:release  one free agent y changes; some best owner o' != y of P2 has an optimal bundle holding a good y gave up
    R1:unblock  one free agent y changes; some best owner o' != y of P2, none of whose optimal bundles holds such a good
    R1:owner    one free agent y changes and only y is a best owner of P2
    R1:need-transfer  one agent changes and the needed set changes (an unchanged agent freezes, another unfreezes)
    R2:role-swap      two agents change, one unfreezes and the other freezes (/needer: it needed the other's good;
                      /J: the unfrozen agent's new base is junk only, /T: it takes a good of the other)
    R2:two-free       two free agents change, the needed set is unchanged
    Rk:...            otherwise, the sorted status changes of the changed agents (/nt: the needed set changes)"""
    n = P.I.n
    ch = [i for i in range(n) if P.Bs[i] != P2.Bs[i]]
    k = len(ch)
    nt = P2.NA != P.NA
    if k == 1:
        y = ch[0]
        if nt: return 'R1:need-transfer'
        b2 = best_owners(res2)
        rel = P.Bs[y] & ~P2.Bs[y]
        others = [o for o in b2 if o != y]
        if any(X & rel for o in others for X in res2[o][1]): return 'R1:release'
        if others: return 'R1:unblock'
        return 'R1:owner'
    st = sorted(('F' if P.frozen[i] else 'f') + '>' + ('F' if P2.frozen[i] else 'f') for i in ch)
    if k == 2:
        if st == ['F>f', 'f>F']:
            x = next(i for i in ch if P.frozen[i]); z = next(i for i in ch if not P.frozen[i])
            sub = '/needer' if P.N[z] & P.Bs[x] else '/other'
            sub += '/T' if P2.Bs[x] & P.Bs[z] else '/J'
            return 'R2:role-swap' + sub + ('/nt' if nt else '')
        if st == ['f>f', 'f>f']:
            return 'R2:two-free' + ('/nt' if nt else '')
    return 'R%d:' % k + ','.join(st) + ('/nt' if nt else '')


KIND_ORDER = ['R1:release', 'R1:unblock', 'R1:owner', 'R1:need-transfer']


def primary_kind(kinds):
    for k in KIND_ORDER:
        if k in kinds: return k
    return sorted(kinds)[0] if kinds else None


# ------------------------------------------------------------------ the lemmas of k4/dl2.md, checked on every state
def rebases(I, P, y):
    """Lemma 1: the bases B' != B_y with B' ⊆ (B_y ∪ J) ∩ R_y, |B'| <= 2, N_y(B') ⊆ 𝒩"""
    pool = list(bits((P.Bs[y] | P.J) & I.R[y]))
    out = []
    for k in range(3):
        for c in itertools.combinations(pool, k):
            B = mask(c)
            if B != P.Bs[y] and not (I.needs(y, B) & ~P.NA): out.append(B)
    return out


def counted(P, o, X):
    """the frozen agents counted in u_o(X)"""
    I = P.I
    NA2 = I.needs(o, X)
    for j in range(I.n):
        if j != o: NA2 |= P.N[j]
    return [j for j in range(I.n) if j != o and P.frozen[j] and not (P.Bs[j] & NA2)]


def max_ext(P2, o, X):
    """the largest |K| with K ⊆ W'_o \\ X and X ∪ K safe in P2"""
    rest = list(bits(P2.W(o) & ~X))
    for k in range(len(rest), 0, -1):
        for K in itertools.combinations(rest, k):
            if P2.safe(o, X | mask(K)): return k
    return 0


def lemma_checks(I, P, Bs, PAs, D, OWN):
    """which lemmas of k4/dl2.md apply at P (def(P) > 0); every conclusion is asserted against the exact deficits.
    L2: extension (Lemma 2) at a best owner o and an optimal X; L2o: Lemma 2 at another free agent o and one of its
    optimal X (the gain must exceed Val(P) - Val_o(P)); L3: owner re-base (Lemma 3);
    C4: release (Corollary 4, hypotheses (i)-(iii)); C4s: its structural form (q valued by nobody outside {o, y}, and
    X ⊄ R_z for every z outside {o, y}); C5: unblocking (Corollary 5)."""
    res = OWN[Bs]; best = best_owners(res)
    vs = res[best[0]][0]
    out = {}

    def new(y, B2):
        b = list(Bs); b[y] = B2; return tuple(b)
    # Lemma 3: owner re-base
    for y in P.free:
        if 'L3' in out: break
        for B2 in rebases(I, P, y):
            W = P.W(y); rest = list(bits(W & ~B2)); bestv = -1
            for k in range(len(rest) + 1):
                for K in itertools.combinations(rest, k):
                    Z = B2 | mask(K)
                    if P.safe(y, Z): bestv = max(bestv, pc(Z) + P.u(y, Z))
            if bestv > vs:
                b2 = new(y, B2)
                assert b2 in PAs and D[b2] <= D[Bs] - (bestv - vs), ('Lemma 3 violated', Bs, y, B2)
                out['L3'] = (y, sorted(bits(B2))); break
    for o in sorted(res, key=lambda o: (o not in best, o)):       # best owners first, then the other free agents
        gap = vs - res[o][0]                                       # 0 for a best owner
        for X in res[o][1]:
            cnt = counted(P, o, X)
            C = P.J & ~X
            for y in P.free:
                if y == o: continue
                for B2 in rebases(I, P, y):
                    b2 = new(y, B2)
                    assert b2 in PAs, ('Lemma 1 violated', Bs, y, B2)
                    P2 = PAs[b2]
                    Ny = I.needs(y, B2)
                    # Lemma 2 with the bundle X0 = X \ B2 of o (X0 ∩ B2 = ∅) and Y = X0 ∪ K, K maximal
                    X0 = X & ~B2
                    cnt0 = cnt if X0 == X else counted(P, o, X0)
                    e = sum(1 for x in cnt0 if P.Bs[x] & Ny)
                    gain = pc(X0) + max_ext(P2, o, X0) + len(cnt0) - e - vs
                    if gain > 0:
                        assert D[b2] <= D[Bs] - gain, ('Lemma 2 violated', Bs, o, y, B2)
                        out.setdefault('L2' if gap == 0 else 'L2o', (o, y, sorted(bits(B2))))
                    if gap or B2 & X: continue                     # the corollaries: best owners, B2 ∩ X = ∅
                    # Corollary 4 (release): B_y = {p, q}, B2 = {p}
                    if pc(P.Bs[y]) == 2 and pc(B2) == 1 and B2 & P.Bs[y]:
                        q = P.Bs[y] & ~B2; qg = next(bits(q))
                        h_i = not any(I.threat(z, X | q, P.bv[z]) for z in range(I.n) if z not in (o, y))
                        h_ii = I.val(y, X & I.R[y]) + I.v[y][qg] <= I.val(y, B2)
                        h_iii = e == 0
                        if h_i and h_ii and h_iii:
                            assert D[b2] <= D[Bs] - 1, ('Corollary 4 violated', Bs, o, y, B2)
                            out.setdefault('C4', (o, y, qg))
                            if all(not (I.R[z] >> qg) & 1 and (X & ~I.R[z]) for z in range(I.n) if z not in (o, y)):
                                out.setdefault('C4s', (o, y, qg))
                    # Corollary 5 (unblocking): B2 ⊆ B_y ∪ C, v_y(B2) >= v_y(B_y), some c ∈ C \ B2 blocked only by y
                    if not (B2 & ~(P.Bs[y] | C)) and I.val(y, B2) >= P.bv[y]:
                        for c in bits(C & ~B2):
                            Y = X | (1 << c)
                            if any(I.threat(z, Y, P.bv[z]) for z in range(I.n) if z not in (o, y)): continue
                            if I.threat(y, Y, I.val(y, B2)): continue
                            assert D[b2] <= D[Bs] - 1, ('Corollary 5 violated', Bs, o, y, B2, c)
                            out.setdefault('C5', (o, y, sorted(bits(B2)), c))
                            break
    return out


def multi_checks(I, P, Bs, PAs, D, OWN, reps):
    """certificates for a multi-agent repair P -> P' (P' among `reps`), checked and asserted:
    E2: Lemma 2* (extension through any move keeping the needed set) at a best owner o of P that does not move, an
        optimal bundle X, X0 = X minus the new bases: def(P') <= def(P) - (|Y| - |X0| ... ) as in k4/dl2.md;
    L7: Lemma 7 (the unfrozen agent x as owner unfreezes z frozen on g ∈ R_x that nobody else needs)."""
    res = OWN[Bs]; best = best_owners(res)
    vs = res[best[0]][0]
    out = {}
    omega = pc(P.J) - P.S
    for B2 in reps:
        P2 = PAs[B2]
        if P2.NA != P.NA: continue
        ch = [i for i in range(I.n) if Bs[i] != B2[i]]
        newb = 0
        NC = 0
        for i in ch: newb |= B2[i]; NC |= P2.N[i]
        for o in best:
            if o in ch or 'E2' in out: continue
            for X in res[o][1]:
                X0 = X & ~newb
                cnt0 = counted(P, o, X0)
                e = sum(1 for x in cnt0 if x in ch or not P2.frozen[x] or P.Bs[x] & NC)
                gain = pc(X0) + max_ext(P2, o, X0) + len(cnt0) - e - vs
                if gain > 0:
                    assert D[B2] <= D[Bs] - gain, ('Lemma 2* violated', Bs, B2, o)
                    out['E2'] = (o, [sorted(bits(b)) for b in B2]); break
        if 'L7' not in out:
            for z in range(I.n):
                if not P2.frozen[z]: continue
                g = P2.Bs[z]
                for x in P2.free:
                    if not (I.R[x] & g) or any(P2.N[i] & g for i in range(I.n) if i != x): continue
                    rest = list(bits(P2.J)); vg = I.val(x, g); bestv = -1
                    for k in range(len(rest) + 1):
                        for K in itertools.combinations(rest, k):
                            Z = P2.Bs[x] | mask(K)
                            if I.val(x, Z) > vg and P2.safe(x, Z):
                                cz = counted(P2, x, Z)
                                assert z in cz and D[B2] <= omega + 1 - pc(Z), ('Lemma 7 violated', B2, x, z)
                                bestv = max(bestv, pc(Z) + len(cz))
                    if bestv > vs:
                        assert D[B2] <= D[Bs] - (bestv - vs)
                        out['L7'] = (x, z, [sorted(bits(b)) for b in B2])
    return out


def signature(obs):
    """the obstruction class of P: the classes of the exposures at the best owner with the fewest exposures"""
    if not obs: return 'none'
    ob = min(obs, key=lambda ob: (len(ob['exp']), ob['o']))
    return '+'.join(sorted(set(v[0] for v in ob['exp'].values()))) or 'none'


def group(sig):
    """a coarse obstruction group of a signature"""
    parts = sig.split('+')
    if any(p.startswith('O') for p in parts): return 'other: frozen exposure not G/G1/L'
    if 'fO' in parts: return 'other: free exposure not e1-e3 with (U), (U2)'
    if 'fU' in parts or 'fU2' in parts: return 'free exposed agent violating (U)/(U2)'
    fr = [p for p in parts if p[0] in 'GL']
    fe = [p for p in parts if p[0] == 'e']
    dbl = any(p.endswith('2') for p in fr)
    if fr and fe: return 'H3 + H7 mixed' + (', double threat' if dbl else '')
    if fe: return 'H3 only (' + '/'.join(sorted(set(fe))) + ')'
    if fr: return 'H7 only, ' + ('double threat (Lemma D)' if dbl else 'single threats')
    return 'none'


def analyze(d, want_repairs=True, maxrep=6, lemmas=True):
    """list of records, one per min-frozen P with def(P) > 0"""
    I = M.Inst(d['sets'], d['vals'], d.get('m'))
    I.preallocs()
    if I.omega <= 0: return [], {'omega': I.omega, 'f': I.f, 'nmin': len(I.minP)}
    mp = [Bs for Bs, NA in I.minP]
    PAs = {Bs: PA(I, Bs) for Bs in mp}
    D, OWN = {}, {}
    for Bs in mp:
        dv, res = PAs[Bs].deficit()
        ref = I.deficit(Bs)
        ref = INF if ref is None else ref
        assert dv == ref, ('deficit mismatch', Bs, dv, ref)
        D[Bs], OWN[Bs] = dv, res
    # Pareto-maximality inside the min-frozen class (a Pareto improvement of a min-frozen P is min-frozen)
    vec = {Bs: tuple(PAs[Bs].bv) for Bs in mp}
    recs = []
    for Bs in mp:
        if D[Bs] <= 0: continue
        P = PAs[Bs]
        res = OWN[Bs]
        best = best_owners(res)
        pareto = not any(all(a >= b for a, b in zip(vec[B2], vec[Bs])) and vec[B2] != vec[Bs] for B2 in mp)
        obs = []
        for o in best:
            W = P.W(o)
            exp = [x for x in range(I.n) if x != o and I.threat(x, W, P.bv[x])]
            cls = {}
            for x in exp:
                c = exposure_class(P, o, x)
                if P.frozen[x]:
                    mult = sum(1 for o2 in P.free if o2 != x and I.threat(x, P.W(o2), P.bv[x]))
                    if mult >= 2: c += '2'
                lab, unh = labels(P, o, x)
                cls[x] = (c, lab, unh)
            X = res[o][1][0]
            obs.append({'o': o, 'X': sorted(bits(X)), 'C': sorted(bits(P.J & ~X)), 'u': P.u(o, X),
                        'exp': {str(x): list(v) for x, v in cls.items()}})
        sig = signature(obs)
        rec = {'Bs': [sorted(bits(B)) for B in Bs], 'def': D[Bs], 'f': I.f, 'omega': I.omega,
               'frozen': [i for i in range(I.n) if P.frozen[i]], 'J': sorted(bits(P.J)), 'pareto': pareto,
               'best': best, 'obs': obs, 'sig': sig, 'group': group(sig)}
        if want_repairs:
            dist = None; reps = []
            for B2 in mp:
                if D[B2] >= D[Bs]: continue
                k = sum(1 for a, b in zip(Bs, B2) if a != b)
                if dist is None or k < dist: dist, reps = k, [B2]
                elif k == dist: reps.append(B2)
            rec['k'] = dist
            ob0 = min(obs, key=lambda ob: (len(ob['exp']), ob['o'])) if obs else None
            o0 = ob0['o'] if ob0 else None
            exp0 = set(int(x) for x in ob0['exp']) if ob0 else set()
            rr = []
            for B2 in reps:
                P2 = PAs[B2]
                rr.append({'Bs': [sorted(bits(B)) for B in B2], 'def': D[B2], 'best': best_owners(OWN[B2]),
                           'type': repair_type(P, P2, o0, exp0), 'kind': repair_kind(P, P2, OWN[B2])})
            rr.sort(key=lambda r: (KIND_ORDER.index(r['kind']) if r['kind'] in KIND_ORDER else 9, r['def'], r['type']))
            rec['nrep'] = len(rr)
            rec['types'] = sorted(set(r['type'] for r in rr))
            rec['kinds'] = sorted(set(r['kind'] for r in rr))
            rec['kind'] = primary_kind(rec['kinds'])
            rec['reps'] = rr[:maxrep]
        if lemmas:
            lc = lemma_checks(I, P, Bs, PAs, D, OWN)
            rec['lemmas'] = lc
            if lc and want_repairs:
                assert rec['k'] == 1, ('a lemma applies at a state with k > 1', Bs, lc)
            if want_repairs and rec['k'] is not None and rec['k'] >= 2:
                rec['multi'] = multi_checks(I, P, Bs, PAs, D, OWN, reps)
        recs.append(rec)
    return recs, {'omega': I.omega, 'f': I.f, 'nmin': len(mp)}


def one_record(args):
    d, src = args
    try:
        recs, info = analyze(d)
    except AssertionError as e:
        return src, d, None, {'error': str(e)}
    return src, d, recs, info


def opener(fn):
    return gzip.open(fn, 'wt') if fn.endswith('.gz') else open(fn, 'w')


def main(argv):
    if not argv: print(__doc__); return
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in argv[1:] if a.startswith('--') and '=' in a)
    every = int(opt.get('every', 1)); mx = int(opt['max']) if 'max' in opt else None
    jobs = int(opt.get('jobs', 1)); out = opt.get('out')
    items = []
    if mode == 'suite':
        import glob
        for f in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
            d = json.load(open(f))
            if 'kind' in d or len(d['sets']) > int(opt.get('nmax', 6)): continue
            d.setdefault('m', 1 + max(g for S in d['sets'] for g in S))
            items.append(({'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}, d['id']))
    elif mode == 'catalog':
        cat = rest[0]
        recs = json.load(gzip.open(cat, 'rt'))['records'][::every]
        if mx: recs = recs[:mx]
        base = os.path.basename(cat).replace('.json.gz', '')
        for r in recs:
            c = r['core']
            items.append(({'sets': c['sets'], 'vals': r['vals'], 'm': c['m']},
                          '%s:%s#%d:%s' % (base, c['file'], c['idx'], ','.join(map(str, r['prof'])))))
    elif mode == 'one':
        d = json.loads(rest[0]); recs, info = analyze(d)
        print(json.dumps(info))
        for r in recs: print(json.dumps(r))
        return
    else:
        print(__doc__); return
    print('# command: python3 k4/dl2_classify.py ' + ' '.join(argv), flush=True)
    fo = opener(out) if out else None
    nprof = nstate = nerr = 0
    hist = {}
    it = map(one_record, items) if jobs <= 1 else Pool(jobs).imap(one_record, items, chunksize=4)
    for src, d, recs, info in it:
        nprof += 1
        if recs is None:
            nerr += 1; print('ERROR', src, info, flush=True); continue
        for r in recs:
            nstate += 1
            hist[r.get('k')] = hist.get(r.get('k'), 0) + 1
            if fo:
                r2 = dict(r); r2['src'] = src; r2['sets'] = d['sets']; r2['vals'] = d['vals']; r2['m'] = d['m']
                fo.write(json.dumps(r2, separators=(',', ':')) + '\n')
        if mode == 'suite':
            print('%-40s n=%d omega=%s f=%s minP=%s def>0: %d  k: %s' % (
                src, len(d['sets']), info.get('omega'), info.get('f'), info.get('nmin'), len(recs),
                sorted(set(r.get('k') for r in recs), key=lambda x: (x is None, x))), flush=True)
    if fo: fo.close()
    print('profiles %d, def>0 states %d, errors %d, k histogram %s' % (
        nprof, nstate, nerr, dict(sorted(hist.items(), key=lambda x: (x[0] is None, x[0] or 0)))), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
