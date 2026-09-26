"""Pre-allocations with three-good bases (proof/k4-strategy, k4/strategy.md §2.4): the space 𝒫_T.

𝒫 of k4/c4x.md §1 allows bases of at most two goods. At k = 4 its first failure (G1, k4/c4x.md §5) is a big-top agent
(four goods, a > b + c): no base of at most two goods is worth more than its top without containing it; only the triple
{b, c, d} is. 𝒫_T adds three-good bases:
  mode 'bt'  : a big-top agent may hold its lower triple R_i \\ {a_i};
  mode 'low' : every 4-good agent may hold its lower triple;
  mode 'any' : every 4-good agent may hold any three of its goods.
Needs are value-based; valid iff every needed good is a one-good base (so no good of a base of two or three goods is
needed, and no junk good is). Frozen: a one-good base that is needed. Slots: 2 - |B_i| for free agents with |B_i| <= 2,
none for a three-good base. A completion (owner o free, or none) is as in k4/c4x.md §1, with one more condition, since a
three-good bundle other than the owner's can be strongly envied: no agent strongly envies a three-good base of another
agent. Every completion found is re-checked to be EFX0 by the raw definition (model.Inst.efx0_check); the soundness
argument is Theorem 1'4's plus that explicit check.
Removal-only (the analogue of the deficit): the owner's bundle B_o ∪ (J \\ C) and every other three-good base threaten
nobody holding its base, and |C| fits the other agents' slots with o's needs from its bundle.
"""
import itertools
from model import Inst, bits, pc, mask


def triple_options(I, i, mode):
    gs = I.sets[i]
    if len(gs) != 4: return []
    vs = sorted(gs, key=lambda g: -I.v[i][g])
    a, b, c, d = vs
    if mode == 'bt':
        return [mask([b, c, d])] if I.v[i][a] > I.v[i][b] + I.v[i][c] else []
    if mode == 'low': return [mask([b, c, d])]
    if mode == 'any': return [mask(t) for t in itertools.combinations(gs, 3)]
    raise ValueError(mode)


class TSpace:
    def __init__(self, I, mode='bt'):
        self.I, self.mode = I, mode
        n = I.n
        opts = []
        for i in range(n):
            o = [mask(c) for k in range(3) for c in itertools.combinations(I.sets[i], k)] + triple_options(I, i, mode)
            opts.append(o)
        nd = [{B: I.needs(i, B) for B in opts[i]} for i in range(n)]
        out = []
        def rec(i, used, Bs, NA, singles):
            if i == n:
                if NA & ~singles == 0: out.append((tuple(Bs), NA))
                return
            for B in opts[i]:
                if B & used: continue
                Bs.append(B)
                rec(i + 1, used | B, Bs, NA | nd[i][B], singles | (B if pc(B) == 1 else 0))
                Bs.pop()
        rec(0, 0, [], 0, 0)
        self.P = out
        self.fz = {k: sum(1 for B in Bs if pc(B) == 1 and B & NA) for k, (Bs, NA) in enumerate(out)}
        self.f = min(self.fz.values())

    def omega(self, Bs, NA):
        I = self.I
        used = 0
        for B in Bs: used |= B
        J = pc(I.ALL & ~used)
        S = sum(0 if (pc(B) == 1 and B & NA) else max(0, 2 - pc(B)) for B in Bs)
        return J - S

    def tri_ok(self, Bs, hold, skip=None):
        """no agent j strongly envies a three-good base B_i (i != skip), j holding hold[j]"""
        I = self.I
        for i, B in enumerate(Bs):
            if i == skip or pc(B) < 3: continue
            for j in range(I.n):
                if j != i and I.threat(j, B, I.val(j, hold[j])): return False
        return True

    def removal_only(self, Bs):
        I, n = self.I, self.I.n
        N = [I.needs(i, Bs[i]) for i in range(n)]
        NA = 0
        for x in N: NA |= x
        used = 0
        for B in Bs: used |= B
        J = I.ALL & ~used
        frozen = [pc(Bs[i]) == 1 and bool(Bs[i] & NA) for i in range(n)]
        S = sum(0 if frozen[i] else max(0, 2 - pc(Bs[i])) for i in range(n))
        if pc(J) <= S:
            return self.tri_ok(Bs, Bs), None
        Jl = list(bits(J))
        for o in range(n):
            if frozen[o]: continue
            if not self.tri_ok(Bs, Bs, skip=o): continue
            others = 0
            for j in range(n):
                if j != o: others |= N[j]
            for k in range(len(Jl) + 1):
                for Cl in itertools.combinations(Jl, k):
                    C = mask(Cl); X = Bs[o] | (J & ~C)
                    if any(I.threat(x, X, I.val(x, Bs[x])) for x in range(n) if x != o): continue
                    NA2 = others | I.needs(o, X)
                    slots = sum(0 if (pc(Bs[j]) == 1 and Bs[j] & NA2) else max(0, 2 - pc(Bs[j])) for j in range(n) if j != o)
                    if k <= slots:
                        hold = list(Bs); hold[o] = X
                        if not self.tri_ok(Bs, hold, skip=o): continue
                        return True, o
        return False, None

    def completable_full(self, Bs):
        I, n = self.I, self.I.n
        N = [I.needs(i, Bs[i]) for i in range(n)]
        used = 0
        for B in Bs: used |= B
        J = list(bits(I.ALL & ~used))
        for o in [None] + list(range(n)):
            NA = 0
            for i in range(n): NA |= N[i] if i != o else 0
            if o is not None and pc(Bs[o]) == 1 and Bs[o] & (NA | N[o]): continue
            for k in range(len(J) + 1):
                if o is None and k: break
                for Kl in itertools.combinations(J, k):
                    Xo = (Bs[o] | mask(Kl)) if o is not None else 0
                    NAo = NA | (I.needs(o, Xo) if o is not None else 0)
                    cap = {i: (0 if pc(Bs[i]) == 1 and Bs[i] & NAo else max(0, 2 - pc(Bs[i]))) for i in range(n) if i != o}
                    rest = [g for g in J if g not in Kl]
                    if len(rest) > sum(cap.values()): continue
                    agents = sorted(cap)
                    for pick in itertools.product(agents, repeat=len(rest)):
                        if any(pick.count(i) > cap[i] for i in agents): continue
                        X = list(Bs)
                        if o is not None: X[o] = Xo
                        for g, i in zip(rest, pick): X[i] |= 1 << g
                        if I.efx0_check(X): return True, o, X
        return False, None, None

    def pareto_max(self, sub=None):
        I = self.I
        sp = self.P if sub is None else sub
        vecs = [tuple(I.val(i, Bs[i]) for i in range(I.n)) for Bs, _ in sp]
        return [sp[k] for k, a in enumerate(vecs) if not any(all(b[i] >= a[i] for i in range(I.n)) and b != a for b in vecs)]


def pareto_every(d, mode='bt', full=False):
    I = Inst(d['sets'], d['vals'], d.get('m'))
    T = TSpace(I, mode)
    par = T.pareto_max()
    test = (lambda Bs: T.completable_full(Bs)[0]) if full else (lambda Bs: T.removal_only(Bs)[0])
    bad = [Bs for Bs, NA in par if not test(Bs)]
    return not bad, '%d Pareto-maxima, %d not completable%s' % (len(par), len(bad), '' if full else ' (removal-only)')


def minfrozen_some(d, mode='bt'):
    I = Inst(d['sets'], d['vals'], d.get('m'))
    T = TSpace(I, mode)
    mf = [(Bs, NA) for k, (Bs, NA) in enumerate(T.P) if T.fz[k] == T.f]
    return any(T.removal_only(Bs)[0] for Bs, NA in mf), 'f_T=%d' % T.f
