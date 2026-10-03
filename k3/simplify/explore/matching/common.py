"""Base states for the k = 3 core case (branch proof/k3-simplify, exploration "matching"). Evidence only.

A ranking profile `rank` lists, for every agent i, its goods (a_i, b_i, c_i), best first; every agent is strictly
balanced (values 4, 3, 2), and goods nobody ranks are worthless. EFX0 is then ordinal (Lemma L5).

A *base state* gives every agent one option:
    0 = nothing, 1 = a, 2 = b, 3 = c, 4 = the pair {b, c}
with all held goods distinct. Goods nobody holds are *junk*. Needs (as in the paper): option 0 needs a, b, c;
option 1 nothing; option 2 needs a; option 3 needs a and b; option 4 nothing. NA = all needed goods.
A base state is *valid* if every good of NA is held by an agent with a single good (so it can stay alone).

*Free* agents: options 0-3 whose good is not in NA. Slots: 2 for option 0, 1 for a free single, 0 otherwise.
Completion with absorber o (o free, or a pair holder): junk goes first into the other agents' slots; if everything
fits into all slots (o's too) no bundle has three goods. Otherwise o's bundle has >= 3 goods, and every agent x
holding only a_x with b_x, c_x both in junk or base(o) ("exposed for o") needs one of its junk goods b_x / c_x put
into a slot of another free agent: a minimum hitting set of those pairs must fit the other agents' slots.
"""
import itertools, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
from k3s import efx0 as efx0_raw  # noqa: E402

NONE, A, B, C, P = 0, 1, 2, 3, 4
VAL = (4, 3, 2)

def held(r, o):
    """goods held by an agent with ranking r under option o"""
    return () if o == 0 else ((r[o - 1],) if o < 4 else (r[1], r[2]))

def need(r, o):
    return r if o == 0 else (() if o in (1, 4) else r[:o - 1])

def states(rank, opts=(0, 1, 2, 3, 4)):
    """every base state (tuple of options) with distinct held goods"""
    n = len(rank); out = []
    cur = [0] * n
    def rec(i, used):
        if i == n: out.append(tuple(cur)); return
        for o in opts:
            h = held(rank[i], o)
            if any(g in used for g in h): continue
            cur[i] = o; rec(i + 1, used | set(h))
    rec(0, frozenset())
    return out

class Base:
    """a base state with derived data"""
    __slots__ = ('rank', 'm', 'opt', 'n', 'holder', 'NA', 'valid', 'J', 'free', 'slots')
    def __init__(self, rank, m, opt):
        self.rank, self.m, self.opt, self.n = rank, m, tuple(opt), len(rank)
        holder = {}
        for i, o in enumerate(opt):
            for g in held(rank[i], o): holder[g] = i
        self.holder = holder
        NA = set()
        for i, o in enumerate(opt): NA.update(need(rank[i], o))
        self.NA = NA
        self.valid = all(g in holder and opt[holder[g]] in (1, 2, 3) for g in NA)
        self.J = [g for g in range(m) if g not in holder]
        self.free = [i for i, o in enumerate(opt) if o == 0 or (o in (1, 2, 3) and rank[i][o - 1] not in NA)]
        self.slots = [0] * self.n
        for i in self.free: self.slots[i] = 2 if opt[i] == 0 else 1

    def overflow(self):
        return len(self.J) - sum(self.slots)

    def exposed(self, o):
        base_o = set(held(self.rank[o], self.opt[o])); W = set(self.J) | base_o
        return [x for x in range(self.n) if x != o and self.opt[x] == 1
                and self.rank[x][1] in W and self.rank[x][2] in W]

    def hit_pairs(self, o):
        """pairs (as sets of junk goods to hit) for the agents exposed for o; None if some pair lies in base(o)"""
        J = set(self.J); res = []
        for x in self.exposed(o):
            s = frozenset(g for g in self.rank[x][1:] if g in J)
            if not s: return None
            res.append(s)
        return res

    def complete(self, o, how='fill'):
        """allocation X (X[g] = agent) with absorber o, or None. how='fill': junk fills the other free agents'
        slots (hitting set first) and o takes the rest; how='k3s': only the hitting set goes to other free agents
        (one each, K3S step 3), o takes the rest."""
        if o not in self.free and self.opt[o] != 4: return None
        J = list(self.J)
        others = [f for f in self.free if f != o]
        S_other = sum(self.slots[f] for f in others)
        cap = {f: self.slots[f] for f in others}
        if how == 'k3s': cap = {f: 1 for f in others}; S_other = len(others)
        X = [None] * self.m
        for g, i in self.holder.items(): X[g] = i
        if how == 'fill' and len(J) <= S_other + self.slots[o]:
            # everything fits into slots: no bundle of three goods
            it = iter(J)
            for f in others + [o]:
                for _ in range(self.slots[f] if f != o else self.slots[o]):
                    g = next(it, None)
                    if g is None: break
                    X[g] = f
            return X
        pairs = self.hit_pairs(o)
        if pairs is None: return None
        H = min_hitting(pairs, S_other)
        if H is None: return None
        rest = [g for g in J if g not in H]
        if how == 'fill':
            order = list(H) + rest
        else:
            order = list(H)
        it = iter(order); placed = set()
        for f in others:
            for _ in range(cap[f]):
                g = next(it, None)
                if g is None: break
                X[g] = f; placed.add(g)
        for g in J:
            if g not in placed: X[g] = o
        return X

def min_hitting(pairs, limit):
    """a smallest set of goods meeting every set in `pairs` if it has at most `limit` goods, else None"""
    if not pairs: return []
    univ = sorted({g for s in pairs for g in s})
    for k in range(0, min(limit, len(univ)) + 1):
        for H in itertools.combinations(univ, k):
            hs = set(H)
            if all(s & hs for s in pairs): return list(H)
    return None

def vals(rank): return [dict(zip(r, VAL)) for r in rank]

def efx0_rank(rank, m, X):
    return X is not None and efx0_raw(len(rank), m, vals(rank), X)

def completes(b, how='fill', absorbers=None):
    """some absorber gives an EFX0 completion of base state b: returns (o, X) or None"""
    cand = absorbers if absorbers is not None else [i for i in range(b.n) if i in b.free or b.opt[i] == 4]
    for o in cand:
        X = b.complete(o, how)
        if X is not None:
            assert efx0_rank(b.rank, b.m, X), (b.rank, b.m, b.opt, o, X)
            return o, X
    return None

def upgrade_loop(rank, opt, m):
    """K3S step 2 on a base state: while some agent holds b, its c is junk and nobody needs b, it takes c too"""
    opt = list(opt)
    while True:
        b = Base(rank, m, opt); J = set(b.J)
        k = next((k for k in range(len(rank)) if opt[k] == 2 and rank[k][2] in J and rank[k][1] not in b.NA), None)
        if k is None: return tuple(opt)
        opt[k] = 4
