"""The families S(sigma, k) and S'(sigma, k) of kgen/charity.md (Lemma CH7, §6), whose stranded states are CKMS
stopping states with sigma - 1 unallocated goods.  build() is copied verbatim from kgen/charity/stuck_family.py on
branch claude/kgen-charity (read 2026-11-26); only chlib.Inst is replaced by the small class below.  Used by
ht_wwalk.py sprime (k4/haxell.md §7)."""
import collections


class Inst:
    def __init__(self, n, m, v):
        self.n, self.m, self.v = n, m, v


def build(sigma, k, own=False, vals=None):
    """own=False: S(sigma, k).  own=True: the variant S'(sigma, k) (k >= 3) in which every agent values its own bundle:
    sources value x_j and x'_j at 2 each and their children at 5; relays value their own good at 4 and their children
    at 5; parents value a champion's good at 5."""
    p = sigma - 1
    # vals (own=True only): dict with keys y, x, g (champion), sx, sxp, sc (source: x_j, x'_j, a child), rz, rc (relay)
    V = dict(y=10, x=6, g=6, sx=2, sxp=2, sc=5, rz=4, rc=5)
    if vals:
        V.update(vals)
    cv = V['rc'] if own else 2
    goods = collections.OrderedDict()

    def good(name):
        if name not in goods:
            goods[name] = len(goods)
        return goods[name]
    v = []; X = []

    def agent(vals, holds):
        v.append({good(g): x for g, x in vals.items()}); X.append({good(g) for g in holds}); return len(v) - 1
    for j in range(sigma):
        good(('x', j)); good(("x'", j))
    for g in range(p):
        good(('g', g))
    src = [None] * sigma; children = {}
    # champions first (their goods), then trees bottom-up, then the sources
    champ = {}
    for j in range(sigma):
        for g in range(p):
            champ[(g, j)] = agent({('g', g): V['g'] if own else 6, ('x', j): V['x'] if own else 6,
                                   ('y', g, j): V['y'] if own else 10}, [('y', g, j)])
    rid = [0]

    def tree(leaves, top_arity):
        """Return the goods the parent must value: group leaves into relays of arity k until top_arity remain."""
        level = [('y',) + lf for lf in leaves]          # goods held by the current level's agents
        while len(level) > top_arity:
            nxt = []
            step = k - 1 if own else k                  # a relay values its children (and, if own, its good)
            for a in range(0, len(level), step):
                grp = level[a:a + step]
                rid[0] += 1; zr = ('z', rid[0])
                d = {gg: cv for gg in grp}
                if own:
                    d[zr] = V['rz']
                agent(d, [zr])
                nxt.append(zr)
            level = nxt
        return level
    for j in range(sigma):
        tops = tree([(g, (j - 1) % sigma) for g in range(p)], k - 2 if own else k - 1)
        vals = {gg: (V['sc'] if own else cv) for gg in tops}; vals[("x'", j)] = V['sxp'] if own else 1
        if own:
            vals[('x', j)] = V['sx']
        src[j] = agent(vals, [('x', j), ("x'", j)])
    I = Inst(len(v), len(goods), v)
    pool = {goods[('g', g)] for g in range(p)}
    return I, X, pool, src, champ



def sprime(sigma, k, own=True):
    """(name, sets, vals, m, state) for S'(sigma, k) (own=True) or S(sigma, k), state = the stranded allocation"""
    I, X, pool, src_, champ = build(sigma, k, own=own)
    sets = [sorted(d) for d in I.v]; vals = [[d[g] for g in sorted(d)] for d in I.v]
    st = [-1] * I.m
    for i, B in enumerate(X):
        for g in B:
            st[g] = i
    return ("S'(%d,%d)" % (sigma, k) if own else 'S(%d,%d)' % (sigma, k)), sets, vals, I.m, tuple(st)
