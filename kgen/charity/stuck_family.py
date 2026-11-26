"""Lemma CH7 (kgen/charity.md): robust CKMS stopping states with sigma - 1 unallocated goods at k = 3.

Construction S(sigma, k), for sigma >= 2 sources and p = sigma - 1 pool goods g_1..g_p:
  - source s_j (j in Z_sigma) holds {x_j, x'_j}; it values x'_j at 1 and its children (below) at 2;
  - champion c(g, j) for every pool good g and source j: values g at 6, x_j at 6, its own good y_{g,j} at 10, and
    holds {y_{g,j}};
  - the champions c(., j) of source j hang below source s_{j+1} in a tree of relays: a relay holds one good z_r that
    its parent values at 2, values each of its own children's goods at 2, and values nothing else; the source has at
    most k - 1 children, a relay at most k.
So every agent values at most k goods (champions 3), and every good is valued by someone.

The script builds S(sigma, k), checks with the raw definitions that it is EFX0 with strong charity, that no good can be
added to any bundle (U0), that the pool is unenvied (U1), and that U2 is inapplicable for every champion option
(chlib.champion_table mode 'all', chlib.shortest_rainbow); runs chlib.ckms(mode='all') from it to confirm that no
rule moves; checks Lemmas CH1-CH4 (chlib.stuck_report); and computes the least charity of the instance by SAT for the
small cases (it is 0: the instance has a complete EFX0 allocation, as TARGET says for k = 3).

    python3 kgen/charity/stuck_family.py SIGMA_MAX K [SAT_MAX_N]"""
import sys, collections
from chlib import (Inst, efx0, pool_ok, pool_of, u0_moves, envy_graph, sources, champion_table, shortest_rainbow,
                   ckms, stuck_report, sat_min_charity)


def build(sigma, k):
    p = sigma - 1
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
            champ[(g, j)] = agent({('g', g): 6, ('x', j): 6, ('y', g, j): 10}, [('y', g, j)])
    rid = [0]

    def tree(leaves, top_arity):
        """Return the goods the parent must value: group leaves into relays of arity k until top_arity remain."""
        level = [('y',) + lf for lf in leaves]          # goods held by the current level's agents
        while len(level) > top_arity:
            nxt = []
            for a in range(0, len(level), k):
                grp = level[a:a + k]
                rid[0] += 1; zr = ('z', rid[0])
                agent({gg: 2 for gg in grp}, [zr])
                nxt.append(zr)
            level = nxt
        return level
    for j in range(sigma):
        tops = tree([(g, (j - 1) % sigma) for g in range(p)], k - 1)   # s_j reaches the champions of source j-1
        vals = {gg: 2 for gg in tops}; vals[("x'", j)] = 1
        src[j] = agent(vals, [('x', j), ("x'", j)])
    I = Inst(len(v), len(goods), v)
    pool = {goods[('g', g)] for g in range(p)}
    return I, X, pool, src, champ


if __name__ == '__main__':
    SMAX, K = int(sys.argv[1]), int(sys.argv[2])
    SATN = int(sys.argv[3]) if len(sys.argv) > 3 else 14
    print('$ python3 kgen/charity/stuck_family.py', *sys.argv[1:], flush=True)
    for sigma in range(2, SMAX + 1):
        I, X, P, src, champ = build(sigma, K)
        assert pool_of(I, X) == P
        G = envy_graph(I, X); S = sources(I, X, G)
        assert sorted(S) == sorted(src), 'the sources are exactly s_1..s_sigma'
        ok = efx0(I, X) and pool_ok(I, X, P, strong=True)
        u0 = u0_moves(I, X, P)
        tab = champion_table(I, X, P, S, mode='all')
        cyc = shortest_rainbow(I, X, P, G, S, tab)
        X2, P2, cnt, tab2 = ckms(I, X=X, mode='all')
        moved = dict(cnt)
        rep = stuck_report(I, X2, P2, tab2)
        least = None
        if I.n <= SATN:
            least, _ = sat_min_charity(I, strong=True, upto=0)
        print('sigma %d k %d: n %d m %d max |R_i| %d | EFX0+strong charity %s | U0 moves %d | rainbow cycle %s | '
              'ckms(all) moves %s, pool %d | report %s | least charity %s' % (
                  sigma, K, I.n, I.m, I.k(), ok, len(u0), cyc is not None, moved or 'none', len(P2), rep,
                  least if least is not None else 'not computed'), flush=True)
        assert ok and not u0 and cyc is None and not moved and len(P2) == sigma - 1 and I.k() <= K
    print('all checks passed')
