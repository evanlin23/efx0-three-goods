"""B< (k4/sd_induct.md §9): which SD orders' picks form a maximum matching of the agent/relevant-good graph, and does
OC1 (one-absorber completion of the picks, or after one improving chain or ring) hold for them?  Brute force
(sdilib.completions); chains and rings from de_free.moves.

    python3 k4/sdind/verify_blt_max.py"""
import itertools, collections
import networkx as nx
import _paths
from sdilib import Inst, sd, completions, picks_base
import de_free as DF
from sdclib import Enc
sets = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
vals = [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]
m = 10; I = Inst(sets, vals, m); E = Enc(sets, vals, m)
G = nx.Graph(); G.add_nodes_from(('a', i) for i in range(6))
G.add_edges_from((('a', i), ('g', g)) for i in range(6) for g in I.R[i])
nu = len(nx.bipartite.maximum_matching(G, top_nodes=[('a', i) for i in range(6)])) // 2
DF.CHAIN_ONLY = False
res = {}; C = collections.Counter()
for o in itertools.permutations(range(6)):
    Y = tuple(sd(I, o)[0])
    if Y not in res:
        _, A = completions(I, picks_base(I, list(Y)), 1)
        if len(A): res[Y] = 0
        else:
            b = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: b[g] = i
            res[Y] = 1 if any(len(completions(I, [[g for g in range(m) if st[g] == i] for i in range(6)], 1)[1])
                              for st in DF.moves(E, tuple(b))) else None
    size = sum(g is not None for g in Y)
    C['orders, picks %s, OC1 %s' % ('maximum (%d)' % nu if size == nu else 'size %d' % size,
                                    'fails' if res[Y] is None else 'needs %d chain(s)' % res[Y])] += 1
print('nu =', nu, '; distinct outcomes', len(res))
for k in sorted(C): print(k, C[k])
