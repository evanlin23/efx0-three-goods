"""Independent check of the coordinator's reported OC1^max counterexample at n = 4 (k4/sd_induct.md §9): the order's
picks form a maximum matching, have no one-absorber completion (numpy brute force, raw EFX0), and no state after one
improving chain or ring (de_free.moves; chains cross-checked with sdilib.chains) has one; then: does some state after
two sequential moves have one?

    python3 k4/sdind/verify_oc1max_n4.py"""
import itertools
import networkx as nx
import _paths
from sdilib import Inst, sd, completions, picks_base, chains, wanted_by
import de_free as DF
from sdclib import Enc
sets = [[0, 1, 2, 5], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 6]]
vals = [[2, 10, 4, 7], [10, 3, 4, 8], [3, 5, 6, 7], [3, 2, 4]]
m = 7; I = Inst(sets, vals, m); E = Enc(sets, vals, m); n = 4
Y, J = sd(I, (0, 3, 2, 1))
G = nx.Graph(); G.add_nodes_from(('a', i) for i in range(n))
G.add_edges_from((('a', i), ('g', g)) for i in range(n) for g in I.R[i])
nu = len(nx.bipartite.maximum_matching(G, top_nodes=[('a', i) for i in range(n)])) // 2
print('picks', Y, 'junk', J, 'picks', sum(g is not None for g in Y), 'nu', nu, 'wanted by', wanted_by(I, Y))
_, A1 = completions(I, picks_base(I, Y), 1); _, Af = completions(I, picks_base(I, Y), None)
print('one-absorber completions', len(A1), 'free completions', len(Af))
base = [-1] * m
for i, g in enumerate(Y):
    if g is not None: base[g] = i
def bases_of(st): return [[g for g in range(m) if st[g] == i] for i in range(n)]
def ok(st): return len(completions(I, bases_of(st), 1)[1]) > 0
DF.CHAIN_ONLY = True; ch = set(DF.moves(E, tuple(base)))
mine = set()
for nb, p, H in chains(I, picks_base(I, Y)):
    b = [-1] * m
    for i, bb in enumerate(nb):
        for g in bb: b[g] = i
    mine.add(tuple(b))
DF.CHAIN_ONLY = False; one = set(DF.moves(E, tuple(base)))
print('one-move states', len(one), '(chains: de_free', len(ch), 'sdilib', len(mine), 'agree', ch == mine, ')',
      'with a one-absorber completion:', sum(ok(s) for s in one))
two = set()
for s in one: two |= set(DF.moves(E, s))
good2 = [s for s in two if ok(s)]
print('two-move states', len(two), 'with a one-absorber completion:', len(good2))
if good2: print('example two-move repair: bases', bases_of(good2[0]))
