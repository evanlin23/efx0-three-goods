"""The Hall obstruction at the smallest RING start, T3 with picks (0, 1, 4) (k4/oc1max_multi.md §10): for every canonical
chain from a dangerous agent, owner k, and every kept-out set H, the needy non-holders (Lemma M (C1)) and each needy
holder's acceptable goods; then the repairing moves and their S* owners.

    python3 k4/oc1max_multi/ring_hall.py
"""
import sys, itertools, json, gzip
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mmlib import Inst, base_from_picks, junk, frozen, holders, dangerous, moves, sstar_owners
from dred import canonical_chains, improving_sets, apply_chain
def why(I, B, o):
    n = I.n; J = junk(I, B); N1 = holders(I, B, o); b = [I.V(i, B[i]) for i in range(n)]; out = []
    for s in range(len(J) + 1):
        for H in itertools.combinations(J, s):
            X = list(B[o]) + [g for g in J if g not in H]
            needy = [i for i in range(n) if i != o and I.threat(i, b[i], X)]
            c1 = [i for i in needy if i not in N1]
            nb = {i: [h for h in H if h in I.R[i] and not I.threat(i, b[i] + I.v[i][h], X)] for i in needy if i in N1}
            out.append((H, 'X=%s' % X, 'C1 violators (needy non-holders) %s' % c1, 'needy holders -> acceptable goods %s' % nb, '#holders %d' % len(N1)))
    return out
for l in gzip.open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_oc1max_multi', 'hard2_starts.jsonl.gz'), 'rt'):
    r = json.loads(l)
    if r['name'] != 'T3' or tuple(r['picks']) != (0, 1, 4): continue
    I = Inst(r['inst']['sets'], r['inst']['vals'], r['inst']['m']); b = base_from_picks((0, 1, 4)); J = junk(I, b); D = dangerous(I, b)
    print('T3 picks (0,1,4)', [dict(sorted(I.v[i].items())) for i in range(I.n)], 'J', J, 'D', D, 'F', frozen(I, b))
    for k in D:
        for P in canonical_chains(I, b, k):
            for H0 in improving_sets(I, b, k, J + list(b[P[-1]]), True):
                nb = apply_chain(I, b, P, H0); print(' chain', P, 'H0', H0, 'state', nb, 'frozen', frozen(I, nb))
                for w in why(I, nb, k): print('   ', w)
    for nb, ds in moves(I, b).items():
        ss = sstar_owners(I, nb)
        if ss: print(' repair', ds, 'state', nb, 'S* owners', ss)
    break
