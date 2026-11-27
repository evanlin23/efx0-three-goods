"""The two-move repairs of the 11 n = 4 OC1^max failures in the exchange language (k4/matching.md §5).

For each stored start: every official first move (described as in explain.described_moves) after which a Lemma EX*
exchange repairs, with the exchange found (chain, H0, middle junk, owner) and the values involved.

    python3 k4/matching/n4_twomoves.py [instance ...]"""
import sys, os, json, collections
import _mpaths  # noqa: F401
from mlib import M
from explain import described_moves
from exchange import ex_star_witness

if __name__ == '__main__':
    D = json.load(open(os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'oc1max_cex_n4.json')))['instances']
    want = [int(a) for a in sys.argv[1:]] or range(len(D))
    T = collections.Counter()
    for t in want:
        d = D[t]; I = M(d['sets'], d['vals']); Y = d['picks']; base = [[g] for g in Y]
        print('instance %d' % t, json.dumps([d['sets'], d['vals']]), 'picks', Y, 'J', I.junk(base), 'frozen', I.frozen(base),
              'D', I.dangerous(base), 'holders', I.holders(base))
        print('   want arcs', [(i, j) for i in range(I.n) for j in range(I.n) if i != j and I.wants(i, Y[j], base)])
        for (kind, path, Hs), B1 in described_moves(I, base):
            w = ex_star_witness(I, B1)
            if not w: continue
            P, H0, Hs2, o, B2 = w
            X = I.complete(B2, 0, 'ss', [o])
            print('   first %s %s %s -> %s | then chain %s H0 %s Hs %s owner %d -> %s | completion %s' % (
                kind, list(path), {i: list(h) for i, h in Hs.items() if h}, B1, P, H0, {i: h for i, h in Hs2.items() if h}, o, B2,
                X[1] if X else None))
            T['first move kind %s' % kind] += 1
            T['first move from a dangerous agent %s' % (path[0] in I.dangerous(base))] += 1
            T['second chain starts at the first move\'s head %s' % (P[0] == path[0])] += 1
            T['second chain starts at a frozen agent of B1 %s' % (P[0] in I.frozen(B1))] += 1
            picks = set(Y); rel = set(I.junk(B1)) & picks
            T['second H0 holds %d picks of Y (foreign picks collected by its head: %d)' % (
                len(set(H0) & picks), len((set(H0) & picks) - {Y[P[0]]}))] += 1
            T['second H0 contains a pick released by the first move %s' % bool(set(H0) & rel)] += 1
            T['first move head takes a junk pair valued by another dangerous agent %s' % any(
                len(set(Hs[0]) & set(I.junk(base)) & I.R[x]) >= 2 for x in I.dangerous(base) if x != path[0])] += 1
    for k in sorted(T): print(k, T[k])
