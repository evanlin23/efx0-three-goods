"""Lemma OWN (k4/oc1max_multi.md §4): the overlap completion (PWk(a)'s owner w_2, in general).

Let P = (k, ..., z) be a canonical chain from k with an improving junk pair H_0 inside J, B' the state after it.
Suppose
  (W1) every frozen d in D_T - {k} at B' is not threatened by B'_o + (J - H_0) at v_d(B'_d) (e.g. d values both
       goods of H_0, Lemma PL(c));
  (W2) the owner o is not k or x_1, holds at most one good, is unfrozen at B', and no agent frozen at B' (k included)
       values B'_o;
  (W3) some holder u != o is admissible for Y_z against B'_o + (J - H_0), and if z is frozen at B' it is not
       threatened by B'_o + (J - H_0).
Then B' has an S* completion owned by o in which u takes Y_z and k keeps exactly H_0 (Lemma 2*).

Census at the hard perfect starts with |D| >= 2: OWN chains (all k in D, all improving junk pairs, every o, u), the
explicit completion checked with the raw EFX0 definition; and how many starts not covered by KEEP or D-red it covers.

    python3 k4/oc1max_multi/lemma_own.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen, holders
from dred import canonical_chains, apply_chain
from lemma_b import truly_dangerous


def own_completion(I, nb, o, u, yz):
    """S* completion of nb owned by o in which u takes yz"""
    J = junk(I, nb); hs = [h for h in holders(I, nb, o) if h != u]
    rest0 = [g for g in J if g != yz]
    for r in range(min(len(rest0), len(hs)) + 1):
        for K in itertools.combinations(rest0, r):
            rest = [g for g in rest0 if g not in K]
            for who in itertools.permutations(hs, r):
                X = [list(b) for b in nb]
                X[u].append(yz)
                for g, i in zip(K, who): X[i].append(g)
                X[o] += rest
                if I.efx0(X): return X
    return None


def own_chains(I, base, D, DT, J):
    p = [I.V(i, base[i]) for i in range(I.n)]
    for k in D:
        pairs = [H for H in itertools.combinations([g for g in J if g in I.R[k]], 2) if I.V(k, H) > p[k]]
        for path in canonical_chains(I, base, k):
            z = path[-1]; yz = base[z][0]
            for H0 in pairs:
                nb = apply_chain(I, base, path, H0); F2 = set(frozen(I, nb))
                val = [I.V(i, nb[i]) for i in range(I.n)]
                L = [g for g in J if g not in H0]
                for o in range(I.n):
                    if o in (k, path[1]) or len(nb[o]) > 1 or o in F2: continue
                    if any(I.v[q].get(g, 0) > 0 for q in list(F2) + [k] for g in nb[o]): continue
                    W = list(nb[o]) + L
                    if any(d in F2 and I.threat(d, val[d], W) for d in DT if d != k): continue
                    if z in F2 and I.threat(z, val[z], W): continue
                    for u in holders(I, nb, o):
                        if u == o: continue
                        if not I.threat(u, val[u], W) or (yz in I.R[u] and not I.threat(u, val[u] + I.v[u][yz], W)):
                            yield path, H0, nb, o, u, yz


if __name__ == '__main__':
    T = collections.Counter(); viol = []
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            base = base_from_picks(tuple(rec['picks'])); J = junk(I, base); D = rec['D']
            DT = truly_dangerous(I, base, D, J)
            ok = False
            for path, H0, nb, o, u, yz in own_chains(I, base, D, DT, J):
                T['OWN (chain, owner, holder) triples'] += 1
                X = own_completion(I, nb, o, u, yz)
                if X is None: viol.append((rec['name'], rec['picks'], path, H0, o, u))
                else: ok = True
            from regimes import mechanism
            mech, _ = mechanism(I, rec)
            T['starts'] += 1; T[('mechanism ' + mech, 'OWN chain' if ok else 'no OWN chain')] += 1
    print('$ python3 k4/oc1max_multi/lemma_own.py', *sys.argv[1:])
    for k in sorted(T, key=str): print(k, T[k])
    print('Lemma OWN violations:', len(viol), viol[:5])
