"""Lemma KEEP and the D_T census (k4/oc1max_multi.md §3).

D_T = the dangerous agents threatened by the junk alone (J at the pick value): the *truly dangerous* agents.
Lemma KEEP: let P = (k, ..., z) be a canonical chain from k with an improving H_0 inside the junk J (not using the head's
pick), without CROWD, whose head z is unfrozen at B' (a holder).  Then the state B' after P has an S* completion owned by k in which the head z takes back
its old pick Y_z as its one junk good, provided every agent of D_T - {k} is neutralized (unfrozen at B', or
unthreatened by J at its value at B').  In particular, if D_T = {k}, every such chain repairs.

The census, at every hard perfect start with |D| >= 2:
  * the size of D_T;
  * KEEP chains: canonical chains from k in D_T with an improving H_0 inside J, head unfrozen at B', no CROWD, every agent of
    D_T - {k} neutralized.  For each, the explicit completion of the lemma (owner k, z takes Y_z, the other exposed
    holders by Theorem DT's moves, via mmlib.sstar restricted to that shape) is checked with the raw EFX0 definition.

    python3 k4/oc1max_multi/lemma_b.py FILE.jsonl [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen, holders, sstar
from dred import canonical_chains, improving_sets, obstacles, apply_chain


def truly_dangerous(I, base, D, J):
    return [d for d in D if I.threat(d, I.V(d, base[d]), J)]


def keep_completion(I, nb, k, z):
    """S* completion of nb owned by k in which z takes its old pick back (the good of nb's junk that z values most
    among its old pick); search over the other holders' slots, raw EFX0"""
    J = junk(I, nb); hs = [h for h in holders(I, nb, k) if h != z]
    yz = [g for g in J if g in I.R[z] and g not in nb[z]]
    for g0 in yz:
        rest0 = [g for g in J if g != g0]
        for r in range(min(len(rest0), len(hs)) + 1):
            for K in itertools.combinations(rest0, r):
                rest = [g for g in rest0 if g not in K]
                for who in itertools.permutations(hs, r):
                    X = [list(b) for b in nb]
                    X[z].append(g0)
                    for g, i in zip(K, who): X[i].append(g)
                    X[k] += rest
                    if I.efx0(X): return X
    return None


def keep_star_completion(I, nb, k, u, yz):
    """S* completion of nb owned by k in which holder u takes the released pick yz (Lemma KEEP*)"""
    J = junk(I, nb); hs = [h for h in holders(I, nb, k) if h != u]
    rest0 = [g for g in J if g != yz]
    for r in range(min(len(rest0), len(hs)) + 1):
        for K in itertools.combinations(rest0, r):
            rest = [g for g in rest0 if g not in K]
            for who in itertools.permutations(hs, r):
                X = [list(b) for b in nb]
                X[u].append(yz)
                for g, i in zip(K, who): X[i].append(g)
                X[k] += rest
                if I.efx0(X): return X
    return None


def keep_star_chains(I, base, k, DT, J):
    """Lemma KEEP*: canonical chains from k with an improving H_0 inside J, no crowding, every frozen agent of
    (D_T - {k}) + {z} at B' unthreatened by J, and a holder u admissible for Y_z (owner bundle J).  Yields
    (path, H0, nb, u)."""
    for path in canonical_chains(I, base, k):
        z = path[-1]; yz = base[z][0]
        for H0 in improving_sets(I, base, k, J, True):
            nb, ob = obstacles(I, base, path, H0)
            if 'CROWD' in ob: continue
            F2 = set(frozen(I, nb)); val = [I.V(i, nb[i]) for i in range(I.n)]
            if any(q in F2 and I.threat(q, val[q], J) for q in list(DT) + [z] if q != k): continue
            for u in holders(I, nb, k):
                if not I.threat(u, val[u], J) or (yz in I.R[u] and not I.threat(u, val[u] + I.v[u][yz], J)):
                    yield path, H0, nb, u


if __name__ == '__main__':
    T = collections.Counter(); viol = []
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            Y = tuple(rec['picks']); base = base_from_picks(Y); J = junk(I, base); D = rec['D']
            DT = truly_dangerous(I, base, D, J)
            T['starts'] += 1; T['|D_T| = %d' % len(DT)] += 1
            st = set()
            for k in DT:
                for path in canonical_chains(I, base, k):
                    z = path[-1]
                    for H0 in improving_sets(I, base, k, J, True):
                        nb, ob = obstacles(I, base, path, H0)
                        if {'HEAD', 'CROWD'} & ob: continue
                        F2 = set(frozen(I, nb))
                        if z in F2: continue          # the head must be a holder at B'
                        neut = all(d not in F2 or not I.threat(d, I.V(d, nb[d]), J) for d in DT if d != k)
                        if not neut: continue
                        T['KEEP chains'] += 1
                        X = keep_completion(I, nb, k, z)
                        if X is None: viol.append((rec['name'], Y, path, H0))
                        else: st.add('KEEP chain repairs')
            T[('|D_T| = %d' % len(DT), 'KEEP chain' if 'KEEP chain repairs' in st else 'no KEEP chain')] += 1
            for k in DT:
                for path, H0, nb, u in keep_star_chains(I, base, k, DT, J):
                    T['KEEP* chains'] += 1
                    X = keep_star_completion(I, nb, k, u, base[path[-1]][0])
                    if X is None: viol.append(('KEEP*', rec['name'], Y, path, H0, u))
                    else: st.add('KEEP* chain repairs')
            T[('|D_T| = %d' % len(DT), 'KEEP* chain' if 'KEEP* chain repairs' in st else 'no KEEP* chain')] += 1
    print('$ python3 k4/oc1max_multi/lemma_b.py', *sys.argv[1:])
    for k in sorted(T, key=str): print(k, T[k])
    print('Lemma KEEP / KEEP* violations (chains without the completion):', len(viol), viol[:5])
