"""Lemma SET (k4/oc1max_multi.md §4): after a canonical chain from k in which k takes a junk pair H_0, agent k with
bundle H_0 is settled.  Every S* completion of the state B' with an owner o != k gives k nothing more, and
  (a) nobody strongly envies k's bundle H_0 (removing a good leaves one junk good);
  (b) k strongly envies nobody, provided the owner o is not x_1 (who holds Y_k) and k does not want o's base
      (|R_k| <= 4: outside Y_k and H_0, k values at most one more good; holders' bases are unwanted, frozen agents
      take nothing).
So the S* completions of B' with an owner o not in {k, x_1} whose base k does not want are exactly the allocations X_k = H_0 plus the S*-shaped completions of
the reduced state (instance without agent k and the goods H_0; same holders, frozen status as in B') that are EFX0
in the reduced instance.

Check: at every hard perfect start with |D| >= 2, for every canonical chain from every k in D and every improving junk
pair H_0, and every owner o not in {k, x_1} whose base k does not want, the two completion tests (raw enumeration in I, and in the reduced instance) agree.

    python3 k4/oc1max_multi/lemma_set.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, holders, sstar
from dred import canonical_chains, apply_chain


def reduced_sstar(I, nb, k, o):
    """S*-shaped completion of nb with owner o, computed in the instance without agent k and the goods of nb[k]:
    holders as in I (mmlib.holders), EFX0 checked among the other agents only"""
    keep = [i for i in range(I.n) if i != k]; H0 = set(nb[k])
    J = [g for g in junk(I, nb)]; hs = [h for h in holders(I, nb, o) if h != k]
    def efx0_red(X):
        own = {i: I.V(i, X[i]) for i in keep}
        for j in keep:
            if len(X[j]) < 2: continue
            for i in keep:
                if i == j: continue
                vs = [I.v[i].get(g, 0) for g in X[j]]
                if sum(vs) - min(vs) > own[i]: return False
        return True
    for r in range(min(len(J), len(hs)) + 1):
        for K in itertools.combinations(J, r):
            rest = [g for g in J if g not in K]
            for who in itertools.permutations(hs, r):
                X = [list(b) for b in nb]
                for g, i in zip(K, who): X[i].append(g)
                X[o] += rest
                if efx0_red(X): return True
    return False


if __name__ == '__main__':
    T = collections.Counter(); bad = []
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            base = base_from_picks(tuple(rec['picks'])); J = junk(I, base); p = [I.V(i, base[i]) for i in range(I.n)]
            for k in rec['D']:
                pairs = [H for H in itertools.combinations([g for g in J if g in I.R[k]], 2) if I.V(k, H) > p[k]]
                if not pairs: continue
                for path in canonical_chains(I, base, k):
                    for H0 in pairs:
                        nb = apply_chain(I, base, path, H0)
                        vk = I.V(k, nb[k])
                        for o in range(I.n):
                            if o == k: continue
                            if I.V(k, nb[o]) > vk: T['owners whose base k wants (excluded)'] += 1; continue
                            if o == path[1]: T['owner x_1 (excluded)'] += 1; continue
                            a = sstar(I, nb, o); b = reduced_sstar(I, nb, k, o)
                            T['owner tests'] += 1; T['  completion exists'] += a
                            if a != b: bad.append((rec['name'], rec['picks'], path, H0, o, a, b))
    print('$ python3 k4/oc1max_multi/lemma_set.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
    print('mismatches (Lemma SET violations):', len(bad), bad[:5])
