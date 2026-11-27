"""Minimal checker for the rank-dominance witnesses (k4/rkmax.md §3), written separately from rklib.

For every start (sets, vals, picks Y) of a failure export and its witness M:
  1. Y and M are matchings: every assigned good is relevant to its agent (value > 0), no good twice;
  2. |M| = |Y| = nu, where nu is recomputed here by augmenting paths (Kuhn's algorithm);
  3. rank_i(X) = 1 + #{g : v_i(g) > v_i(X_i)} (5 if unassigned); sorted(rank(M)) <= sorted(rank(Y)) pointwise and
     differs.
Then sigma(M) > sigma(Y) lexicographically (Lemma TC), so Y is not sigma-maximal; with the export's completeness this
certifies RKDOM and RKMAX on the export's hypergraphs (given the type reduction).
    python3 rk_dom_check.py EXPORT WITNESSES"""
import sys, gzip, json


def max_matching_size(sets):
    match = {}                                       # good -> agent

    def aug(a, seen):
        for g in sets[a]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen):
                match[g] = a; return True
        return False
    return sum(1 for a in range(len(sets)) if aug(a, set()))


def check(sets, vals, Y, M):
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    for X in (Y, M):
        goods = [g for g in X if g is not None]
        if len(goods) != len(set(goods)): return 'good used twice'
        if any(g is not None and v[i].get(g, 0) <= 0 for i, g in enumerate(X)): return 'irrelevant good'
    nu = max_matching_size(sets)
    if sum(g is not None for g in Y) != nu or sum(g is not None for g in M) != nu: return 'not maximum'

    def rank(i, g):
        return 5 if g is None else 1 + sum(1 for h in v[i] if v[i][h] > v[i][g])
    rY = sorted(rank(i, g) for i, g in enumerate(Y)); rM = sorted(rank(i, g) for i, g in enumerate(M))
    if not all(a <= b for a, b in zip(rM, rY)) or rM == rY: return 'not dominating'
    return 'ok'


if __name__ == '__main__':
    d = json.load(gzip.open(sys.argv[1])); w = json.load(gzip.open(sys.argv[2]))
    W = {(a, b): c for a, b, c in w['witnesses']}
    from collections import Counter
    C = Counter()
    for hi, h in enumerate(d['hypergraphs']):
        for si, st in enumerate(h['starts']):
            M = W.get((hi, si))
            C['missing witness' if M is None else check(h['sets'], st['vals'], st['picks'], M)] += 1
    print('$ python3 k4/rkmax/rk_dom_check.py', sys.argv[1].split('/')[-1], sys.argv[2].split('/')[-1])
    for k in sorted(C): print(k, C[k])
