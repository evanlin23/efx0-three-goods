"""Lemma D1-red's proved parts and its open sub-lemmas (k4/oc1_hall.md §21), checked on every one-absorber-hard start
with exactly one dangerous agent k.  For every canonical chain k = x_0 -> ... -> x_t (each x_i wants Y_{x_{i-1}} and
takes it alone; x_t unfrozen at the picks) and every inclusion-minimal improving H_0 inside (J + {Y_{x_t}}) & R_k,
owner k:
  P1  the start's picks form a maximum matching, and x_t has a pick (Lemma MAX);
  P2  (J + {Y_{x_t}}) & R_k is improving for k (Lemma D1-pool);
  P3  if x_t is frozen after the chain, some agent off the chain wanted Y_{x_{t-1}} at the picks; k wants no chain pick;
  P4  only x_t and agents unfrozen at the picks value a junk good among the agents other than k; a crowded holder is
      one of them;
  P5  no HEAD and no CROWD => an S* completion owned by k (Lemma D1-red);
and, for the open sub-lemmas:
  D1-C  a chain with CROWD that fails: another minimal H_0 for the same chain repairs;
  D1-H  a chain with HEAD that fails: a chain through another wanter of Y_{x_{t-1}} repairs;
  HW    for every chain path with HEAD (for some minimal H_0): whether every off-chain wanter w of Y_{x_{t-1}} is
        frozen at the picks (case H-i) or some w is not (case H-ii), and whether the same path repairs with some
        minimal H_0, or a chain through such a w does;
  LONG  rule LONGEST: among the canonical chains of maximum length, some (or every) one repairs with some minimal H_0;
        a longest chain is never in case H-i (the chain through w would be longer);
  COMP  the least number of junk goods the completion found gives to holders (DT's moves included, so this is not
        |H| of Lemma 2*; 0 = k takes the whole pool).
Prints every violation of P1-P5 (there should be none) and every start where D1-C, D1-H or COMP <= 1 fails.

    python3 k4/oc1_hall/d1_subcases.py SRC
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, threatened, wants_good, shaped_completion
from max_matching import nu
from greedy_rules import canonical_paths, apply_chain
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load


def analyse(I, P, base, k, path, H0):
    """obstacles and the least |H| of an S* completion owned by k (None: no completion)"""
    n, m, Y = I.n, I.m, P.Y; xt = path[-1]
    b2 = apply_chain(I, P, base, path, H0); B2 = bundles_of(I, b2)
    F2 = set(frozen_set(I, b2)); J2 = [g for g in range(m) if b2[g] < 0]
    holders = [j for j in range(n) if len(B2[j]) <= 1 and j not in F2]
    X = shaped_completion(I, b2, k, holders, witness=True)
    comp = None if X is None else sum(len(X[j]) - len(B2[j]) for j in range(n) if j != k)
    pv2 = [I.val(i, B2[i]) for i in range(n)]
    obs = set(); crowded = []
    if xt in F2 and threatened(I, xt, pv2[xt], list(H0) + J2): obs.add('HEAD')
    for u in holders:
        if u == k: continue
        Hu = [g for g in H0 if g in I.R[u]]
        if len(Hu) >= 2 and I.val(u, Hu) > pv2[u]: obs.add('CROWD'); crowded.append(u)
    return obs, comp, F2, crowded, B2


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/oc1_hall/d1_subcases.py', *sys.argv[1:], flush=True)
    def bad(tag, *a):
        C[tag] += 1
        if C['shown ' + tag] < 3: C['shown ' + tag] += 1; print(tag, *a, flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); N = nu(I); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.D) != 1: continue
            base = base_of_picks(I, Y)
            if extends_A(E, base, 1): continue
            k = P.D[0]; C['starts'] += 1; inst = json.dumps((sets, vals))
            if sum(1 for y in Y if y is not None) != N: bad('P1 FAILS (picks not a maximum matching)', name, inst, Y)
            junkval = [i for i in range(n) if any(g in I.R[i] for g in P.J)]
            for i in junkval:
                if i != k and i in P.F: bad('P4 FAILS (frozen non-dangerous agent values junk)', name, inst, Y, i)
            best = None; res = {}
            for path in canonical_paths(I, P, k):
                xt = path[-1]
                if xt in P.F: continue
                if Y[xt] is None: bad('P1 FAILS (chain end without a pick)', name, inst, Y, path); continue
                pool = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] in I.R[k] else [])
                if I.val(k, pool) <= P.pv[k]: bad('P2 FAILS (pool not improving)', name, inst, Y, path); continue
                imp = [H for r in range(1, len(pool) + 1) for H in itertools.combinations(pool, r) if I.val(k, H) > P.pv[k]]
                for H0 in [H for H in imp if not any(set(K) < set(H) for K in imp)]:
                    obs, comp, F2, crowded, B2 = analyse(I, P, base, k, path, H0)
                    res[(path, H0)] = (obs, comp)
                    C['chains'] += 1
                    if xt in F2:
                        others = [w for w in P.W[path[-2]] if w not in path]
                        if not others: bad('P3 FAILS (head frozen, no off-chain wanter)', name, inst, Y, path, H0)
                    for g in range(m):
                        if base[g] >= 0 and g != Y[k] and any(g == Y[x] for x in path) and wants_good(I, B2, k, g):
                            bad('P3 FAILS (k wants a chain pick)', name, inst, Y, path)
                    for u in crowded:
                        if u != xt and (u in P.F or u in path): bad('P4 FAILS (crowded holder frozen at the picks)', name, inst, Y, path, u)
                    if not (obs & {'HEAD', 'CROWD'}):
                        C['chains free of HEAD and CROWD'] += 1
                        if comp is None: bad('P5 FAILS (Lemma D1-red)', name, inst, Y, path, H0)
                    if comp is not None and (best is None or comp < best): best = comp
            C['  starts with a repair of compensation %s' % best] += 1
            if best is None or best > 1: bad('COMP<=1 FAILS', name, inst, 'order', od, 'picks', Y, 'k', k, best)
            for (path, H0), (obs, comp) in res.items():
                if comp is not None: continue
                if 'CROWD' in obs:
                    C['failing chains with CROWD'] += 1
                    if any(c is not None for (p2, h2), (o2, c2) in res.items() for c in [c2] if p2 == path):
                        C['  ... repaired by another minimal H0 on the same chain (D1-C)'] += 1
                    else: bad('D1-C FAILS', name, inst, 'order', od, 'picks', Y, 'k', k, 'chain', path, 'H0', H0)
                if 'HEAD' in obs:
                    C['failing chains with HEAD'] += 1
                    pre = path[:-1]; ws = [w for w in P.W[path[-2]] if w not in path]
                    if any(c2 is not None for (p2, h2), (o2, c2) in res.items() if p2[:len(pre)] == pre and len(p2) > len(pre) and p2[len(pre)] in ws):
                        C['  ... repaired by a chain through another wanter of Y_{x_{t-1}} (D1-H)'] += 1
                    else: bad('D1-H FAILS', name, inst, 'order', od, 'picks', Y, 'k', k, 'chain', path, 'H0', H0)
            paths = {p for (p, h) in res}
            if paths:
                L = max(len(p) for p in paths); longest = [p for p in paths if len(p) == L]
                rep = [p for p in longest if any(c is not None for (p2, h2), (o2, c) in res.items() if p2 == p)]
                C['LONG some longest chain repairs'] += bool(rep); C['LONG every longest chain repairs'] += len(rep) == len(longest)
                C['LONG every chain repairs (some minimal H0)'] += all(any(c is not None for (p2, h2), (o2, c) in res.items() if p2 == p) for p in paths)
                if not rep: bad('LONG-SOME FAILS', name, inst, 'order', od, 'picks', Y, 'k', k, longest)
                for p in longest:
                    if any('HEAD' in o and c is None and all(w in P.F for w in P.W[p[-2]] if w not in p) for (p2, h2), (o, c) in res.items() if p2 == p):
                        bad('LONG H-i (contradicts the remark)', name, inst, Y, p)
                if len(rep) < len(longest): bad('LONG-ALL FAILS', name, inst, 'order', od, 'picks', Y, 'k', k, [p for p in longest if p not in rep])
            heads = {p for (p, h), (o, c) in res.items() if 'HEAD' in o}
            for path in heads:
                pre = path[:-1]; ws = [w for w in P.W[path[-2]] if w not in path]
                case = 'H-i (every other wanter frozen at the picks)' if all(w in P.F for w in ws) else 'H-ii (some other wanter unfrozen at the picks)'
                same = any(c is not None for (p2, h2), (o2, c2) in res.items() for c in [c2] if p2 == path)
                via = any(c2 is not None for (p2, h2), (o2, c2) in res.items() if p2[:len(pre)] == pre and len(p2) > len(pre) and p2[len(pre)] in ws)
                C['HW paths with HEAD, %s' % case] += 1
                C['HW paths with HEAD, %s: same path repairs %s, a path through another wanter repairs %s' % (case, same, via)] += 1
                if not same and not via: bad('HW FAILS', name, inst, 'order', od, 'picks', Y, 'k', k, 'chain', path)
    for k_ in sorted(C):
        if not k_.startswith('shown'): print(k_, C[k_])
