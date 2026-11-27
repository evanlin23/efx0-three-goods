"""Explicit chain rules at hard starts (no S* completion), k4/oc1_hall.md §6.  A canonical chain from k in D: distinct
agents k = x_0, x_1, ..., x_t (t >= 1), each x_i (i >= 1) wanting B_{x_{i-1}} and taking no junk.  Rules for H_0 (the
set k takes), each required to be improving (v_k(H_0) > p_k):
  ALL  : every good of (J + B_{x_t}) that k values;
  JUNK : every junk good k values (B_{x_t} becomes junk unless ...);
  MIN  : some inclusion-minimal improving subset of J + B_{x_t};
  ANY  : some improving subset.
Owner after the chain: k (OWN=k), the end x_t (OWN=end), or either.  Reports, per rule and owner policy, the hard
starts on which some k in D and some canonical chain from k work.

    python3 k4/oc1_hall/greedy_rules.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of
from chain_shapes import s_star_owners
from min_frozen import load


def canonical_paths(I, P, k):
    """simple paths k = x_0 -> ... -> x_t (t >= 1), x_i wanting Y_{x_{i-1}}"""
    out = []
    def ext(path):
        if len(path) >= 2: out.append(tuple(path))
        last = path[-1]
        for y in P.W[last]:
            if y not in path and P.Y[last] is not None: ext(path + [y])
    ext([k]); return out


def apply_chain(I, P, base, path, H0):
    nb = list(base); Y = P.Y; xt = path[-1]
    if Y[xt] is not None: nb[Y[xt]] = -1
    for i in range(len(path) - 1, 0, -1): nb[Y[path[i - 1]]] = path[i]
    for g in H0: nb[g] = path[0]
    return tuple(nb)


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/greedy_rules.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); base = base_of_picks(I, Y)
            if s_star_owners(I, base): continue
            P = Picks(I, Y); C['hard starts'] += 1
            got = set()
            for k in P.D:
                for path in canonical_paths(I, P, k):
                    xt = path[-1]
                    pool = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] is not None and Y[xt] in I.R[k] else [])
                    imp = [H for r in range(1, len(pool) + 1) for H in itertools.combinations(pool, r) if I.val(k, H) > P.pv[k]]
                    if not imp: continue
                    minimal = [H for H in imp if not any(set(K) < set(H) for K in imp)]
                    junk = tuple(g for g in pool if g in P.J)
                    rules = {'ALL': [tuple(pool)] if tuple(pool) in imp else [], 'JUNK': [junk] if junk in imp else [],
                             'MIN': minimal, 'ANY': imp}
                    for rn, Hs in rules.items():
                        for H0 in Hs:
                            ow = s_star_owners(I, apply_chain(I, P, base, path, H0))
                            if path[0] in ow: got.add((rn, 'k'))
                            if xt in ow: got.add((rn, 'end'))
                            if path[0] in ow or xt in ow: got.add((rn, 'k or end'))
                            if ow: got.add((rn, 'any owner'))
            for g in got: C['  %s, owner %s' % g] += 1
            if ('ANY', 'any owner') not in got and C['shown'] < 4:
                C['shown'] += 1; print('NO CANONICAL RULE', name, json.dumps((sets, vals)), 'picks', Y, 'D', P.D, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
