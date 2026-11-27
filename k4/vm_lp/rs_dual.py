"""RS (min rank sum) duals at RS-optimal maximum matchings (exploration for k4/vm_lp/).
For a perfect-agent maximum matching Y (nu = n), the RS LP  min sum rank x  s.t. each agent matched once, each good
at most once  has dual prices beta_g >= 0 (beta(junk) = 0 by complementary slackness) with, for every relevant
edge (i, g):  beta_g >= beta_{Y_i} - (rank_i(g) - rank_i(Y_i)).  Y is RS-optimal iff such beta exists; the least
solution beta_min is a longest-path potential.  For a truly dangerous agent x (frozen, the junk threatens it) the
junk constraints beta_{Y_x} <= rank_x(g) - rank_x(Y_x) (g junk in R_x) have slack s_x = min_g(...) - beta_min(Y_x);
s_x = 0 means an RS-neutral alternating path in which x steps down to a junk good.
    python3 rs_dual.py EXPORT.json.gz [LIMIT]"""
import sys, os, gzip, json, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rklib_copy as R


def beta_min(P, Y):
    """least nonnegative prices on goods with beta(junk) = 0 and beta_g >= beta_{Y_i} - (rank_i(g) - rank_i(Y_i)) for
    every agent i and relevant g; None if infeasible (Y not RS-optimal among perfect-agent matchings)"""
    n, m = P.n, P.m; held = {Y[i]: i for i in range(n) if Y[i] is not None}
    beta = {g: 0 for g in range(m)}
    for _ in range(m + 2):                                   # Bellman-Ford style relaxation (longest paths)
        changed = False
        for i in range(n):
            yi = Y[i]
            for g in P.rel[i]:
                if g == yi: continue
                lb = beta[yi] - (P.rank(i, g) - P.rank(i, yi))
                if g in held:
                    if beta[g] < lb: beta[g] = lb; changed = True
                # junk: beta must stay 0; constraint 0 >= beta[yi] - gap checked below
        if not changed: break
    else:
        return None
    for i in range(n):
        for g in P.rel[i]:
            if g not in held and beta[Y[i]] - (P.rank(i, g) - P.rank(i, Y[i])) > 0: return None
    return beta


def main():
    J = json.load(gzip.open(sys.argv[1])); limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
    C = collections.Counter(); ex = collections.defaultdict(list); nprof = 0
    for h in J['hypergraphs']:
        seen = set()
        for st in h['starts']:
            key = json.dumps(st['vals'])
            if key in seen: continue
            seen.add(key); nprof += 1
            if limit and nprof > limit: break
            P = R.Prof(h['sets'], st['vals'])
            nu, Ms = P.max_matchings()
            if nu != P.n: C['nu < n (skipped)'] += 1; continue
            rs = {M: sum(P.ranks(M)) for M in Ms}; best = min(rs.values())
            for Y in [M for M in Ms if rs[M] == best]:
                beta = beta_min(P, Y); assert beta is not None, (h['sets'], st['vals'], Y)
                oc = P.oc1(Y); ro = P.roles(Y)
                J_ = set(ro['J']); slack = {}
                for x in ro['DT']:
                    gaps = [P.rank(x, g) - P.rank(x, Y[x]) for g in P.rel[x] if g in J_]
                    slack[x] = min(gaps) - beta[Y[x]]
                tight = any(s == 0 for s in slack.values())
                k = (oc, '|DT|=%d' % len(ro['DT']), 'some DT tight' if tight else ('all DT slack' if slack else 'no DT'))
                C[k] += 1
                if len(ex[k]) < 2: ex[k].append((h['list'], h['idx'], st['vals'], Y, slack, {g: b for g, b in beta.items() if b}))
    print('profiles', nprof)
    for k, v in sorted(C.items(), key=str): print(' ', v, k)
    for k, L in ex.items():
        for e in L: print('  ex', k, e)


if __name__ == '__main__' and not (len(sys.argv) > 3 and sys.argv[3] == 'shapes'):
    main()


def tight_in(P, Y, beta, x):
    """agents j with a tight wants-arc j -> x: j wants Y_x and beta(Y_x) - beta(Y_j) = rank_j(Y_j) - rank_j(Y_x)"""
    return [j for j in range(P.n) if j != x and Y[x] in P.rel[j] and P.rank(j, Y[x]) < P.rank(j, Y[j])
            and beta[Y[x]] - beta[Y[j]] == P.rank(j, Y[j]) - P.rank(j, Y[x])]


def move_shapes(argv):
    J = json.load(gzip.open(argv[1])); limit = int(argv[2]) if len(argv) > 2 else None
    C = collections.Counter(); nprof = 0; ex = []
    for h in J['hypergraphs']:
        seen = set()
        for st in h['starts']:
            key = json.dumps(st['vals'])
            if key in seen: continue
            seen.add(key); nprof += 1
            if limit and nprof > limit: break
            P = R.Prof(h['sets'], st['vals']); nu, Ms = P.max_matchings()
            rs = {M: sum(P.ranks(M)) for M in Ms}; best = min(rs.values())
            for Y in [M for M in Ms if rs[M] == best]:
                if P.oc1(Y) != 'M': continue
                beta = beta_min(P, Y); ro = P.roles(Y); J_ = set(ro['J'])
                tightDT = [x for x in ro['DT'] if min(P.rank(x, g) - P.rank(x, Y[x]) for g in P.rel[x] if g in J_) == beta[Y[x]]]
                B = [frozenset([g]) for g in Y]
                shapes = set()
                for nb in P.moves(B):
                    if P.one_absorber(list(nb)) is None: continue
                    ch = [i for i in range(P.n) if nb[i] != B[i]]
                    x0 = [i for i in ch if not (nb[i] & set(Y))]       # agents now holding junk only
                    desc = []
                    for i in ch:
                        gone = Y[i] not in nb[i]; took = sorted(set(nb[i]) - {Y[i]})
                        desc.append((i, 'drops pick' if gone else 'keeps pick', tuple(took)))
                    on_tight = all(i in tightDT or any(i in tight_in(P, Y, beta, x) for x in tightDT) for i in ch)
                    kind = 'addition' if len(ch) == 1 else ('x0 = tight DT' if any(i in tightDT and not (nb[i] & set(Y)) for i in ch) else 'other')
                    shapes.add((kind, 'changed agents on the tight structure' if on_tight else 'off it'))
                for s in shapes: C[s] += 1
                C['M starts'] += 1
                if len(ex) < 4: ex.append((h['list'], h['idx'], st['vals'], Y, tightDT, sorted(shapes)))
    print('profiles', nprof)
    for k, v in sorted(C.items(), key=str): print(' ', v, k)
    for e in ex: print('  ex', e)


if __name__ == '__main__' and len(sys.argv) > 3 and sys.argv[3] == 'shapes':
    move_shapes(sys.argv)
