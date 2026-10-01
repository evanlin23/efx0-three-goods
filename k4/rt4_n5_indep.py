#!/usr/bin/env python3
"""Independent checker of the n = 5 DL_RT4 failures, of DL on the key graph and of DL_RC (ledger rows K4.DL2.RT4,
K4.DL13.KEY, K4.DL2.RC). Written independently in the PR #86 audit (compute/k4-rt4-n5) by the auditor, from
k4/c4x.md §1, k4/dl2.md §3, the ledger's T4 / T3+ wording and k4/dl13.md §2.3; it shares no code with k4/dlrt4.c,
k4/dlrt4_ref.py (k4/suite/model.py), k4/rt4_n5_xcheck.py or k4/c4x_check.py, and imports nothing from the repository.
EVIDENCE tooling.

Its own enumeration of the pre-allocations (bases of at most two goods inside R_i, pairwise disjoint; validity (V1)
junk outside NA and (V2) no two-good base meeting NA), needs, frozen agents, the removal-only deficit (owner o free,
X = B_o + (J minus C) threatening nobody, |C| minus the slots of the other free agents with o's needs taken from X),
keys, and the move kinds T1, T2, T3, T4 and T3+ of the ledger rows. It also asserts the identity |J| - S = omega at
every valid P (k4/c4x.md §1) and that every profile is strict. T2 has a 'generous' variant (changed agents free in P
only, not also in P'); the DL_RT4 verdicts use it, so they are if anything more lenient than k4/dlrt4.c's.

Committed from the auditor's scratch files mycheck.py (the single-instance report) and mycheck_all.py (the loop over
inst lists, which exec'd a text-patched copy of mycheck.py); here the same code is wrapped in functions so that both
modes share it. The definitions are unchanged; the outputs equal the audit's logs line for line.

usage:
  python3 k4/rt4_n5_indep.py                                  the report on rt4-n5m9-chain (P and the repair P')
  python3 k4/rt4_n5_indep.py --one REC.json [P P']            the report on one instance ({"sets", "vals"[, "m"]}), with
                                                              the state P and the repair P' as JSON lists of bases
  python3 k4/rt4_n5_indep.py INST.json ...                    per profile of each inst list (k4/dlrt4_ref.py format):
      f, min-frozen count, def > 0 states, DL_RT4 failures, DL_RC failures, keys, keys with def* > 0, key-graph DL
      failures with T3/T4 edges and with T3+/T4 edges; then the totals and the nearest shapes of the DL_RT4 failures
Log: results/k4_rt4/indep_n5_failures.log."""
import itertools, sys, json, collections
from collections import Counter


def analyse(sets, vals, m=None):
    """the auditor's definitions on one profile (mycheck.py up to its instance-specific part); returns its namespace"""
    if m is None: m = 1 + max(max(S) for S in sets)
    n = len(sets)
    v = [dict(zip(S, V)) for S, V in zip(sets, vals)]

    # strictness: all nonempty subset sums distinct, per agent
    for i in range(n):
        sums = [sum(c) for r in range(1, len(vals[i]) + 1) for c in itertools.combinations(vals[i], r)]
        assert len(sums) == len(set(sums)), ('not strict', i)

    def val(i, B): return sum(v[i].get(g, 0) for g in B)

    def needs(i, B):
        b = val(i, B)
        return frozenset(g for g in sets[i] if g not in B and v[i][g] > b)

    # enumerate P: pairwise disjoint B_i subset R_i, |B_i| <= 2
    opts = [[frozenset()] + [frozenset([g]) for g in S] + [frozenset(c) for c in itertools.combinations(S, 2)] for S in sets]
    allP = []

    def rec(i, used, cur):
        if i == n:
            allP.append(tuple(cur)); return
        for B in opts[i]:
            if B & used: continue
            rec(i + 1, used | B, cur + [B])
    rec(0, frozenset(), [])

    def info(P):
        N = [needs(i, P[i]) for i in range(n)]
        NA = frozenset().union(*N)
        J = frozenset(range(m)) - frozenset().union(*P)
        fz = [len(B) == 1 and B <= NA for B in P]
        return N, NA, J, fz

    valid = []
    for P in allP:
        N, NA, J, fz = info(P)
        if J & NA: continue                                       # V1
        if any(len(B) == 2 and B & NA for B in P): continue        # V2
        valid.append(P)

    def deficit(P):
        N, NA, J, fz = info(P)
        S = sum(2 - len(P[i]) for i in range(n) if not fz[i])
        if len(J) - S <= 0: return len(J) - S
        best = None
        Jl = sorted(J)
        for o in range(n):
            if fz[o]: continue
            for r in range(len(Jl) + 1):
                for C in itertools.combinations(Jl, r):
                    X = P[o] | (J - frozenset(C))
                    # threatens nobody: for all x != o, max_h v_x(X \ h) <= v_x(B_x)
                    bad = False
                    for x in range(n):
                        if x == o or not X: continue
                        vx = val(x, X)
                        if vx - min(v[x].get(h, 0) for h in X) > val(x, P[x]): bad = True; break
                    if bad: continue
                    No = frozenset(g for g in sets[o] if g not in X and v[o][g] > val(o, X))
                    NAX = frozenset().union(*[N[i] for i in range(n) if i != o]) | No
                    So = sum(2 - len(P[i]) for i in range(n) if i != o and not (len(P[i]) == 1 and P[i] <= NAX))
                    c = len(C) - So
                    if best is None or c < best: best = c
        return float('inf') if best is None else best

    nf = {P: sum(info(P)[3]) for P in valid}
    f = min(nf.values())
    mf = [P for P in valid if nf[P] == f]
    D = {P: deficit(P) for P in mf}
    sigma = 2 * n - m
    # identity |J| - S = omega at every valid P (c4x.md §1)
    for P in valid:
        N, NA, J, fz = info(P)
        S = sum(2 - len(P[i]) for i in range(n) if not fz[i])
        assert len(J) - S == sum(fz) - sigma

    def classify(P, Q, generous=False):
        """the kinds of the move P -> Q, as a set of names"""
        N1, NA1, J1, f1 = info(P); N2, NA2, J2, f2 = info(Q)
        ch = [i for i in range(n) if P[i] != Q[i]]
        U = [i for i in ch if f1[i] and not f2[i]]; Z = [i for i in ch if f2[i] and not f1[i]]
        W = [i for i in ch if f1[i] and f2[i]]; Y = [i for i in ch if not f1[i] and not f2[i]]
        k = set()
        if not ch or NA1 != NA2: return k, (ch, U, W, Z, Y)
        # T1: one free agent re-bases
        if len(ch) == 1 and not f1[ch[0]]: k.add('T1')
        # T2: |ch| >= 2, all changed agents free in P (and in Q, code RTr); generous: free in P only
        if len(ch) >= 2 and all(not f1[i] for i in ch) and (generous or all(not f2[i] for i in ch)): k.add('T2')
        # T3: frozen x with {g}, free z with g in N_z(B_z), Q_z = {g}; at most one more agent h, free in P, giving up a good
        for x in ch:
            if not f1[x]: continue
            g = next(iter(P[x]))
            for z in ch:
                if z == x or f1[z] or Q[z] != P[x] or g not in N1[z]: continue
                rest = [i for i in ch if i not in (x, z)]
                if len(rest) <= 1 and all(not f1[h] and (P[h] - Q[h]) for h in rest): k.add('T3')
        # T4: every changed agent frozen in P and in Q
        if all(f1[i] and f2[i] for i in ch): k.add('T4')
        # T3+: one x in U, one z in Z, z needs its new good in P, |Y| <= 1 giving up a good, bases of W+z in Q == W+x in P
        if len(U) == 1 and len(Z) == 1 and len(Y) <= 1 and all(P[y] - Q[y] for y in Y):
            if sorted(sorted(Q[i]) for i in W + Z) == sorted(sorted(P[i]) for i in W + U) and Q[Z[0]] <= N1[Z[0]]:
                k.add('T3+')
        return k, (ch, U, W, Z, Y)

    return dict(n=n, m=m, valid=valid, f=f, sigma=sigma, mf=mf, D=D, info=info, classify=classify)


def fs(*bs): return tuple(frozenset(b) for b in bs)
def show(P): return '(' + ', '.join('{' + ','.join(map(str, sorted(B))) + '}' for B in P) + ')'


def report(ns, P, P2):
    """mycheck.py's instance-specific part: P, the repair P', P's better states and move kinds, every def > 0 state, keys"""
    n, valid, f, sigma, mf, D, info, classify = (ns[k] for k in ('n', 'valid', 'f', 'sigma', 'mf', 'D', 'info', 'classify'))
    print('valid P:', len(valid), '; f =', f, '; omega =', f - sigma, '; min-frozen:', len(mf), '; with def > 0:', sum(1 for P_ in mf if D[P_] > 0))
    for name, X in (('P', P), ("P'", P2)):
        N, NA, J, fz = info(X)
        print(name, show(X), 'valid', X in valid, 'min-frozen', X in D, 'frozen', [i for i in range(n) if fz[i]],
              'NA', sorted(NA), 'J', sorted(J), 'def', D.get(X))
    better = [Q for Q in mf if D[Q] < D[P]]
    dist = lambda A, B: sum(1 for a, b in zip(A, B) if a != b)
    print('better states:', len(better), 'by distance:', dict(sorted(Counter(dist(P, Q) for Q in better).items())))
    kinds = Counter(); kinds_g = Counter()
    for Q in better:
        k, cls = classify(P, Q); kg, _ = classify(P, Q, generous=True)
        for t in k: kinds[t] += 1
        for t in kg: kinds_g[t] += 1
    print('better states reached by move kind:', dict(kinds), '; with T2 generous (free in P only):', dict(kinds_g))
    print('RT4 move to a better state exists:', any(classify(P, Q, True)[0] & {'T1', 'T2', 'T3', 'T4'} for Q in better))
    near = [Q for Q in better if dist(P, Q) == 3]
    shapes = Counter()
    for Q in near:
        k, (ch, U, W, Z, Y) = classify(P, Q)
        chain = len(U) == len(W) == len(Z) == 1 and not Y and Q[W[0]] == P[U[0]] and Q[Z[0]] == P[W[0]] and info(P)[1] == info(Q)[1]
        shapes[(len(U), len(W), len(Z), len(Y), chain, 'T3+' in k)] += 1
    print('distance-3 better states:', len(near), 'shapes (U,W,Z,Y,chain,T3+):', dict(shapes))
    k, cls = classify(P, P2)
    print("P -> P' kinds:", k, 'ch,U,W,Z,Y =', cls)

    # all def > 0 states: DL_RT4 and DL_RC
    st = [X for X in mf if D[X] > 0]
    rt4f = []; rcf = []
    for X in st:
        ks = set()
        for Q in mf:
            if D[Q] < D[X]: ks |= classify(X, Q)[0]
        if not ks & {'T1', 'T2', 'T3', 'T4'}: rt4f.append(X)
        if not ks & {'T1', 'T2', 'T3+', 'T4'}: rcf.append(X)
    print('def > 0 states:', len(st), '; DL_RT4 fails at', [show(X) for X in rt4f], '; DL_RC fails at', len(rcf))

    # key graph
    def key(X):
        N, NA, J, fz = info(X)
        return (NA, tuple(X[i] if fz[i] else None for i in range(n)))
    K = {}
    for X in mf: K.setdefault(key(X), []).append(X)
    dstar = {kk: min(D[X] for X in Xs) for kk, Xs in K.items()}
    pos = [kk for kk in K if dstar[kk] > 0]
    kf = []; kfp = []
    for kk in pos:
        e1 = e2 = False
        for X in K[kk]:
            for Q in mf:
                kq = key(Q)
                if kq == kk or dstar[kq] >= dstar[kk]: continue
                ks = classify(X, Q)[0]
                e1 |= bool(ks & {'T3', 'T4'}); e2 |= bool(ks & {'T3', 'T3+', 'T4'})
        if not e1: kf.append(kk)
        if not e2: kfp.append(kk)
    print('keys:', len(K), 'with def* > 0:', len(pos), '; key-graph DL (T3/T4 edges) fails at',
          [(sorted(kk[0]), {i: sorted(b) for i, b in enumerate(kk[1]) if b is not None}, dstar[kk]) for kk in kf],
          '; with T3+/T4 edges fails at', len(kfp))
    print('key of P:', sorted(key(P)[0]), {i: sorted(b) for i, b in enumerate(key(P)[1]) if b is not None}, 'def*', dstar[key(P)])


def totals(files):
    """mycheck_all.py: every profile of the inst lists, with the totals and the nearest shapes of the DL_RT4 failures"""
    tot = collections.Counter(); shapes = collections.Counter()
    for fn in files:
        for e in json.load(open(fn)):
            ns = analyse(e['sets'], e['vals'], e['m'])
            mf, D, classify, info, n = ns['mf'], ns['D'], ns['classify'], ns['info'], ns['n']
            st = [X for X in mf if D[X] > 0]
            rt4f = rcf = 0; near = 0
            for X in st:
                ks = set(); better = [Q for Q in mf if D[Q] < D[X]]
                for Q in better: ks |= classify(X, Q, True)[0]
                if not ks & {'T1', 'T2', 'T3', 'T4'}:
                    rt4f += 1
                    dist = min(sum(1 for a, b in zip(X, Q) if a != b) for Q in better)
                    for Q in better:
                        if sum(1 for a, b in zip(X, Q) if a != b) != dist: continue
                        k, (ch, U, W, Z, Y) = classify(X, Q)
                        chain = len(U) == len(W) == len(Z) == 1 and not Y and Q[W[0]] == X[U[0]] and Q[Z[0]] == X[W[0]]
                        shapes[(D[X], dist, len(U), len(W), len(Z), len(Y), chain, 'T3+' in k)] += 1; near += 1
                if not ks & {'T1', 'T2', 'T3+', 'T4'}: rcf += 1

            def kf(X):
                N, NA, J, fz = info(X)
                return (NA, tuple(X[i] if fz[i] else None for i in range(n)))
            K = {}
            for X in mf: K.setdefault(kf(X), []).append(X)
            ds = {k: min(D[X] for X in Xs) for k, Xs in K.items()}
            pos = [k for k in K if ds[k] > 0]
            f1 = f2 = 0
            for k in pos:
                e1 = e2 = False
                for X in K[k]:
                    for Q in mf:
                        kq = kf(Q)
                        if kq == k or ds[kq] >= ds[k]: continue
                        ks = classify(X, Q)[0]
                        e1 |= bool(ks & {'T3', 'T4'}); e2 |= bool(ks & {'T3', 'T3+', 'T4'})
                f1 += not e1; f2 += not e2
            print('%s f=%d min-frozen=%d states=%d RT4fail=%d RCfail=%d keys=%d pos=%d keyfail=%d keyplusfail=%d' % (
                e['id'], ns['f'], len(mf), len(st), rt4f, rcf, len(K), len(pos), f1, f2), flush=True)
            for c, x in (('profiles', 1), ('states', len(st)), ('rt4', rt4f), ('rc', rcf), ('keys', len(K)), ('pos', len(pos)),
                         ('kf', f1), ('kfp', f2), ('near', near)): tot[c] += x
    print('TOTAL', dict(tot))
    print('nearest shapes (def, dist, |U|, |W|, |Z|, |Y|, chain, T3+):', dict(shapes))


def main(argv):
    if argv and argv[0] == '--one':
        d = json.load(open(argv[1]))
        ns = analyse(d['sets'], d['vals'], d.get('m'))
        P, P2 = (fs(*json.loads(argv[2])), fs(*json.loads(argv[3]))) if len(argv) > 3 else (
            fs({7}, {8}, {3}, {5}, {6}), fs({0}, {8}, {3}, {6}, {7}))
        report(ns, P, P2)
    elif argv:
        totals(argv)
    else:                                   # rt4-n5m9-chain
        sets = [[0, 2, 4, 7], [1, 4, 7, 8], [3, 6, 8], [5, 6, 7, 8], [5, 6, 7, 8]]
        vals = [[6, 3, 5, 7], [4, 2, 8, 7], [2, 4, 3], [4, 8, 1, 6], [2, 7, 8, 4]]
        report(analyse(sets, vals), fs({7}, {8}, {3}, {5}, {6}), fs({0}, {8}, {3}, {6}, {7}))


if __name__ == '__main__':
    main(sys.argv[1:])
