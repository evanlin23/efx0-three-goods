#!/usr/bin/env python3
"""DL_RC with a relaxed helper, on k4/rt4_n5_indep.py's model (compute/k4-rc-refute; ledger rows K4.DL2.RC,
K4.DL2.RCY, K4.DL2.RCKEY). EVIDENCE tooling.

Uses only `analyse` of k4/rt4_n5_indep.py (the PR #86 auditor's checker, which imports nothing from the repository):
its enumeration of the valid pre-allocations, the min-frozen class, the removal-only deficit, needs, NA and frozen
agents, and its move descriptor `classify` (the kinds T1, T2, T3, T4, T3+ and the sets ch, U, W, Z, Y). Nothing
from k4/dlrc.c, k4/dlrc_ref.py, k4/portfolio_*.py or k4/suite/model.py. For every min-frozen state X with def > 0 of
each profile and every min-frozen Q with def(Q) < def(X), it tests the move X -> Q against:

  RC     T1, T2 (generous), T3+ or T4 of `classify` (as rt4_n5_indep.py's DL_RC verdict)
  RCY    RC with T3+'s helper unrestricted: NA kept, |U| = |Z| = 1, |Y| <= 1 (the helper need not give up a good),
         z needs its new good in X, and the bases of W + Z in Q are exactly the bases of W + U in X
         (portfolio predicate RC_Yfree of compute/k4-portfolio)
  RCY0   the same T3+ with an unrestricted helper, or ANY move keeping NA with U empty (weaker than RCY: every T1, T2,
         T4 move and every union of them); RCY0 failing implies RCY failing, whatever reading of T2 is taken
  RCany  RC with T3+ allowing any number of helpers, each giving up a good (portfolio predicate RC_Yany)

and prints per profile the states, the failures of each, and the shapes (|U|, |Z|, |W|, |Y|, every helper gives) of
the nearest better states at the RCY failures; then the totals.

  python3 k4/rcy_indep.py INST.json ...        (JSON lists of {"id", "sets", "vals", "m"})
"""
import collections, json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rt4_n5_indep import analyse


def t3plus(X, Q, info, U, W, Z, Y, ymax=1, give=True):
    N1, NA1, _, _ = info(X)
    if NA1 != info(Q)[1] or len(U) != 1 or len(Z) != 1 or len(Y) > ymax: return False
    if give and not all(X[y] - Q[y] for y in Y): return False
    if not Q[Z[0]] <= N1[Z[0]]: return False
    return sorted(sorted(Q[i]) for i in W + Z) == sorted(sorted(X[i]) for i in W + U)


def profile(e):
    ns = analyse(e['sets'], e['vals'], e.get('m'))
    mf, D, classify, info = ns['mf'], ns['D'], ns['classify'], ns['info']
    st = [X for X in mf if D[X] > 0]
    fails = collections.Counter(); shapes = collections.Counter(); bad = []
    for X in st:
        ok = collections.Counter()
        better = [Q for Q in mf if D[Q] < D[X]]
        for Q in better:
            kinds, (ch, U, W, Z, Y) = classify(X, Q, True)
            keep = info(X)[1] == info(Q)[1]
            rc = bool(kinds & {'T1', 'T2', 'T3+', 'T4'})
            ty = t3plus(X, Q, info, U, W, Z, Y, give=False)
            ok['RC'] += rc
            ok['RCY'] += rc or ty
            ok['RCY0'] += (keep and not U) or ty
            ok['RCany'] += rc or t3plus(X, Q, info, U, W, Z, Y, ymax=99)
        for name in ('RC', 'RCY', 'RCY0', 'RCany'):
            if not ok[name]: fails[name] += 1
        if not ok['RCY']:
            bad.append(X)
            dist = min(sum(1 for a, b in zip(X, Q) if a != b) for Q in better)
            for Q in better:
                if sum(1 for a, b in zip(X, Q) if a != b) != dist: continue
                _, (ch, U, W, Z, Y) = classify(X, Q, True)
                shapes[(dist, len(U), len(Z), len(W), len(Y), all(X[y] - Q[y] for y in Y))] += 1
    return ns['f'], len(mf), len(st), fails, shapes, bad


def main(files):
    tot = collections.Counter(); tsh = collections.Counter()
    for fn in files:
        for e in json.load(open(fn)):
            f, nmf, nst, fails, shapes, bad = profile(e)
            print('%s f=%d min-frozen=%d states=%d fails: RC=%d RCY=%d RCY0=%d RCany=%d' % (
                e['id'], f, nmf, nst, fails['RC'], fails['RCY'], fails['RCY0'], fails['RCany']), flush=True)
            for X in bad[:4]:
                print('   RCY fails at', '(' + ', '.join('{' + ','.join(map(str, sorted(B))) + '}' for B in X) + ')')
            tot['profiles'] += 1; tot['states'] += nst
            for k, v in fails.items(): tot[k] += v
            tsh.update(shapes)
    print('TOTAL', dict(tot))
    print('nearest better states at the RCY failures, (distance, |U|, |Z|, |W|, |Y|, every helper gives up a good): count',
          dict(sorted(tsh.items())))


if __name__ == '__main__':
    print('# command: python3 k4/rcy_indep.py ' + ' '.join(sys.argv[1:]), flush=True)
    main(sys.argv[1:])
