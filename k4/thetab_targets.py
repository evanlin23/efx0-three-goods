#!/usr/bin/env python3
"""The target states of k4/dl13.md §6 item 2 and their repairs (workstream proof/k4-thetab; k4/thetab.md §1, §4, §6).

Reads PR #75's dumps of T1-stuck states (results/k4_dl13_stuck/stuck_*.jsonl.gz; every improving (T3) move is listed
there), keeps the T3-stage states that C1, C2, C3 of k4/dl13.md §4 do not certify, and reports:
  - the classes (S1 theta-b / S1 theta-a / no S1 shape) by f (k4/dl13.md §6 item 2: 1,242 theta-b, 1,199 of them at
    f = 1 with several needers; 22 + 77 without an S1 shape), and the number of distinct states;
  - at f = 1: the types of the needers and of x (setting (H): two needers, both big-top);
  - the shapes of the improving (T3) moves of the dump: helper or none, who owns afterwards;
  - the first of Theorem W, Theorem K (k4/thetab.md §3), Corollary G1 with a plain swap ('G1') and Corollary G1 with
    one helper ('G1h') that applies, with the conclusions asserted against the exact deficits (W: def(P') <= |A| - 2;
    K and G1: def(P') <= 0; every Lemma G bound computed is asserted too);
  - at f >= 2: whether a plain swap lowers the deficit (from the dump) and whether Lemma G certifies one;
  - with --show: the smallest target of each class.
usage: python3 k4/thetab_targets.py [--show] [--f1] [--check]   (--check: every deficit also by k4/suite/model.py's direct
       removal-only test, asserted equal)"""
import sys
from thetab_lib import *


def main(argv):
    print('# command: python3 k4/thetab_targets.py ' + ' '.join(argv), flush=True)
    cnt = collections.Counter(); small = {}; distinct = set()
    f1 = '--f1' in argv
    for r, pr, ctx, cls in targets(fpred=(lambda r: r['f'] == 1) if f1 else None, check='--check' in argv):
        I, P, Bs = ctx.I, ctx.P, ctx.Bs
        cnt[('all', cls, 'f=%d' % r['f'])] += 1
        distinct.add((cls, r['f'], json.dumps([r['sets'], r['vals'], r['Bs']])))
        k = (cls, r['f'])
        if k not in small or (I.n, I.m) < small[k][0]: small[k] = ((I.n, I.m), r, ctx)
        if r['f'] != 1:
            plain = any(mv['h'] is None for mv in r['t3'])
            cert = bool(g_certificates(ctx, pr, plain_moves(ctx), ctx.D))
            cnt[('f>=2', cls, 'a plain swap lowers def' if plain else 'NO plain swap',
                 'Lemma G certifies one' if cert else 'Lemma G certifies none')] += 1
            continue
        x, g, nd, third = setting(ctx)
        typ = '+'.join(sorted(ntype(I, y) for y in nd))
        cnt[('f=1', cls, 'n=%d' % I.n, 'needers %s' % typ, 'x ' + ntype(I, x))] += 1
        shapes = set()
        for mv in r['t3']:
            B2 = tup(mv['Bs'])
            for o2 in best_owners(pr.OWN[B2]):
                who = 'x' if o2 == mv['x'] else ('helper' if o2 == mv['h'] else (
                    'other needer' if o2 in nd else 'third agent'))
                shapes.add(('helper' if mv['h'] is not None else 'no helper', who))
        if not any(s[0] == 'no helper' for s in shapes): cnt[('f=1', cls, 'every repair has a helper')] += 1
        for s in shapes: cnt[('f=1', cls, 'some repair:') + s] += 1
        bad = gw1_hyp(ctx)
        cnt[('f=1', cls, 'n=%d' % I.n, 'Theorem W hypotheses', 'hold' if not bad else '; '.join(bad))] += 1
        cnt[('f=1', cls, 'n=%d' % I.n, 'first theorem', theorems(pr, ctx, r['src']))] += 1
    for k in sorted(cnt, key=str): print('  %-100s %d' % (' | '.join(map(str, k)), cnt[k]))
    dc = collections.Counter((c, f) for c, f, _ in distinct)
    print('distinct states per (class, f):', ', '.join('%s f=%d: %d' % (c, f, v) for (c, f), v in sorted(dc.items())))
    print('smallest target per (class, f):')
    for k, ((n, m), r, ctx) in sorted(small.items(), key=str):
        print('  %s f=%d: n=%d m=%d %s sets=%s vals=%s P=%s' % (k[0], k[1], n, m, r['src'], r['sets'], r['vals'], r['Bs']))
        if '--show' in argv: show(r, ctx)
    print('no assertion failed')


if __name__ == '__main__':
    main(sys.argv[1:])
