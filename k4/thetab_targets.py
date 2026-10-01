#!/usr/bin/env python3
"""The target states of k4/dl13.md §6 item 2 and their repairs (workstream proof/k4-thetab; k4/thetab.md §1, §3).

Reads PR #75's dumps of T1-stuck states (results/k4_dl13_stuck/stuck_*.jsonl.gz; every improving (T3) move is listed
there), keeps the T3-stage states that C1, C2, C3 of k4/dl13.md §4 do not certify, and reports:
  - the classes (S1 theta-b / S1 theta-a / no S1 shape) by f and number of needers (k4/dl13.md §6 item 2: 1,242 theta-b,
    1,199 of them at f = 1 with several needers; 22 + 77 without an S1 shape);
  - at f = 1: the types of the needers and of x (setting (H): two needers, both big-top);
  - the shapes of the improving (T3) moves of the dump: helper or none, which needer swaps, who owns afterwards;
  - Lemma G (k4/thetab_lib.swap_bound) at every no-helper swap: its bound is asserted against the exact deficit, and
    each target is classified by the first mode that certifies it: W1 (a pair A meeting L_{y_i}: no edge of y_i or x),
    K (kappa = 1), S (any other), with "quiet" when every other free agent's edges are met by its own slots;
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
            # f >= 2 (k4/thetab.md §6): Lemma G at any f, plain swaps of a frozen x with a free needer z
            plain = any(mv['h'] is None for mv in r['t3'])
            cert = False
            for x in range(I.n):
                if not P.frozen[x]: continue
                for z in ctx.free_needers(x):
                    for A in ctx.admissible(x, P.J | Bs[z]):
                        b2 = ctx.new(x, z, A)
                        for o in P.free:
                            if o == z: continue
                            bd = swap_bound_any_f(ctx, x, z, A, o)
                            if bd is None: continue
                            assert pr.D[b2] <= bd, ('Lemma G (any f) violated', r['src'], x, z, A, o)
                            if bd < ctx.D: cert = True
            cnt[('f>=2', cls, 'a plain swap lowers def' if plain else 'NO plain swap',
                 'Lemma G certifies one' if cert else 'Lemma G certifies none')] += 1
            continue
        x, g, nd, third = setting(ctx)
        typ = '+'.join(sorted(ntype(I, y) for y in nd))
        cnt[('f=1', cls, 'n=%d' % I.n, 'needers %s' % typ, 'x ' + ntype(I, x))] += 1
        # the improving (T3) moves of the dump
        shapes = set()
        for mv in r['t3']:
            B2 = tup(mv['Bs'])
            for o2 in best_owners(pr.OWN[B2]):
                who = 'x' if o2 == mv['x'] else ('helper' if o2 == mv['h'] else (
                    'other needer' if o2 in nd else 'third agent'))
                shapes.add(('helper' if mv['h'] is not None else 'no helper', who))
        if not any(s[0] == 'no helper' for s in shapes): cnt[('f=1', cls, 'every repair has a helper')] += 1
        for s in shapes: cnt[('f=1', cls, 'some repair:') + s] += 1
        # Theorem W: its hypotheses, and its construction where they hold
        bad = gw1_hyp(ctx)
        cnt[('f=1', cls, 'n=%d' % I.n, 'Theorem W hypotheses', 'hold' if not bad else '; '.join(bad))] += 1
        if not bad:
            zA = w1_construction(ctx)
            assert zA is not None, ('Theorem W: no construction', r['src'])
            z, A = zA
            b2 = ctx.new(x, z, A)
            assert pr.D[b2] <= pc(A) - 2 and pr.D[b2] < ctx.D, ('Theorem W violated', r['src'], z, A, pr.D[b2])
        ks = k_swaps(ctx); ss = s_swaps(ctx); gs = g1_swaps(ctx)
        for z, A, o in gs:
            b2 = ctx.new(x, z, A)
            assert pr.D[b2] <= 0, ('Corollary G1 violated', r['src'], z, A, o, pr.D[b2])
        for z, A in ks + ss:
            b2 = ctx.new(x, z, A)
            assert pr.D[b2] <= 0, ('Theorem K/S violated', r['src'], z, A, pr.D[b2])
        thm = 'W' if not bad else ('K' if ks else ('G1' if gs else ('S' if ss else 'none')))
        cnt[('f=1', cls, 'n=%d' % I.n, 'first theorem', thm)] += 1
        # Lemma G at every no-helper swap, owner every free agent other than z
        modes = set()
        for z in nd:
            for A in swaps(ctx, z):
                b2 = ctx.new(x, z, A)
                for o in P.free:
                    if o == z: continue
                    sb = swap_bound(ctx, z, A, o)
                    if sb['best'] is None: continue
                    assert pr.D[b2] <= sb['best'], ('Lemma G bound violated', r['src'], z, A, o)
                    if sb['best'] < ctx.D:
                        if sb['ez'] == 0 and sb['ex'] == 0 and pc(A) == 2: md = 'W1'
                        elif sb['kappa_h'] is not None and sb['kappa_h'] - sb['capx'] - sb['S_rest'] - 1 < ctx.D \
                                and not (sb['h0'] is not None and sb['h0'] - sb['capx'] - sb['S_rest'] < ctx.D):
                            md = 'K'
                        else: md = 'S'
                        role = 'other needer' if o in nd else 'third agent'
                        modes.add((md, 'quiet' if sb['quiet'] else 'loud', role))
        if not modes: cnt[('f=1', cls, 'Lemma G certifies no swap')] += 1
        else:
            first = sorted(modes, key=lambda t: (t[1] != 'quiet', ['W1', 'K', 'S'].index(t[0]), t[2]))[0]
            cnt[('f=1', cls, 'n=%d' % I.n, 'first Lemma G mode', first)] += 1
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
