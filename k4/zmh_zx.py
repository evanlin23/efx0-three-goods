#!/usr/bin/env python3
"""The x-owner form of ZMOVE on data (workstream proof/k4-zmove-hall; k4/zmove_hall.md §1). EVIDENCE tooling,
k4/zmh_lib.py's model.

ZX: at a Z′-maximum Q of a key κ with def*(κ) > 0, some (T3⁺) move with at most one helper from P_Q reaches a P′ with
def(P′) <= 0 in which the unfrozen agent x is a best owner: Val_{P′}(x) >= ω + 2 (Lemma H1), i.e. x has a safe bundle Z
in P′ with |Z| + u′_x(Z) >= ω + 2. Restricted forms: W = ∅ (a (T3) move), no helper, both. Counted per maximum and per
key (some maximum / every maximum).

usage: python3 k4/zmh_zx.py [--every=E] [--max=N] [--fmin=F] INPUT ..."""
import collections, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zmh_lib import Prof, load_inputs, show

FORMS = ('ZMOVE', 'ZMOVE W=0', 'ZMOVE nohelper', 'ZMOVE nohelper W=0',
         'ZX', 'ZX W=0', 'ZX nohelper', 'ZX nohelper W=0')


def flags_at(pr, P):
    fl = set()
    for Q in pr.states:
        if pr.D[Q] > 0: continue
        k, (ch, U, Z, W, Y) = pr.move_kind(P, Q)
        if 'T3+' not in k: continue
        x = U[0]
        w0 = not W; nh = not Y
        fl.add('ZMOVE')
        if w0: fl.add('ZMOVE W=0')
        if nh: fl.add('ZMOVE nohelper')
        if w0 and nh: fl.add('ZMOVE nohelper W=0')
        v, _ = pr.owner_val(Q, x)
        if v >= pr.omega + 2:
            fl.add('ZX')
            if w0: fl.add('ZX W=0')
            if nh: fl.add('ZX nohelper')
            if w0 and nh: fl.add('ZX nohelper W=0')
    return fl


def main(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            kk, _, vv = a[2:].partition('='); opts[kk] = vv
        else: ins.append(a)
    every = int(opts.get('every', 1)); mx = int(opts.get('max', 10 ** 9)); fmin = int(opts.get('fmin', 1))
    maxn = int(opts.get('maxn', 99))
    cnt = collections.Counter(); idx = 0; shown = collections.Counter()
    seen = set()
    for path in ins:
        for rec in load_inputs(path):
            idx += 1
            if (idx - 1) % every: continue
            if len(rec['sets']) > maxn: continue
            sig = json.dumps([rec['sets'], rec['vals']])
            if sig in seen: continue
            seen.add(sig)
            if cnt['profiles'] >= mx: break
            cnt['profiles'] += 1
            pr = Prof(rec['sets'], rec['vals'], rec.get('m'))
            if pr.omega < 1 or pr.f < fmin: continue
            for key, ds in pr.dstar.items():
                if ds <= 0: continue
                cnt['keys, f=%d' % pr.f] += 1
                zs, best = pr.zmax_states(key)
                per = [flags_at(pr, P) for P in zs]
                for fl in per:
                    cnt['maxima, f=%d' % pr.f] += 1
                    for F in FORMS:
                        if F not in fl: cnt['maxima, f=%d, WITHOUT %s' % (pr.f, F)] += 1
                for F in FORMS:
                    if not any(F in fl for fl in per):
                        cnt['keys, f=%d, at no maximum: %s' % (pr.f, F)] += 1
                        if shown[F] < 2:
                            shown[F] += 1
                            print('no maximum with %s:' % F, json.dumps({'sets': pr.sets, 'vals': [[pr.v[i][h] for h in pr.sets[i]] for i in range(pr.n)], 'm': pr.m}),
                                  'key', [None if b is None else sorted(b.bit_length() - 1 for _ in [0]) for b in key],
                                  'maxima', [show(P) for P in zs], flush=True)
    for kk in sorted(cnt): print('%-55s %d' % (kk, cnt[kk]))


if __name__ == '__main__':
    main(sys.argv[1:])
