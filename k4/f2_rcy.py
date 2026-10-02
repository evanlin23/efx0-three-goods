#!/usr/bin/env python3
"""The single-step DL_RC failures of compute/k4-rc at core 4515 (f = 2; states whose nearest better states need two
helpers or two agents unfrozen, K4.DL2.RCY), seen from Theorem Z′'s state P_Q of their keys (workstream proof/k4-f2,
k4/f2.md §7.2). EVIDENCE.

For every profile of compute/k4-rc's `results/k4_rc/rc_failures_4515_inst.json` (suite form, with `fail_bases`, the
failing states) and every failing state P: the key κ of P, def(P) and def*(κ), whether κ's frozen need digraph is
acyclic, and at the maxima Q of (r′, Λ′) at κ which of the lemmas applies at P_Q: Lemma A⁺ or Lemma B⁺ with a threat path
of length 1 (K4.SX.APLUS, through PR #80's k4/sx_f2.analyse_key), Lemma C⁺ or C′⁺ (K4.F2.CC), Lemma C⁺ₕ or C′⁺ₕ
(K4.F2.CCH) (k4/f2_cc.py, which asserts def(P′) <= 0 at every instance). "H1 alone" rows are a safe bundle of ω + 2
goods in P′ found by k4/f2_cc.py's general owner loop (owner as named), not one of the lemmas.
usage: python3 k4/f2_rcy.py RC_FAILURES_4515_INST.json [--src=TEXT]   (TEXT: where the input comes from, printed)"""
import collections, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import f2_cc
from f2_lib import Prof, tup, bits


def main(argv):
    print('# command: python3 k4/f2_rcy.py ' + ' '.join(argv), flush=True)
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    if 'src' in opt: print('# input: ' + opt['src'], flush=True)
    data = json.load(open([a for a in argv if not a.startswith('--')][0]))
    cnt = collections.Counter()
    for d in data:
        pr = Prof({'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}, fmin=2)
        assert pr.ok
        kp = f2_cc.keyprofile(pr)
        cnt['profiles'] += 1
        keys = {}
        for fb in d['fail_bases']:
            Bs = tup(fb)
            assert Bs in pr.D, ('not a min-frozen state', fb)
            P = pr.PA[Bs]
            k = tuple(next(bits(Bs[i])) if P.frozen[i] else None for i in range(pr.I.n))
            cnt['failing states'] += 1
            cnt[('failing state: def(P) - def*(key)', pr.D[Bs] - kp.dstar[k])] += 1
            keys[k] = pr.D[Bs]
        for k in keys:
            cnt['keys of failing states'] += 1
            cnt[('key', 'def*', kp.dstar[k])] += 1
            cnt[('key', 'frozen need digraph acyclic', f2_cc.acyclic(pr, k))] += 1
            if kp.dstar[k] <= 0:
                cnt[('key', 'def* <= 0: completable, nothing to repair')] += 1
                continue
            c1 = collections.Counter(); exs = collections.defaultdict(list)
            f2_cc.sx_f2.analyse_key(kp, k, c1, exs, 10 ** 6)
            aplus = any(c1[t] for t in c1 if t.startswith('A+ applies'))
            bplus1 = any(c1[t] for t in c1 if t.startswith('B+ applies') and t.endswith('path k=1'))
            mx = f2_cc.maxima(kp, k)
            cnt[('key', 'maxima')] += len(mx)
            names = set()
            if aplus: names.add('A+')
            if bplus1: names.add('B+ (k=1)')
            fails = set(tup(fb) for fb in d['fail_bases'])
            for t in mx:
                cnt[('maximum', 'P_Q is one of the failing states', t[1] in fails)] += 1
                cnt[('maximum', 'def(P_Q) - def*', pr.D[t[1]] - kp.dstar[k])] += 1
                app, _ = f2_cc.test_max(pr, *t, collections.Counter(), None)
                for a in app:
                    names.add(('H1 alone, a full bundle, ' + a[2] if a[0] == 'full' else a[0]) + ' (k=%d)' % a[1])
                if not app:
                    for a in f2_cc.test_helper(pr, *t):
                        names.add(a[0] + ' (k=%d)' % a[1])
            for nm in sorted(names): cnt[('key', 'applies at some maximum', nm)] += 1
            cnt[('key', 'some lemma without helper', bool(names - {n for n in names if n.startswith(("C+h", "C'+h"))}))] += 1
    for k in sorted(cnt, key=str):
        print('  %-90s %s' % (' | '.join(map(str, k)) if isinstance(k, tuple) else k, cnt[k]))
    print('# no assertion failed')


if __name__ == '__main__':
    main(sys.argv[1:])
