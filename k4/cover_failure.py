#!/usr/bin/env python3
"""Detail of a key that COVER / COVER⁺ leaves uncovered (workstream compute/k4-cover). EVIDENCE tooling.

For one profile and each of its keys with def* > 0 that k4/cover_check.py finds uncovered: every maximum of (r′, Λ′),
P_Q and def(P_Q), the leaves and the agents each leaf's bundle threatens, PR #80's sx_f2 obstruction counters (why A⁺
and B⁺ fail), PR #82's f2_cc obstruction counters (C′⁺ bundles with no counted good), every move of (T3), (T3⁺), (T4)
from P_Q to a state of smaller deficit than def*, and the same from every state of the key (DLKey), each with the
deficit by k4/rt4_n5_indep.py (no repository code) and its move kinds by that file's classify.

usage: python3 k4/cover_failure.py '{"sets": ..., "vals": ..., "m": ...}'"""
import collections, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cover_check as CC
import rt4_n5_indep as R
from f2_lib import Prof, lst
from model import bits, pc, mask


def fs(Bs): return tuple(frozenset(bits(B)) for B in Bs)


def main(argv):
    d = json.loads(argv[0]); d.setdefault('m', 1 + max(map(max, d['sets'])))
    rec = CC.check_profile(d, {'fmin': 1, 'fmax': 99, 'verify': True, 'dlk': True})
    pr = Prof(d, fmin=1); kp = CC.f2_cc.keyprofile(pr); I = pr.I
    ns = R.analyse(d['sets'], d['vals'], d['m'])
    print('profile', json.dumps(d)); print('core violations', I.core_violations(), 'strict', I.strict())
    print('n=%d m=%d f=%d omega=%d; keys %d, with def* > 0: %d' % (I.n, I.m, I.f, I.omega, len(kp.K), len(rec['keys'])))
    for kr in rec['keys']:
        k = tuple(kr['key'])
        print('\nkey %s def* %d (rt4_n5_indep: %s) states %d covered %s %s' % (
            kr['key'], kr['dstar'], min(ns['D'][fs(b)] for b in kp.K[k]), kr['states'], kr['covered'], kr['cover']))
        if kr['covered']: continue
        for c, Bs, V, X in CC.f2_cc.maxima(kp, k):
            print('  maximum Q=%s' % repr(c))
            print('    P_Q = %s def %s (rt4_n5_indep %s)' % (lst(Bs), kp.D[Bs], ns['D'][fs(Bs)]))
            for o in c.free:
                thr = [w for w in range(I.n) if w != o and I.threat(w, X[o], c.hv(w))]
                print('    free %d: Q=%s H=%s robust=%s leaf=%s X=%s threatens %s needs %s' % (
                    o, sorted(bits(c.Q[o])), sorted(bits(Bs[o])), c.robust(o), o in V, sorted(bits(X[o])), thr,
                    sorted(bits(kp.PA[Bs].N[o]))))
            for x in c.frozen:
                print('    frozen %d on %d: needs %s; needers of its good: %s' % (
                    x, k[x], sorted(bits(kp.PA[Bs].N[x])), [i for i in range(I.n) if kp.PA[Bs].N[i] & Bs[x]]))
            cnt = CC.one_max(I, c, CC.sx_f2.analyse_key, kp, k) if I.f >= 2 else CC.one_max(
                I, c, CC.sx_zprime.analyse_key, kp, k, CC._NB())
            for key in sorted(cnt):
                if cnt[key] and (key.startswith('no A+') or 'A+' in key or 'B+' in key or 'direct' in key or 'cases' in key):
                    print('    PR #80 counter: %s = %d' % (key, cnt[key]))
            applied, why = CC.f2_cc.test_max(pr, c, Bs, V, X, collections.Counter(), None)
            print('    PR #82 test_max: applied %s' % sorted(map(str, applied)))
            for w, v in sorted(why.items()): print('    PR #82 obstruction: %s = %d' % (' | '.join(w), v))
            mv = [(b2, x, z, W, h) for b2, x, z, W, h in kp.t3plus_moves(Bs) if kp.D[b2] < kr['dstar']]
            print('    improving (T3)/(T3+) moves from P_Q: %d' % len(mv))
            for b2, x, z, W, h in mv[:12]:
                ks, _ = ns['classify'](fs(Bs), fs(b2))
                print('      x=%d z=%d W=%s helper=%s -> %s def %d (indep def %s, kinds %s)' % (
                    x, z, list(W), h, lst(b2), kp.D[b2], ns['D'][fs(b2)], sorted(ks)))
            if I.f >= 2:
                for b2 in kp.t4_moves(Bs):
                    if kp.D[b2] < kr['dstar']: print('      T4 -> %s def %d' % (lst(b2), kp.D[b2]))
        print('  DLKey over every state of the key: %s' % kr.get('dlkey'))
        for Bs in kp.K[k]:
            mv = [(b2, x, z, W, h) for b2, x, z, W, h in kp.t3plus_moves(Bs) if kp.dstar[CC.keyof(kp.PA[b2])] < kr['dstar']]
            best = min(mv, key=lambda t: (len(t[3]), t[4] is not None, kp.D[t[0]])) if mv else None
            print('    state %s def %d: %d key-improving (T3)/(T3+) moves%s' % (
                lst(Bs), kp.D[Bs], len(mv), '' if not best else '; e.g. x=%d z=%d W=%s helper=%s -> %s def %d (indep %s)' % (
                    best[1], best[2], list(best[3]), best[4], lst(best[0]), kp.D[best[0]], ns['D'][fs(best[0])])))


if __name__ == '__main__':
    main(sys.argv[1:])
