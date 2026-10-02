#!/usr/bin/env python3
"""Report on one profile for Theorem ZMOVE (workstream compute/k4-zmove): both implementations' verdicts per key with
def* > 0, and, for the failing keys (or every key with --all), DL on the key graph (DLKey) there. EVIDENCE tooling.

Per key: def*, the Z′-maxima with def(P_Q), the best one-move repair from each P_Q and its move, the margin, the (T4)
verdict, by k4/zmove_check.py and k4/zmove_indep.py (they must agree). DLKey at κ: every (T3⁺) move with <= 1 helper
(PR #80's KeyProfile.t3plus_moves) and every (T4) move from every state of κ to a min-frozen state whose key has
smaller def*, summarized by the least |W| and helper use, with one witness per class (from which state, def of that
state, the target state, its def and its key's def*); and the descent chain: the least number of key-graph steps
(edges to a key of smaller def*, (T3⁺) with <= 1 helper or (T4)) from κ to a key with def* <= 0.
usage: python3 k4/zmove_failure.py '{"sets": ..., "vals": ..., "m": ...}' [--all]"""
import collections, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import zmove_check as ZC
import zmove_indep as ZI
from f2_lib import lst
from sx_keygraph import keyof


def edges(kp, k):
    """the key-graph edges out of k to keys of smaller def*: [(class, |W|, helper?, state, target, k2)]"""
    out = []
    ds = kp.dstar[k]
    for Bs in kp.K[k]:
        for b2, x, z, W, h in kp.t3plus_moves(Bs):
            k2 = keyof(kp.PA[b2])
            if kp.dstar[k2] < ds:
                out.append(('T3' if not W else 'T3+W%d' % len(W), len(W), h is not None, Bs, b2, k2, x, z, W, h))
        if kp.I.f >= 2:
            for b2 in kp.t4_moves(Bs):
                k2 = keyof(kp.PA[b2])
                if k2 != k and kp.dstar[k2] < ds:
                    out.append(('T4', 0, False, Bs, b2, k2, None, None, (), None))
    return out


def chain(kp, k):
    """least number of descending key-graph steps from k to a key with def* <= 0 (None if none)"""
    if kp.dstar[k] <= 0: return 0
    memo = {}

    def rec(k):
        if kp.dstar[k] <= 0: return 0
        if k in memo: return memo[k]
        memo[k] = None
        best = None
        for e in edges(kp, k):
            r = rec(e[5])
            if r is not None and (best is None or r + 1 < best): best = r + 1
        memo[k] = best
        return best
    return rec(k)


def main(argv):
    d = json.loads([a for a in argv if not a.startswith('--')][0])
    d = {'sets': d['sets'], 'vals': d['vals'], 'm': d.get('m') or 1 + max(map(max, d['sets']))}
    rec, kp = ZC.check_profile(d, {'fmin': 1, 'fmax': 99, 'all': True, 'verify_now': True})
    print('profile:', json.dumps(d))
    if 'keys' not in rec: print('skipped:', rec.get('skip')); return
    print('n = %d, f = %d, omega = %d; min-frozen states %d, keys %d, with def* > 0: %d (deficits checked against '
          'model.py)' % (rec['n'], rec['f'], rec['omega'], len(kp.mp), len(kp.K), len(rec['keys'])))
    ind = ZI.zmove(d['sets'], d['vals'], d['m'])
    print('second implementation (k4/zmove_indep.py):', ZC.compare_indep(d, rec))
    for kr in rec['keys']:
        k = tuple(kr['key'])
        print('\nkey %s: def* %d, %d states, %d configurations, %d maxima (%d distinct P_Q)' % (
            kr['key'], kr['dstar'], kr['states'], kr['nconf'], kr['nmax'], len(kr['maxima'])))
        for mr in kr['maxima']:
            print('  P_Q %s def %s: best one-move def %s, repairing moves %s; a best move %s' % (
                mr['PQ'], mr['defPQ'], mr['best'], mr['kinds'], mr['move']))
        t = ind['keys'][k]
        print('  margin %s (indep %s), margin_U %s, margin over all configurations %s; (T4) edge to smaller def*: %s '
              '(indep %s); ZMOVE %s' % (kr['margin'], ZC.jv(t['margin']), kr['margin_U'], kr['margin_all'], kr['t4edge'],
                                        t['t4edge'], 'holds' if kr['pass'] else 'FAILS'))
        if kr['pass'] and '--all' not in argv: continue
        es = edges(kp, k)
        cl = collections.Counter((e[0] + ('+helper' if e[2] else '')) for e in es)
        print('  DLKey at this key: %s; edges to smaller def* by class: %s' % ('holds' if es else 'FAILS', dict(cl)))
        best = {}
        for e in es:
            c = e[0] + ('+helper' if e[2] else '')
            if c not in best or kp.D[e[4]] < kp.D[best[c][4]]: best[c] = e
        for c, e in sorted(best.items()):
            print('    %s: from %s (def %d) to %s (def %d, key %s with def* %d); x %s z %s W %s helper %s' % (
                c, lst(e[3]), kp.D[e[3]], lst(e[4]), kp.D[e[4]], list(e[5]), kp.dstar[e[5]], e[6], e[7], list(e[8]), e[9]))
        print('  least descending key-graph chain to def* <= 0: %s step(s)' % chain(kp, k))


if __name__ == '__main__':
    main(sys.argv[1:])
