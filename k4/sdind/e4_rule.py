"""E4: deterministic move rules for the reverse-SD insertion (k4/sd_induct.md §3).

Insert pi_n, ..., pi_1; keep one completion X of the current sub-instance; at each insertion of f, choose the next X
among the one-absorber completions of the new sub-instance at Hamming distance <= 1 (or <= DMAX) from X by a rule:
  stay   : distance 0 if possible (f unthreatened);
  then, for a one-good move of junk good g from holder a to holder b (o = absorber of X), the key ranks:
    'f-first'   : b = f before helpers, goods from the absorber first, then by v_f(g) descending
    'f-low'     : b = f first, then v_f(g) ascending
    'helper'    : helpers before f
    'keepo'     : moves that keep pi_n the absorber first, then f-first
Report per rule: starts on which the rule reaches the end for SOME order producing Y, for EVERY order, and for the
first order.

    python3 k4/sdind/e4_rule.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time, os
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by
from e1_delete import load
from e2_paths import sub_completions
from e3_suffix import absorber

DMAX = int(os.environ.get('E4_DMAX', '1'))


def run(I, Y, pi, cache, rule, J):
    seq = list(pi)[::-1]
    X = sub_completions(I, Y, seq[:1], cache)[0]
    for k in range(2, I.n + 1):
        f = seq[k - 1]
        A = sub_completions(I, Y, seq[:k], cache)
        if len(A) == 0: return False, k
        d = (A != X[None, :]).sum(axis=1) if A.shape[1] else np.zeros(len(A), int)
        if (d == 0).any():
            X = A[np.nonzero(d == 0)[0][0]]; continue
        cand = np.nonzero((d >= 1) & (d <= DMAX))[0]
        if len(cand) == 0: return False, k
        o = absorber(X, I.n)
        def key(ci):
            x2 = A[ci]; t = np.nonzero(x2 != X)[0]
            g = J[t[0]]; a, b = X[t[0]], x2[t[0]]
            vf = int(I.V[f, g])
            fromo = (a == o)
            if rule == 'f-first': return (len(t), b != f, not fromo, -vf, g)
            if rule == 'f-low': return (len(t), b != f, not fromo, vf, g)
            if rule == 'helper': return (len(t), b == f, not fromo, -vf, g)
            if rule == 'keepo': return (len(t), absorber(x2, I.n) != seq[0], b != f, not fromo, -vf, g)
            raise ValueError(rule)
        X = A[min(cand, key=key)]
    return True, None


RULES = ['f-first', 'f-low', 'helper', 'keepo']

if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e4_rule.py', *sys.argv[1:], '(E4_DMAX=%d)' % DMAX, flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        byY = collections.defaultdict(list)
        for o in itertools.permutations(range(I.n)):
            byY[tuple(sd(I, o)[0])].append(o)
        for Y, orders in byY.items():
            Y = list(Y); cache = {}
            try:
                full = sub_completions(I, Y, range(I.n), cache)
            except ValueError:
                continue
            if len(full) == 0: continue
            C['starts'] += 1
            J = sorted(set(range(I.m)) - set(g for g in Y if g is not None))
            for rule in RULES:
                rs = [run(I, Y, pi, cache, rule, J)[0] for pi in orders]
                C[rule + ': some order'] += any(rs)
                C[rule + ': every order'] += all(rs)
                C[rule + ': first order'] += rs[0]
                if not any(rs) and shown[rule] < 2:
                    shown[rule] += 1
                    print('RULE FAILS', rule, name, json.dumps((sets, vals)), 'picks', Y, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
