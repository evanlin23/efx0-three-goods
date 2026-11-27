"""Replay of attempts/k4-k3oc1-selection-rules.md (k = 3, DE's core case: every agent values three goods, strictly
balanced; dead goods allowed).  For each instance and order: the DE trades from the draft, their score and omega, and
whether a one-absorber completion exists afterwards (exhaustive search, k4/k3oc1/k3lib.completion), and whether the
simple completion test of k4/k3_oc1.md Lemma 1 passes.
    python3 attempts/k4_k3oc1_rules.py"""
import os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(ROOT, 'k4', 'k3oc1'))
from k3lib import sd, base_of, completion, vals
from de_moves import de_trades
from lbtest import lb_simple, parts
from rules import score
CASES = [
    ('max score fails (n = 6, m = 10, no dead good)', [(0, 6, 9), (5, 7, 1), (4, 8, 2), (0, 3, 1), (4, 5, 3), (4, 5, 3)], 10, [0, 1, 2, 3, 4, 5]),
    ('max score fails (n = 6, m = 9, good 7 dead)', [(0, 2, 6), (3, 8, 1), (4, 1, 8), (3, 0, 5), (4, 5, 2), (4, 3, 5)], 9, [0, 1, 2, 4, 3, 5]),
    ('least omega fails the simple test (n = 6, m = 11, goods 9, 10 dead)', [(0, 1, 6), (4, 7, 2), (3, 8, 6), (0, 3, 5), (4, 3, 5), (0, 5, 4)], 11, [0, 1, 2, 3, 4, 5]),
    ('all trades tie in omega, some fail (n = 5, m = 8, good 7 dead)', [(0, 1, 2), (0, 1, 2), (0, 3, 4), (1, 3, 4), (2, 5, 6)], 8, [2, 3, 4, 0, 1]),
]
for name, rk, m, order in CASES:
    V = vals(rk); b = base_of(sd(rk, m, order), m)
    print('===', name, '| order', order, '| picks', sd(rk, m, order))
    print('  draft: one-absorber completion', completion(rk, m, b, 1, V) is not None)
    for nb, d in de_trades(rk, m, b):
        P = parts(rk, m, nb)
        print('  %-28s score %2d omega %d  completion %-5s  Lemma 1 %s' % (d[0] + ' ' + str(d[1]), score(rk, nb), len(P[1]) - len(P[5]),
              completion(rk, m, nb, 1, V) is not None, bool(lb_simple(rk, m, nb))))
