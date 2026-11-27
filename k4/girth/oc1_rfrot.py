"""Consistency check of TTC's Lemma RF-ROT (k4/ttc.md §14.7 on PR #125, as relayed by the coordinator; not read here)
against the RF data of k4/girth.md section 7: at every failing order the receiver u is the LAST picker (so RF is the
rotation (sigma_n, sigma_1, ..., sigma_{n-1})), and sigma_{n-1} is a receiver at the RF picks.  Also: how often the
end d of the RF path is sigma_{n-1}, split by the number of receivers at the RF picks.

    python3 k4/girth/oc1_rfrot.py
"""
import collections
import gzip
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_demote import rf_path  # noqa: E402


def go(sets, vals, Y, tag, C):
    n = len(sets)
    R = [set(s) for s in sets]
    v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    rl, J = roles(sets, vals, list(Y))
    u = rl.index('U')
    for o in itertools.permutations(range(n)):
        if sd(R, v, o) != tuple(Y):
            continue
        C[(tag, 'orders')] += 1
        C[(tag, 'the receiver is the last picker')] += o[-1] == u
        Y2 = sd(R, v, [u] + [a for a in o if a != u])
        if None in Y2:
            continue
        path, end = rf_path(tuple(Y), Y2, J, u)
        rl2, _ = roles(sets, vals, list(Y2))
        k = rl2.count('U')
        C[(tag, 'sigma_{n-1} is a receiver at the RF picks')] += rl2[o[-2]] == 'U'
        C[(tag, "|U'| = %d: orders" % k)] += 1
        C[(tag, "|U'| = %d: d = sigma_{n-1}" % k)] += path[-1] == o[-2]


def main():
    print('$ python3 k4/girth/oc1_rfrot.py', flush=True)
    C = collections.Counter()
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    for h in d['hypergraphs']:
        for st in h['starts']:
            go(h['sets'], st['vals'], st['picks'], 'n=4', C)
    for line in open(os.path.join(ROOT, 'results/k4_oc1max/oc1prime_cex_n5_partial.jsonl')):
        r = json.loads(line)
        go(r['sets'], r['vals'], r['picks'], 'n=5', C)
    for k in sorted(C):
        print('%s  %-46s %7d' % (k[0], k[1], C[k]))


if __name__ == '__main__':
    main()
