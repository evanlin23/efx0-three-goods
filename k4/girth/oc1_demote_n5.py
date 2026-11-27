"""Lemma DEMOTE's uniform statement "(i) or (T) or (C) or (C')" (k4/girth/oc1_residue.check_one) and Rule RF on a
sample of the certifier's n = 5 OC1^max failures (two_move_starts_n5_partial6.json.gz on compute/k4-oc1max-cert,
702,250 starts on 6 hypergraphs, a partial list).  Each sampled start is first re-checked to fail OC1 with main's raw
checker (k4/sdc/oc1_mc2_rand.Inst.check); then for every order giving its picks and every receiver u: Y' = SD(u, o-u),
whether it is a maximum matching, whether it differs from Y along one ejection path from u (Lemma RF-PATH), the
DEMOTE verdict, and the raw OC1 result at Y'.  EVIDENCE.

    python3 k4/girth/oc1_demote_n5.py EXPORT.json.gz PER_HYPERGRAPH SEED
"""
import collections
import gzip
import itertools
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_residue import check_one  # noqa: E402
from oc1_r2n5 import path_from  # noqa: E402


def main():
    path, per, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    print('$ python3 k4/girth/oc1_demote_n5.py', os.path.basename(path), per, seed, flush=True)
    d = json.load(gzip.open(path))
    T = collections.Counter()
    fails = []
    for h in d['hypergraphs']:
        S = h['sets']
        n = len(S)
        R = [set(s) for s in S]
        sts = h['starts'] if len(h['starts']) <= per else rng.sample(h['starts'], per)
        C = collections.Counter()
        allo = list(itertools.permutations(range(n)))
        for st in sts:
            V = st['vals']
            v = [dict(zip(S[i], V[i])) for i in range(n)]
            Y = tuple(st['picks'])
            I = Inst(S, V)
            C['starts'] += 1
            if I.check(Y) != 'OC1 fails':
                C['start does NOT fail OC1 (raw)'] += 1
                continue
            rl, J = roles(S, V, list(Y))
            recv = [i for i in range(n) if rl[i] == 'U']
            nu = max(sum(p is not None for p in sd(R, v, o)) for o in allo)
            orders = [o for o in allo if sd(R, v, o) == Y]
            some_recv_ok = True
            for o in orders:
                C['failing orders'] += 1
                ok_here = False
                for u in recv:
                    Y2 = sd(R, v, [u] + [a for a in o if a != u])
                    if sum(p is not None for p in Y2) != nu:
                        C['(order, receiver): RF picks not maximum'] += 1
                        continue
                    pth = path_from(Y, Y2, J, u)
                    changed = {i for i in range(n) if Y2[i] != Y[i]}
                    C['(order, receiver): one ejection path'] += changed == set(pth)
                    top = max(R[u], key=lambda g: v[u][g])
                    w = Y.index(top) if top in Y and Y.index(top) != u else pth[-1]
                    cls, verdict = check_one(S, V, Y2, w, pth[-1])
                    C['(order, receiver): DEMOTE %s / %s' % (cls, verdict.split(' (')[0] if verdict.startswith('FAILS') else verdict)] += 1
                    raw = I.check(Y2)
                    C['(order, receiver): raw OC1 at Y\': ' + raw] += 1
                    ok_here |= raw != 'OC1 fails'
                    if verdict.startswith('FAILS') and len(fails) < 5:
                        fails.append(('%s#%d' % (h['list'], h['idx']), S, V, list(Y), list(o), u, list(Y2), raw))
                C['failing orders: RF works for some receiver'] += ok_here
        print('%s#%d (%d starts in the export):' % (h['list'], h['idx'], len(h['starts'])), flush=True)
        for k in sorted(C):
            print('   %-80s %6d' % (k, C[k]), flush=True)
        T.update(C)
    print('TOTAL:')
    for k in sorted(T):
        print('   %-80s %6d' % (k, T[k]))
    for f in fails:
        print('DEMOTE FAILS at', f)
    sys.stdout.flush()


if __name__ == '__main__':
    main()
