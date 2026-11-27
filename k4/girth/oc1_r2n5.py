"""RF and Lemma DEMOTE at the n = 5 OC1^max failures with TWO receivers (counterexamples to TTC's R2: 5_pure #650,
#655, #1014, #1050; instances as in the coordinator's k4/sdc/r2_n5_cex_check.py on claude/kind-lamport-y8fdme).

Per-order form: for every order o giving the failing picks Y and every receiver u of Y, Y' = SD(u, o - u).  Reported:
whether Y' is a maximum matching, whether u is the last picker of o (Lemma RF-PATH's hypothesis), whether Y' differs
from Y exactly along one ejection path from u, and the classification "(i) or (T) or (C)" of Lemma DEMOTE
(k4/girth/oc1_residue.check_one, with w = the holder of u's top good at Y and d = the end of the path from u), plus
the raw OC1 result at Y' (k4/sdc/oc1_mc2_rand.Inst.check).

    python3 k4/girth/oc1_r2n5.py
"""
import collections
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_residue import check_one  # noqa: E402

CASES = {
    '5_pure#650': ([[0, 1, 5, 7], [0, 5, 6, 7], [1, 5, 6, 7], [2, 3, 4, 6], [2, 3, 4, 7]],
                   [[3, 6, 7, 5], [2, 10, 7, 6], [2, 8, 4, 3], [4, 5, 6, 8], [5, 4, 6, 8]], (5, 0, 1, 6, 7)),
    '5_pure#655': ([[0, 1, 6, 7], [0, 4, 5, 6], [1, 5, 6, 7], [2, 3, 4, 5], [2, 3, 4, 7]],
                   [[5, 3, 6, 7], [4, 1, 8, 6], [2, 8, 3, 4], [4, 5, 6, 8], [5, 4, 6, 8]], (6, 0, 1, 5, 7)),
    '5_pure#1014': ([[0, 6, 7, 8], [1, 2, 3, 6], [1, 2, 3, 7], [4, 5, 6, 8], [4, 5, 7, 8]],
                    [[2, 7, 10, 4], [3, 5, 6, 7], [4, 6, 5, 8], [3, 5, 7, 6], [3, 6, 8, 10]], (0, 6, 7, 8, 5)),
    '5_pure#1050': ([[0, 2, 3, 4], [1, 4, 8, 9], [2, 3, 8, 9], [5, 6, 7, 8], [5, 6, 7, 9]],
                    [[2, 10, 6, 7], [1, 4, 6, 8], [7, 3, 6, 5], [6, 5, 4, 8], [5, 3, 6, 7]], (2, 4, 3, 8, 9)),
}


def path_from(Y, Y2, J, u):
    path, cur = [u], u
    while True:
        g = Y2[cur]
        if g is None or g in J or g not in Y:
            return path
        nxt = Y.index(g)
        if nxt in path:
            return path
        path.append(nxt)
        cur = nxt


def main():
    print('$ python3 k4/girth/oc1_r2n5.py', flush=True)
    T = collections.Counter()
    for name, (S, V, P) in CASES.items():
        I = Inst(S, V)
        n = I.n
        R = [set(s) for s in S]
        v = [dict(zip(S[i], V[i])) for i in range(n)]
        Y = tuple(P)
        assert I.check(Y) == 'OC1 fails'
        rl, J = roles(S, V, list(Y))
        recv = [i for i in range(n) if rl[i] == 'U']
        allo = list(itertools.permutations(range(n)))
        nu = max(sum(p is not None for p in sd(R, v, o)) for o in allo)
        orders = [o for o in allo if sd(R, v, o) == Y]
        print('%s: receivers %s, %d failing orders, roles %s' % (name, recv, len(orders), rl))
        for u in recv:
            C = collections.Counter()
            for o in orders:
                Y2 = sd(R, v, [u] + [a for a in o if a != u])
                C['orders'] += 1
                C['u is the last picker of o'] += o[-1] == u
                if sum(p is not None for p in Y2) != nu:
                    C['RF picks NOT a maximum matching'] += 1
                    continue
                path = path_from(Y, Y2, J, u)
                changed = {i for i in range(n) if Y2[i] != Y[i]}
                C['change is one path from u'] += changed == set(path)
                top = max(R[u], key=lambda g: v[u][g])
                w = Y.index(top) if top in Y and Y.index(top) != u else path[-1]
                cls, verdict = check_one(S, V, Y2, w, path[-1])
                C['DEMOTE: %s / %s' % (cls, verdict)] += 1
                C['raw OC1 at Y\': ' + I.check(Y2)] += 1
            for k in sorted(C):
                print('   receiver %d first: %-60s %3d' % (u, k, C[k]))
                T[k] += C[k]
    print('TOTAL over the 4 starts and both receivers:')
    for k in sorted(T):
        print('   %-70s %4d' % (k, T[k]))


if __name__ == '__main__':
    main()
