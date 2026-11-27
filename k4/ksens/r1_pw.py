"""OC1 restricted to R1-priority orders (LB's Phase 1, k4/sdc.md §2) and to some order, on the PW family
(k4/ksens.md §1): OC1 quantifies over every order, TARGET needs one.

    python3 k4/ksens/r1_pw.py"""
import sys, itertools, random, json
import _paths
import ocsat, ocseq, fam_pw, fam_ladder


def sd_r1(sets, vals, order, m):
    """R1-priority serial dictatorship: an agent all of whose goods are still available is served only when every
    unserved agent still has all its goods; ties by the order (as k4/sdc/sdc_orders.sd with r1=True)"""
    left = set(range(m)); Y = [None] * len(sets); done = set(); rank = {a: k for k, a in enumerate(order)}
    for _ in range(len(sets)):
        cand = [i for i in range(len(sets)) if i not in done]
        i = min(cand, key=lambda a: (0 if any(g not in left for g in sets[a]) else 1, rank[a]))
        done.add(i)
        av = [(vals[i][k], -g, g) for k, g in enumerate(sets[i]) if g in left]
        if av: g = max(av)[2]; Y[i] = g; left.discard(g)
    return Y


def check(name, sets, vals, m, cmax=2):
    n = len(sets); O = ocsat.OC(sets, vals, m)
    allY = ocsat.starts(sets, vals, m)
    r1Y = {}
    for o in itertools.permutations(range(n)): r1Y.setdefault(tuple(sd_r1(sets, vals, o, m)), o)
    def oc1(Y):
        b = ocsat.bases_of(Y, n); return O.holds(b, chain='any', A=1)
    bad_all = [Y for Y in allY if not oc1(Y)]; bad_r1 = [Y for Y in r1Y if not oc1(Y)]
    ext_r1 = sum(1 for Y in r1Y if O.holds(ocsat.bases_of(Y, n), chain='none', A=1))
    print('%s: k %d n %d m %d | all orders: %d starts, OC1 fails on %d | R1 orders: %d starts, OC1 fails on %d, '
          'picks extend (one absorber, no chain) on %d' % (name, max(map(len, sets)), n, m, len(allY), len(bad_all),
          len(r1Y), len(bad_r1), ext_r1), flush=True)
    O.close()


if __name__ == '__main__':
    print('$ python3 k4/ksens/r1_pw.py')
    rng = random.Random(4)
    for f, W, r in [(3, 2, 4), (4, 2, 4), (3, 3, 5), (4, 3, 6)]:
        sets, vals, m = fam_ladder.clean(f, W, r); check('PW%s clean' % str((f, W, r)), sets, vals, m)
        for t in range(3):
            sets, vals, m = fam_pw.make(f, W, r, rng); check('PW%s random' % str((f, W, r)), sets, vals, m)
