"""Reproduce the two failed approaches of k4/oc1max_multi.md §4 and §6 from the raw definitions (mmlib only).

    python3 k4/oc1max_multi/repro.py t3        canonical chains do not repair T3 (order 0,1,2); a ring does
    python3 k4/oc1max_multi/repro.py disjoint  n4_3#211.0: every canonical chain leaves another agent's danger set
"""
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, frozen, dangerous, oa_absorbers, sstar_owners, moves, describe
from dred import canonical_chains, improving_sets, obstacles


def show(sets, vals, order):
    I = Inst(sets, vals); Y = I.sd(order); b = base_from_picks(Y); J = junk(I, b); D = dangerous(I, b)
    print('sets', sets, 'vals', vals, 'order', order, 'picks', Y, 'junk', J, 'D', D)
    print(describe(I, Y))
    print('one-absorber completions at the picks (absorbers):', sorted(oa_absorbers(I, b)))
    return I, Y, b, J, D


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 't3':
        I, Y, b, J, D = show([[5, 0, 4, 2], [3, 1, 4], [4, 1, 3, 0]], [[1, 38, 36, 6], [12, 22, 30], [28, 20, 12, 38]],
                             (0, 1, 2))
        for k in D:
            for path in canonical_chains(I, b, k):
                Hs = list(improving_sets(I, b, k, J + list(b[path[-1]]), False))
                print('canonical chain', path, 'improving sets', Hs)
                for H0 in Hs:
                    nb, ob = obstacles(I, b, path, H0)
                    print('   H0', H0, '->', nb, 'obstacles', sorted(ob), 'one-absorber absorbers', sorted(oa_absorbers(I, nb)))
        print('repairing moves (all):')
        for nb, ds in moves(I, b).items():
            oa = oa_absorbers(I, nb)
            if oa: print('  ', nb, 'absorbers', sorted(oa), 'S* owners', sorted(sstar_owners(I, nb)), ds)
    elif mode == 'disjoint':
        I, Y, b, J, D = show([[0, 2, 4, 7], [1, 3, 5, 7], [4, 6, 8], [5, 6, 7, 8], [5, 6, 8]],
                             [[15, 16, 13, 26], [15, 18, 29, 16], [2, 28, 29], [19, 13, 30, 14], [29, 27, 11]],
                             (0, 1, 3, 4, 2))
        for d in D: print('agent', d, 'junk', [g for g in J if g in I.R[d]], 'pick value', I.V(d, b[d]))
        for k in D:
            for path in canonical_chains(I, b, k):
                for H0 in improving_sets(I, b, k, J + list(b[path[-1]]), False):
                    nb, ob = obstacles(I, b, path, H0)
                    from mmlib import sstar
                    print('chain', path, 'H0', H0, 'obstacles', sorted(ob), 'S* completion owned by k:', sstar(I, nb, k, witness=True))
