"""Maximum-matching starts (k4/ksens.md §7): a serial-dictatorship start is a matching of the agent / relevant-good
graph; it is a maximum-matching start when its size (agents with a pick) equals the maximum matching size nu.
Reports, for the known counterexamples, whether each failing start (OC1 with one chain; RD1 with one round) is a
maximum-matching start.

    python3 k4/ksens/maxmatch.py"""
import json
import networkx as nx
import _paths
import ocsat


def nu(sets, vals):
    G = nx.Graph(); G.add_nodes_from(('a', i) for i in range(len(sets)))
    for i, (s, v) in enumerate(zip(sets, vals)):
        for g, x in zip(s, v):
            if x > 0: G.add_edge(('a', i), ('g', g))
    return len(nx.max_weight_matching(G, maxcardinality=True))


def is_max(Y, sets, vals, nu_=None):
    return sum(1 for g in Y if g is not None) == (nu_ if nu_ is not None else nu(sets, vals))


if __name__ == '__main__':
    import fam_ladder, fam_pwr1, refute_rd_k5 as R
    from refute_oc1_r1 import pw_flat, pw_nf
    from round_known import KGEN
    cases = {'PW5': fam_ladder.clean(3, 2, 4), 'RD5': (R.SETS, R.VALS, 7), 'kgen-n4': KGEN, 'PW436': fam_ladder.clean(4, 3, 6),
             'PWR1-6': fam_pwr1.make(3, 3, 5, [0]), 'NF2-6': pw_flat(3, 3, 5, (0,)), 'NF1R1-6': pw_nf(4, 3, 5, (0,))}
    print('$ python3 k4/ksens/maxmatch.py')
    for name, (sets, vals, m) in cases.items():
        O = ocsat.OC(sets, vals, m); n = len(sets); v = nu(sets, vals); st = ocsat.starts(sets, vals, m)
        f1 = [Y for Y in st if not O.holds(ocsat.bases_of(Y, n), chain='any', A=1)]
        fr = [Y for Y in st if not O.holds(ocsat.bases_of(Y, n), chain='any', A=1, multi=True)]
        mx = [Y for Y in st if is_max(Y, sets, vals, v)]
        print('%s: n %d, nu %d; starts %d, of which maximum-matching %d; OC1 fails on %d (%d of them maximum-matching); '
              'one round fails on %d (%d maximum-matching)' % (name, n, v, len(st), len(mx), len(f1),
              sum(1 for Y in f1 if is_max(Y, sets, vals, v)), len(fr), sum(1 for Y in fr if is_max(Y, sets, vals, v))), flush=True)
        O.close()
