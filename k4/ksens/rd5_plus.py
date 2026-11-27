"""RD5 plus extra agents (k4/ksens.md §8): how often does RD5's obstruction (a start that one round cannot repair)
survive adding two random agents (results/k4_ksens/seeds_rd5plus2.txt)?  Tests every start; reports the most rounds
any start needs (ocseq multi, one absorber, up to 2).

    python3 k4/ksens/rd5_plus.py"""
import collections
import _paths
import ocsat, ocseq
from climb import load_seeds

if __name__ == '__main__':
    C = collections.Counter(); print('$ python3 k4/ksens/rd5_plus.py', flush=True)
    for sets, vals in load_seeds(_paths.ROOT + '/results/k4_ksens/seeds_rd5plus2.txt'):
        m = 1 + max(max(s) for s in sets); n = len(sets); O = ocsat.OC(sets, vals, m); worst = 0
        for Y in ocsat.starts(sets, vals, m):
            b = ocsat.bases_of(Y, n)
            if O.holds(b, chain='none', A=1): continue
            if O.holds(b, chain='any', A=1): worst = max(worst, 1); continue
            if O.holds(b, chain='any', A=1, multi=True): worst = max(worst, 1); continue
            worst = 2
        C['instances'] += 1; C['most rounds needed by a start: %d' % worst] += 1
        O.close()
    for k in sorted(C): print(k, C[k])
