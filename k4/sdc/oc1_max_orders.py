"""OC1 restricted to maximum-matching orders (OC1^max).  Every OC1 failure on the strict core B< (24 of 720 orders,
k4/sdc/oc1_core_cex_verify.py) comes from an order whose picks match only 4 of the 6 agents, while the instance has a
perfect agent matching: the two pickless agents force the pigeonhole.  OC1^max: for every serial-dictatorship order
whose picks form a maximum-cardinality matching of the agent / relevant-good graph, the picks have a one-absorber
completion, or one official move gives a state with one.  Such orders always exist: a matching that is Pareto optimal
among maximum matchings is Pareto optimal (an improvement keeps every matched agent matched), and every Pareto-optimal
matching of a house-allocation instance is a serial-dictatorship outcome.

This script: for each instance, the size nu of a maximum matching, then every order, classified by (number of picks,
OC1 outcome).  Ties in values are broken towards the lower good index (only the non-core TTC instances have ties).

    python3 k4/sdc/oc1_max_orders.py FILE.json      (a list of {'sets', 'vals'} or the two named cores 'core')"""
import sys, json, itertools, collections, multiprocessing as mp, os
import _paths  # noqa: F401  (keeps the k4/sdc import convention)
from oc1_mc2_rand import Inst


def nu(I):
    match = {}

    def aug(i, seen):
        for g in I.sets[i]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen): match[g] = i; return True
        return False
    return sum(aug(i, set()) for i in range(I.n))


def sd_lowtie(I, order):
    taken = set(); picks = [None] * I.n
    for i in order:
        av = sorted(g for g in I.R[i] if g not in taken)
        if av:
            g = max(av, key=lambda g: (I.v[i][g], -g)); picks[i] = g; taken.add(g)
    return tuple(picks)


def job(k_sets_vals):
    k, sets, vals = k_sets_vals
    I = Inst(sets, vals); N = nu(I)
    picks = collections.Counter(sd_lowtie(I, o) for o in itertools.permutations(range(I.n)))
    C = collections.Counter()
    for pk, c in picks.items():
        size = sum(p is not None for p in pk)
        C[('max' if size == N else 'non-max', I.check(pk))] += c
    return k, N, C


if __name__ == '__main__':
    src = sys.argv[1]
    print('$ python3 k4/sdc/oc1_max_orders.py', src, flush=True)
    if src == 'core':
        S = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
        L = [{'sets': S, 'vals': [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]},
             {'sets': S, 'vals': [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 19], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]}]
    else:
        L = json.load(open(src))
    T = collections.Counter(); badmax = []
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for k, N, C in pool.imap_unordered(job, [(k, d['sets'], d['vals']) for k, d in enumerate(L)]):
            for key, c in C.items(): T[key] += c
            if C[('max', 'OC1 fails')]: badmax.append(k)
            print('instance', k, 'nu', N, sorted(C.items()), flush=True)
    for key in sorted(T): print(key, T[key])
    print('instances where some maximum-matching order fails OC1:', badmax)
