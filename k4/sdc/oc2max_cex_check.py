"""Coordinator's independent check (2026-11-26) of the certifier's claims on the 11 n = 4 OC1^max counterexamples
(results/k4_oc1max/oc1max_cex_n4.json on compute/k4-oc1max-cert).  Own code (oc1_mc2_rand.Inst: raw EFX0, official
moves, one-absorber completion).  For each instance: (1) the stored start fails OC1 (no one-absorber completion at the
picks or after one move); (2) OC2: some state two sequential moves away has a one-absorber completion; (3) every
maximum-matching order of the instance satisfies OC2, and how many satisfy OC1 (the exists-order form).

    python3 k4/sdc/oc2max_cex_check.py FILE.json"""
import sys, json, itertools, collections
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu


def oc2(I, picks):
    base = [[g] if g is not None else [] for g in picks]
    if I.one_absorber(base): return 0
    M = I.moves(base)
    if any(I.one_absorber([list(b) for b in s]) for s in M): return 1
    for s in M:
        for s2 in I.moves([list(b) for b in s]):
            if I.one_absorber([list(b) for b in s2]): return 2
    return None


if __name__ == '__main__':
    D = json.load(open(sys.argv[1]))['instances']
    print('$ python3 k4/sdc/oc2max_cex_check.py', sys.argv[1].split('/')[-1], '|', len(D), 'instances')
    T = collections.Counter()
    for k, d in enumerate(D):
        I = Inst(d['sets'], d['vals']); N = nu(I)
        pk = tuple(d['picks'])
        stored = oc2(I, pk)
        pv = collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n)))
        res = collections.Counter()
        for p, c in pv.items():
            if sum(x is not None for x in p) != N: res['non-max'] += c; continue
            r = oc2(I, p); res['moves needed %s' % r] += c
        T.update(res)
        print('instance', k, 'm', I.m, 'nu', N, '| stored start needs', stored, 'moves | orders:', dict(res))
    for key in sorted(T): print(key, T[key])
