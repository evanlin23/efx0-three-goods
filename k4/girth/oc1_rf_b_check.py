"""Independent check (third checker) of the oc1-hall session's uniform repair for RF residue B (k4/oc1_hall.md §24.8 on
claude/k4-oc1-hall, Lemma RF-B, as relayed in its message; not read here): at an RF start Y' with one receiver d and
two truly dangerous agents, let k be the truly dangerous agent whose pick is wanted by d only, and S the junk pair the
two truly dangerous agents share.  Allocation: k takes S, d takes Y'_k, Y'_d and the rest of the junk J' - S, every
other agent keeps its pick.  Claim: it is EFX0.  Checked with lss.is_efx0 (k4/girth/lss.py, raw EFX0, written for
this workstream) at every distinct B start of the complete n = 4 export and of the 86 stored n = 5 orders.

    python3 k4/girth/oc1_rf_b_check.py
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
from lss import Inst, is_efx0  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402


def check(sets, vals, Y2, C, tag):
    n = len(sets)
    rl2, J2 = roles(sets, vals, list(Y2))
    if rl2.count('U') != 1 or rl2.count('DT') != 2:
        return
    C[(tag, 'B starts')] += 1
    d = rl2.index('U')
    R = [set(s) for s in sets]
    v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    DT = [i for i in range(n) if rl2[i] == 'DT']
    S = R[DT[0]] & R[DT[1]] & set(J2)
    if len(S) != 2:
        C[(tag, 'shared junk of the D_T pair is not a pair')] += 1
        return
    wanted_by = {i: [j for j in range(n) if j != i and v[j].get(Y2[i], 0) > v[j][Y2[j]]] for i in DT}
    ks = [k for k in DT if wanted_by[k] == [d]]
    if len(ks) != 1:
        C[(tag, 'not exactly one D_T agent whose pick only d wants: %d' % len(ks))] += 1
        if not ks:
            return
    I = Inst([sorted(s) for s in sets], [[v[i][g] for g in sorted(sets[i])] for i in range(n)])
    res = []
    for k in ks:
        X = [{Y2[i]} for i in range(n)]
        X[k] = set(S)
        X[d] = {Y2[k], Y2[d]} | (set(J2) - S)
        assert sorted(g for b in X for g in b) == list(range(I.m)), 'not a complete allocation'
        res.append(is_efx0(I, X))
    C[(tag, 'the repair is EFX0 (for some admissible k)')] += any(res)
    C[(tag, 'the repair is EFX0 for every admissible k')] += all(res)


def main():
    print('$ python3 k4/girth/oc1_rf_b_check.py', flush=True)
    C = collections.Counter()
    seen = set()
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    for h in d['hypergraphs']:
        sets = h['sets']
        R = [set(s) for s in sets]
        for st in h['starts']:
            v = [dict(zip(sets[i], st['vals'][i])) for i in range(len(sets))]
            Y = tuple(st['picks'])
            rl, J = roles(sets, st['vals'], st['picks'])
            u = rl.index('U')
            for o in itertools.permutations(range(len(sets))):
                if sd(R, v, o) != Y:
                    continue
                Y2 = sd(R, v, [u] + [a for a in o if a != u])
                key = (h['list'], h['idx'], tuple(map(tuple, st['vals'])), Y2)
                if key not in seen and None not in Y2:
                    seen.add(key)
                    check(sets, st['vals'], Y2, C, 'n=4')
    for line in open(os.path.join(ROOT, 'results/k4_oc1max/oc1prime_cex_n5_partial.jsonl')):
        r = json.loads(line)
        R = [set(s) for s in r['sets']]
        v = [dict(zip(r['sets'][i], r['vals'][i])) for i in range(len(r['sets']))]
        Y = tuple(r['picks'])
        rl, J = roles(r['sets'], r['vals'], r['picks'])
        u = rl.index('U')
        for o in itertools.permutations(range(len(r['sets']))):
            if sd(R, v, o) != Y:
                continue
            Y2 = sd(R, v, [u] + [a for a in o if a != u])
            key = ('n5', r['idx'], Y2)
            if key not in seen and None not in Y2:
                seen.add(key)
                check(r['sets'], r['vals'], Y2, C, 'n=5')
    for k in sorted(C):
        print('%s  %-60s %7d' % (k[0], k[1], C[k]))


if __name__ == '__main__':
    main()
