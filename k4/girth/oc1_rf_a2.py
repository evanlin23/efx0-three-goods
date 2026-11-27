"""RF residue A2 at n = 4 (k4/girth.md section 7; split of the residue with the oc1-hall session, k4/oc1_hall.md
§24.6 on claude/k4-oc1-hall): RF starts Y' with one receiver, no truly dangerous agent, and RF path u -> d (w = d,
d takes a junk good).  From the complete n = 4 export (results/k4_oc1max/two_move_starts_n4.json.gz), every distinct
A2 start (profile, Y'): the core, the roles, and either the one-absorber completions at Y' (owner, its bundle, the
single junk goods) or, if none, the repairing trade of Lemma DEMOTE (T) (partner p, its junk good j) and the shape of
the completion after it.  Raw EFX0 (k4/sdc/oc1_mc2_rand.Inst.efx0).  EVIDENCE / exhaustive at n = 4.

    python3 k4/girth/oc1_rf_a2.py
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
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_demote import rf_path  # noqa: E402


def completions(I, base, owners):
    J = [g for g in range(I.m) if all(g not in b for b in base)]
    out = []
    for a in owners:
        for r in (range(2, len(J) + 1) if a is not None else [0]):
            for S in itertools.combinations(J, r):
                rest = [g for g in J if g not in S]
                others = [i for i in range(I.n) if i != a]
                for recv in itertools.permutations(others, len(rest)):
                    B = [list(b) for b in base]
                    if a is not None:
                        B[a] += list(S)
                    for g, i in zip(rest, recv):
                        B[i].append(g)
                    if I.efx0(B):
                        out.append((a, S, dict(zip(rest, recv))))
    return out


def main():
    print('$ python3 k4/girth/oc1_rf_a2.py', flush=True)
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    seen = set()
    C = collections.Counter()
    for h in d['hypergraphs']:
        sets = h['sets']
        R = [set(s) for s in sets]
        n = len(sets)
        for st in h['starts']:
            vals = st['vals']
            v = [dict(zip(sets[i], vals[i])) for i in range(n)]
            Y = tuple(st['picks'])
            rl, J = roles(sets, vals, list(Y))
            u = rl.index('U')
            for o in itertools.permutations(range(n)):
                if sd(R, v, o) != Y:
                    continue
                Y2 = sd(R, v, [u] + [a for a in o if a != u])
                path, end = rf_path(Y, Y2, J, u)
                rl2, J2 = roles(sets, vals, list(Y2))
                if rl2.count('U') != 1 or rl2.count('DT') != 0 or len(path) != 2:
                    continue
                key = (h['list'], h['idx'], tuple(map(tuple, vals)), Y2)
                if key in seen:
                    continue
                seen.add(key)
                dd = path[1]
                C['A2 starts'] += 1
                C['core %s#%d' % (h['list'], h['idx'])] += 1
                C['roles at Y %s, at Y\' %s' % (''.join(r[0] if r != 'DT' else 'T' for r in rl),
                                               ''.join(r[0] if r != 'DT' else 'T' for r in rl2))] += 1
                C['d is %s at Y; d ends with %s' % (rl[dd], end)] += 1
                I = Inst(sets, vals)
                base = [[p] for p in Y2]
                comps = completions(I, base, [None] + list(range(n)))
                lab = lambda i: 'u' if i == u else ('d' if i == dd else 'D%d' % i)
                if comps:
                    C['completes at Y\''] += 1
                    shapes = sorted({'owner %s takes %d junk; singles to %s' % (
                        'none' if a is None else lab(a), len(S), ','.join(sorted(lab(i) for i in sg.values())) or '-')
                        for a, S, sg in comps})
                    for sh in shapes:
                        C['  completion shape: ' + sh] += 1
                    continue
                C['needs a move'] += 1
                # the trade of DEMOTE (T): p takes {Y'_d, j}, d takes {Y'_p}
                found = []
                for p in range(n):
                    if rl2[p] != 'Dp':
                        continue
                    for j in sorted(J2):
                        if j not in v[p]:
                            continue
                        if not (I.V(p, [Y2[dd], j]) > I.V(p, [Y2[p]]) and I.V(dd, [Y2[p]]) > I.V(dd, [Y2[dd]])):
                            continue
                        stt = [list(b) for b in base]
                        stt[p] = [Y2[dd], j]
                        stt[dd] = [Y2[p]]
                        cs = completions(I, stt, [None] + list(range(n)))
                        if cs:
                            found.append((p, j, cs))
                C['  trade repairs' if found else '  NO TRADE REPAIRS'] += 1
                for p, j, cs in found[:1]:
                    C['  trade partner p = %s (holds the pick of %s at Y)' % (lab(p), lab(Y.index(Y2[p])) if Y2[p] in Y else 'junk')] += 1
                    C['  trade partner p is the agent whose pick u takes? %s' % (Y.index(Y2[u]) == p)] += 1
                    shapes = sorted({'owner %s takes %d junk; singles to %s' % (
                        'none' if a is None else lab(a), len(S), ','.join(sorted(lab(i) for i in sg.values())) or '-')
                        for a, S, sg in cs})
                    for sh in shapes:
                        C['  after the trade: ' + sh] += 1
    for k in sorted(C):
        print('%-90s %6d' % (k, C[k]))


if __name__ == '__main__':
    main()
