"""Rule RF (receiver first; k4/girth.md section 7): at an OC1^max-failing start (strict profile, maximum-matching SD
picks Y of an order o, OC1 fails), move the receiver (the unique unfrozen agent at Y) to the front of o.  Claim: the
new order's picks form a maximum matching and satisfy OC1.

Exhaustive at n = 4, by lookup: results/k4_oc1max/two_move_starts_n4.json.gz lists EVERY (profile, picks) pair of every
n = 4 core where the picks form a maximum matching, come from serial dictatorship and fail OC1 (K4.SDC.OC1MAX.N3,
certified with an independent check), and every such pair lies on one of its 11 cores.  So the new picks Y' satisfy
OC1 iff they form a maximum matching and (profile, Y') is not in that list.  The orders of a start are recomputed here
by serial dictatorship over all n! orders (not read from the file).  The coordinator's other candidate reorders are
tested the same way.  At n = 5 (the 24 stored failures) the raw checker k4/sdc/oc1_mc2_rand.Inst decides instead.

    python3 k4/girth/oc1_recvfirst.py
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
from oc1_cycles import roles, signature  # noqa: E402


def sd(R, v, order):
    taken = set()
    picks = [None] * len(R)
    for i in order:
        av = [g for g in R[i] if g not in taken]
        if av:
            g = max(av, key=lambda h: v[i][h])
            picks[i] = g
            taken.add(g)
    return tuple(picks)


def reorders(o, rl, sets, picks, J):
    """candidate local reorders of the failing order o: name -> list of new orders (the rule works if one of them does)"""
    n = len(o)
    R = [set(S) for S in sets]
    D = [i for i in range(n) if rl[i] in ('DT', 'Dp')]
    DT = [i for i in range(n) if rl[i] == 'DT']
    u = rl.index('U')
    two = [(a, b) for a, b in itertools.combinations(range(n), 2) if len(R[a] & R[b]) >= 2]

    def swap(a, b):
        x = list(o)
        i, j = x.index(a), x.index(b)
        x[i], x[j] = x[j], x[i]
        return x

    def before(x, y):
        z = [a for a in o if a != x]
        z.insert(z.index(y), x)
        return z

    out = {'RF: receiver first': [[u] + [a for a in o if a != u]]}
    dt = [(a, b) for a, b in itertools.combinations(DT, 2) if len(R[a] & R[b] & J) >= 2]
    if dt:
        out['swap the D_T pair sharing two junk goods'] = [swap(*dt[0])]
    sw = [d for d in D if (min(d, u), max(d, u)) in two and picks[d] in R[u] and picks[u] in R[d]]
    if sw:
        out['receiver just before its pick-swap partner'] = [before(u, d) for d in sw if o.index(u) > o.index(d)]
    out['swap the two agents of some Berge 2-cycle'] = [swap(a, b) for a, b in two]
    out['some adjacent transposition'] = [swap(o[k], o[k + 1]) for k in range(n - 1)]
    return out


def main():
    print('$ python3 k4/girth/oc1_recvfirst.py', flush=True)
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    C = collections.Counter()
    example = None
    for h in d['hypergraphs']:
        sets = h['sets']
        R = [set(S) for S in sets]
        n = len(sets)
        fails = set()
        for st in h['starts']:
            fails.add((tuple(signature(x) for x in st['vals']), tuple(st['picks'])))
        orders = list(itertools.permutations(range(n)))
        Hc = collections.Counter()
        for st in h['starts']:
            v = [dict(zip(sets[i], st['vals'][i])) for i in range(n)]
            sig = tuple(signature(x) for x in st['vals'])
            Y = tuple(st['picks'])
            rl, J = roles(sets, st['vals'], st['picks'])
            assert rl.count('U') == 1
            Hc['starts'] += 1
            for o in orders:
                if sd(R, v, o) != Y:
                    continue
                Hc['failing orders'] += 1
                for name, cands in reorders(list(o), rl, sets, Y, J).items():
                    Hc[(name, 'applicable')] += 1
                    ok = False
                    for o2 in cands:
                        Y2 = sd(R, v, o2)
                        if None in Y2 or len(set(Y2)) != h['nu']:
                            continue
                        if (sig, Y2) not in fails:
                            ok = True
                            break
                    Hc[(name, 'works')] += ok
                    if name.startswith('RF') and not ok and example is None:
                        example = (h['list'], h['idx'], sets, st['vals'], Y, o)
        print('%s#%d: %d starts, %d failing orders; RF works on %d' % (
            h['list'], h['idx'], Hc['starts'], Hc['failing orders'], Hc[('RF: receiver first', 'works')]), flush=True)
        C.update(Hc)
    print('n = 4 (exhaustive): %d failing starts, %d failing orders' % (C['starts'], C['failing orders']))
    for name in sorted({k[0] for k in C if isinstance(k, tuple)}):
        print('   %-48s works on %7d of %7d applicable failing orders' % (name, C[(name, 'works')],
                                                                         C[(name, 'applicable')]))
    if example:
        print('RF FAILS, e.g.', example)
    # n = 5: raw checker
    from oc1_mc2_rand import Inst
    C5 = collections.Counter()
    for line in open(os.path.join(ROOT, 'results/k4_oc1max/oc1prime_cex_n5_partial.jsonl')):
        r = json.loads(line)
        I = Inst(r['sets'], r['vals'])
        R = [set(S) for S in r['sets']]
        v = [dict(zip(r['sets'][i], r['vals'][i])) for i in range(I.n)]
        Y = tuple(r['picks'])
        rl, J = roles(r['sets'], r['vals'], r['picks'])
        allo = list(itertools.permutations(range(I.n)))
        nu = max(sum(p is not None for p in sd(R, v, o)) for o in allo)
        assert I.check(Y) == 'OC1 fails'
        C5['starts'] += 1
        for o in allo:
            if sd(R, v, o) != Y:
                continue
            C5['failing orders'] += 1
            for name, cands in reorders(list(o), rl, r['sets'], Y, J).items():
                C5[(name, 'applicable')] += 1
                C5[(name, 'works')] += any(sum(p is not None for p in sd(R, v, o2)) == nu
                                           and I.check(sd(R, v, o2)) != 'OC1 fails' for o2 in cands)
    print('n = 5 (the 24 stored failures, raw checker): %d failing starts, %d failing orders' % (
        C5['starts'], C5['failing orders']))
    for name in sorted({k[0] for k in C5 if isinstance(k, tuple)}):
        print('   %-48s works on %7d of %7d applicable failing orders' % (name, C5[(name, 'works')],
                                                                         C5[(name, 'applicable')]))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
