"""Rule RF (k4/girth.md section 7): who can absorb the junk at the receiver-first picks Y'?

For a sample of the n = 4 failing orders (every 97th) and all n = 5 ones (the 24 stored failures), compute Y' (the
receiver moved to the front), and for each possible owner a (an agent, or nobody) whether the one-absorber completion
with owner a exists: a takes a set of >= 2 junk goods, every other agent at most one, EFX0 (main's raw definition,
k4/sdc/oc1_mc2_rand.Inst.efx0; same enumeration as Inst.one_absorber, split by owner).  The owner is classified
relative to RF's path (receiver, middle agents, the DROPPED agent = the last agent of the path, which lost value).
EVIDENCE.

    python3 k4/girth/oc1_rf_owner.py [STRIDE]
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


def owner_ok(I, base, a):
    J = [g for g in range(I.m) if all(g not in b for b in base)]
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
                    return True
    return False


def classify(sets, vals, Y, o, C, tag):
    n = len(sets)
    R = [set(S) for S in sets]
    v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    rl, J = roles(sets, vals, list(Y))
    u = rl.index('U')
    Y2 = sd(R, v, [u] + [a for a in o if a != u])
    I = Inst(sets, vals)
    base = [[p] for p in Y2]
    changed = [i for i in range(n) if Y2[i] != Y[i]]
    dropped = [i for i in changed if i != u and v[i][Y2[i]] < v[i][Y[i]]]
    C[(tag, 'sampled RF outcomes')] += 1
    C[(tag, 'exactly one dropped agent')] += len(dropped) == 1
    ok = {a: owner_ok(I, base, a) for a in [None] + list(range(n))}
    if not any(ok.values()):
        C[(tag, 'no completion at the picks (a move is needed)')] += 1
        return
    C[(tag, 'completes at the picks')] += 1
    if any(ok[d] for d in dropped):
        C[(tag, 'completes at the picks with the dropped agent as owner')] += 1
    if ok[None]:
        C[(tag, 'completes at the picks with no owner (<= 1 junk each)')] += 1
    if ok[u]:
        C[(tag, 'completes at the picks with the receiver as owner')] += 1


def main():
    stride = int(sys.argv[1]) if len(sys.argv) > 1 else 97
    print('$ python3 k4/girth/oc1_rf_owner.py', *sys.argv[1:], flush=True)
    C = collections.Counter()
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    k = 0
    for h in d['hypergraphs']:
        sets = h['sets']
        R = [set(S) for S in sets]
        for st in h['starts']:
            v = [dict(zip(sets[i], st['vals'][i])) for i in range(len(sets))]
            Y = tuple(st['picks'])
            for o in itertools.permutations(range(len(sets))):
                if sd(R, v, o) != Y:
                    continue
                k += 1
                if k % stride == 0:
                    classify(sets, st['vals'], Y, o, C, 'n=4')
    for line in open(os.path.join(ROOT, 'results/k4_oc1max/oc1prime_cex_n5_partial.jsonl')):
        r = json.loads(line)
        R = [set(S) for S in r['sets']]
        v = [dict(zip(r['sets'][i], r['vals'][i])) for i in range(len(r['sets']))]
        Y = tuple(r['picks'])
        for o in itertools.permutations(range(len(r['sets']))):
            if sd(R, v, o) == Y:
                classify(r['sets'], r['vals'], Y, o, C, 'n=5')
    for tag in ('n=4', 'n=5'):
        for key in sorted(k2 for t, k2 in C if t == tag):
            print('%s  %-62s %6d' % (tag, key, C[(tag, key)]))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
