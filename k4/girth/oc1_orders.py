"""Which serial-dictatorship order works at an OC1^max-failing profile?  (coordinator, burst 5; k4/girth.md section 7)

For a failing start (profile, failing picks Y, the orders that give Y), each candidate LOCAL REORDER of a failing order
is applied and the new picks are tested with main's raw checker k4/sdc/oc1_mc2_rand.Inst (SD picks, official moves,
brute-force one-absorber completion): the reorder WORKS if its picks form a maximum matching and satisfy OC1 (a
one-absorber completion at the picks or after one move).  Roles at Y as in k4/girth/oc1_cycles.py.

Reorders of a failing order o:
  swapDT      swap the positions of the two truly dangerous agents that share two junk goods (n = 4 mechanism);
  swapDD      swap two dangerous agents sharing a junk good (the first such pair; all pairs reported separately);
  recv<d      move the receiver to just before the dangerous agent of its pick swap (n = 5 mechanism);
  recvfirst   move the receiver to the front;
  rev2cyc     swap the positions of the two agents of some Berge 2-cycle (any 2-cycle; "some" = one of them works);
  adj         some adjacent transposition;
  any         some order of the profile (OC1^exists-max).
Also: at how many failing profiles do ALL maximum-matching picks other than the failing ones satisfy OC1?

    python3 k4/girth/oc1_orders.py [STARTS_PER_CORE] [SEED]
EVIDENCE (a stratified sample of the 112,880 n = 4 failing starts; all 24 stored n = 5 ones).
"""
import collections
import gzip
import itertools
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402


def analyse(sets, vals, picks, C, tag):
    I = Inst(sets, vals)
    n = I.n
    allorders = list(itertools.permutations(range(n)))
    sd = {o: I.sd(o) for o in allorders}
    nu = max(sum(p is not None for p in pk) for pk in sd.values())
    cache = {}

    def works(o):
        pk = sd[tuple(o)]
        if sum(p is not None for p in pk) != nu:
            return False
        if pk not in cache:
            cache[pk] = I.check(pk) != 'OC1 fails'
        return cache[pk]

    Y = tuple(picks)
    fail_orders = [o for o in allorders if sd[o] == Y]
    assert fail_orders and not works(fail_orders[0]), 'not a failing start'
    rl, J = roles(sets, vals, picks)
    R = [set(S) for S in sets]
    D = [i for i in range(n) if rl[i] in ('DT', 'Dp')]
    DT = [i for i in range(n) if rl[i] == 'DT']
    U = [i for i in range(n) if rl[i] == 'U']
    two = [(a, b) for a, b in itertools.combinations(range(n), 2) if len(R[a] & R[b]) >= 2]
    dtpair = [(a, b) for a, b in itertools.combinations(DT, 2) if len(R[a] & R[b] & J) >= 2]
    ddj = [(a, b) for a, b in itertools.combinations(D, 2) if R[a] & R[b] & J]
    swaps_du = [(d, u) for d in D for u in U if (min(d, u), max(d, u)) in two and picks[d] in R[u] and picks[u] in R[d]]
    others = {sd[o] for o in allorders if sd[o] != Y and sum(p is not None for p in sd[o]) == nu}
    C[(tag, 'profiles')] += 1
    if all(works(next(o for o in allorders if sd[o] == pk)) for pk in others):
        C[(tag, 'profiles: every other maximum-matching pick vector satisfies OC1')] += 1

    def swap(o, a, b):
        o = list(o)
        i, j = o.index(a), o.index(b)
        o[i], o[j] = o[j], o[i]
        return o

    def move_before(o, x, y):
        o = [a for a in o if a != x]
        o.insert(o.index(y), x)
        return o

    for o in fail_orders:
        C[(tag, 'failing orders')] += 1
        if dtpair:
            C[(tag, 'swapDT applicable')] += 1
            C[(tag, 'swapDT works')] += works(swap(o, *dtpair[0]))
        if ddj:
            C[(tag, 'swapDD applicable')] += 1
            C[(tag, 'swapDD (first pair) works')] += works(swap(o, *ddj[0]))
            C[(tag, 'swapDD (some pair) works')] += any(works(swap(o, a, b)) for a, b in ddj)
        if swaps_du:
            C[(tag, 'recv<d applicable')] += 1
            ok = []
            for d, u in swaps_du:
                if o.index(u) > o.index(d):
                    ok.append(works(move_before(o, u, d)))
                else:
                    ok.append(False)
            C[(tag, 'recv<d (some swap) works')] += any(ok)
            C[(tag, 'receiver already before its swap partner')] += any(o.index(u) < o.index(d) for d, u in swaps_du)
        if U:
            C[(tag, 'recvfirst works')] += works([U[0]] + [a for a in o if a != U[0]])
        if two:
            C[(tag, 'rev2cyc (some 2-cycle) works')] += any(works(swap(o, a, b)) for a, b in two)
            C[(tag, 'rev2cyc (every 2-cycle) works')] += all(works(swap(o, a, b)) for a, b in two)
        C[(tag, 'adj (some adjacent transposition) works')] += any(
            works(swap(o, o[k], o[k + 1])) for k in range(n - 1))
        C[(tag, 'any order works')] += any(works(o2) for o2 in allorders)


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    print('$ python3 k4/girth/oc1_orders.py', *sys.argv[1:], flush=True)
    C = collections.Counter()
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    for h in d['hypergraphs']:
        sts = h['starts'] if len(h['starts']) <= per else rng.sample(h['starts'], per)
        for st in sts:
            analyse(h['sets'], st['vals'], st['picks'], C, 'n=4')
        print('  %s#%d done' % (h['list'], h['idx']), flush=True)
    for line in open(os.path.join(ROOT, 'results/k4_oc1max/oc1prime_cex_n5_partial.jsonl')):
        r = json.loads(line)
        analyse(r['sets'], r['vals'], r['picks'], C, 'n=5')
    for tag in ('n=4', 'n=5'):
        fo = C[(tag, 'failing orders')]
        print('%s: %d failing profiles, %d failing orders' % (tag, C[(tag, 'profiles')], fo))
        for k in sorted(k for t, k in C if t == tag):
            if k in ('failing orders', 'profiles'):
                continue
            base = C[(tag, 'profiles')] if k.startswith('profiles') else fo
            if k.startswith('swapDT') and k != 'swapDT applicable':
                base = C[(tag, 'swapDT applicable')]
            if k.startswith('swapDD') and k != 'swapDD applicable':
                base = C[(tag, 'swapDD applicable')]
            if k.startswith('recv<d') and k != 'recv<d applicable' or k.startswith('receiver already'):
                base = C[(tag, 'recv<d applicable')]
            print('   %-62s %8d of %8d (%.1f%%)' % (k, C[(tag, k)], base, 100.0 * C[(tag, k)] / max(base, 1)))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
