"""Diagnostics on the OC1^max counterexamples of results/k4_oc1max/oc1max_cex_n4.json, with the raw checker
k4/sdc/oc1_mc2_rand.Inst only (workstream compute/k4-oc1max-cert).
(a) Two moves: from the failing picks, every state one move reaches, then every state a second move reaches; does
    one of them have a one-absorber completion (Inst.one_absorber), or a free completion (an EFX0 allocation, found
    by enumerating all allocations, containing the bases)?
(b) Orders: the distinct SD outcomes of all n! orders under the same profile, classified as maximum-matching or not
    and by Inst.check (picks complete / one move repairs / OC1 fails).  The R1-priority order class (k4/sdc.md §31;
    sdc_orders.sd(r1=True)) is reported as well.
(c) The envy / junk structure at the failing picks: each agent's pick rank, whose picks it prefers, which junk goods
    it values.

    python3 k4/oc1cert/diag.py [results/k4_oc1max/oc1max_cex_n4.json]"""
import sys, os, json, itertools, collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst


def efx0_allocs(I):
    out = []
    for X in itertools.product(range(I.n), repeat=I.m):
        B = [[g for g in range(I.m) if X[g] == a] for a in range(I.n)]
        if I.efx0(B): out.append(B)
    return out


def free_ok(I, EF, st):
    return any(all(set(b) <= set(B[a]) for a, b in enumerate(st)) for B in EF)


def r1_sd(I, order):
    """R1-priority serial dictatorship (k4/sdc/sdc_orders.sd with r1=True): at each step the first agent in the order
    among those that have already lost a relevant good, else the first agent."""
    left = set(range(I.m)); Y = [None] * I.n; done = [False] * I.n; rank = {a: k for k, a in enumerate(order)}
    for _ in range(I.n):
        cand = [i for i in range(I.n) if not done[i]]
        i = min(cand, key=lambda a: (0 if sum(g in left for g in I.sets[a]) < len(I.sets[a]) else 1, rank[a]))
        done[i] = True
        av = [g for g in I.sets[i] if g in left]
        if av: g = max(av, key=lambda h: I.v[i][h]); Y[i] = g; left.discard(g)
    return tuple(Y)


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'results', 'k4_oc1max', 'oc1max_cex_n4.json')
    print('$ python3 k4/oc1cert/diag.py', *sys.argv[1:], flush=True)
    D = json.load(open(path))['instances']
    for d in D:
        I = Inst(d['sets'], d['vals']); Y = tuple(d['picks'])
        EF = efx0_allocs(I)
        base = [[p] if p is not None else [] for p in Y]
        one = [list(map(list, s)) for s in I.moves(base)]
        two = set()
        for s in one:
            for s2 in I.moves(s): two.add(s2)
        a1 = sum(I.one_absorber(s) for s in one); f1 = sum(free_ok(I, EF, s) for s in one)
        a2 = sum(I.one_absorber([list(b) for b in s]) for s in two)
        f2 = sum(free_ok(I, EF, s) for s in two)
        nu = max(sum(p is not None for p in I.sd(o)) for o in itertools.permutations(range(I.n)))
        C = collections.Counter(); C1 = collections.Counter()
        outs = collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n)))
        for pk, c in outs.items():
            kind = 'max' if sum(p is not None for p in pk) == nu else 'non-max'
            C[(kind, I.check(pk))] += c
        r1 = collections.Counter(r1_sd(I, o) for o in itertools.permutations(range(I.n)))
        for pk, c in r1.items():
            C1[I.check(pk)] += c
        print(json.dumps({'list': d['list'], 'idx': d['idx'], 'sets': d['sets'], 'vals': d['vals'], 'picks': d['picks']}))
        print('   (a) one move: %d states, %d with a one-absorber completion, %d with a free one; two moves: %d states, '
              '%d one-absorber, %d free' % (len(one), a1, f1, len(two), a2, f2))
        print('   (b) orders by outcome (all %d orders, %d distinct picks): %s' % (sum(outs.values()), len(outs),
              dict(sorted(((' / '.join(k), c) for k, c in C.items())))))
        print('       R1-priority orders: %s' % dict(C1), flush=True)
        # (c) the envy / junk structure at the failing picks
        J = [g for g in range(I.m) if g not in Y]
        for i in range(I.n):
            env = [j for j in range(I.n) if j != i and Y[j] in I.v[i] and I.v[i][Y[j]] > I.v[i][Y[i]]]
            rank = sorted(I.sets[i], key=lambda g: -I.v[i][g]).index(Y[i]) + 1
            print('   (c) agent %d: pick %d (rank %d of %d), prefers the picks of %s, values the junk goods %s'
                  % (i, Y[i], rank, len(I.sets[i]), env, [g for g in J if g in I.R[i]]))


if __name__ == '__main__':
    main()
