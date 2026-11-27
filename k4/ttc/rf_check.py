"""RF at the one-receiver-everywhere profiles (k4/ttc.md §14.7).  RF (girth session): for an order sigma whose SD start
fails OC1, move the start's receiver to the front.  At every distinct n = 4 profile of the certifier's export
(compute/k4-oc1max-cert, two_move_starts_n4.json.gz) in which every perfect SD outcome has exactly one receiver, and,
for comparison, at the others: for every order sigma whose start is perfect and fails OC1, with receiver r, take
sigma' = (r, sigma minus r) and record whether SD(sigma') is perfect, whether it satisfies OC1, its number of receivers,
and where r ends up (r picks first, so it takes its top good).  Also: the shape of the good one-receiver outcomes.

    python3 k4/ttc/rf_check.py two_move_starts_n4.json.gz [STRIDE]"""
import sys, os, gzip, json, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ttclib as T


def oc1(E, b):
    return T.extends_A(E, b, 1) or any(T.extends_A(E, b2, 1) for b2 in T.DF.iter_chains(E, b))


if __name__ == '__main__':
    print('$ python3 k4/ttc/rf_check.py', *sys.argv[1:])
    stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    d = json.load(gzip.open(sys.argv[1])); C = collections.Counter(); seen = set(); k = 0
    for h in d['hypergraphs']:
        sets = h['sets']; m = 1 + max(max(s) for s in sets); n = len(sets)
        for st in h['starts']:
            key = (json.dumps(sets), json.dumps(st['vals']))
            if key in seen:
                continue
            seen.add(key)
            E = T.Enc(sets, st['vals'], m); outY = {}
            for pi in itertools.permutations(range(n)):
                Y = tuple(T.sd(E, list(pi))[0]); outY.setdefault(Y, []).append(pi)
            perfect = [Y for Y in outY if all(y is not None for y in Y)]
            rec = {Y: [i for i in range(n) if i not in T.frozen_set(E, T.base_of(E, Y))] for Y in perfect}
            one = all(len(rec[Y]) == 1 for Y in perfect)
            if not one:
                k += 1
                if k % stride:
                    continue
            cls = 'one receiver everywhere' if one else 'some outcome with >= 2 receivers'
            C['profiles: %s' % cls] += 1
            good = {Y: oc1(E, T.base_of(E, Y)) for Y in perfect}
            rf_all = True
            for Y in perfect:
                if good[Y]:
                    continue
                r = rec[Y][0]
                for pi in outY[Y]:
                    s2 = [r] + [a for a in pi if a != r]
                    Y2 = tuple(T.sd(E, s2)[0])
                    if any(y is None for y in Y2):
                        C['  %s: RF order not perfect' % cls] += 1; rf_all = False; continue
                    g2 = good.get(Y2)
                    if g2 is None:
                        g2 = oc1(E, T.base_of(E, Y2))
                    C['  %s: RF start satisfies OC1' % cls if g2 else '  %s: RF START FAILS OC1' % cls] += 1
                    nr2 = n - len(T.frozen_set(E, T.base_of(E, Y2)))
                    C['  %s: RF start has %d receivers' % (cls, nr2)] += 1
                    rf_all &= g2
            if one:
                tops = [max(sets[i], key=lambda g: E.v[i][g]) for i in range(n)]
                for Y in perfect:
                    if good[Y]:
                        nt = sum(1 for i in range(n) if Y[i] == tops[i])
                        C['  one receiver everywhere: good outcomes with %d agents at their top' % nt] += 1
                    else:
                        nt = sum(1 for i in range(n) if Y[i] == tops[i])
                        C['  one receiver everywhere: bad outcomes with %d agents at their top' % nt] += 1
    for key in sorted(C):
        print(key, C[key])
