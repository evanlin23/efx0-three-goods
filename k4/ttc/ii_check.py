"""Statement (ii) (coordinator, 03:33; k4/ttc.md §14.7): if some maximum-matching SD start of a profile fails OC1, then
some maximum-matching SD outcome of the same profile has >= 2 receivers.  Together with R2 (>= 2 receivers => one move
suffices), it gives OC1^exists-max.  Tested on the certifier's complete n = 4 export of OC1^max-failing (profile, picks)
pairs (compute/k4-oc1max-cert, results/k4_oc1max/two_move_starts_n4.json.gz): for each distinct profile, every order's
SD outcome is computed, the perfect ones kept, their receivers counted, and each outcome with >= 2 receivers is checked
for OC1 (a one-absorber completion at the picks or after one chain or addition).

    python3 k4/ttc/ii_check.py two_move_starts_n4.json.gz"""
import sys, os, gzip, json, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ttclib as T


def oc1(E, b):
    return T.extends_A(E, b, 1) or any(T.extends_A(E, b2, 1) for b2 in T.DF.iter_chains(E, b))


if __name__ == '__main__':
    print('$ python3 k4/ttc/ii_check.py', *sys.argv[1:])
    d = json.load(gzip.open(sys.argv[1])); C = collections.Counter(); seen = set()
    for h in d['hypergraphs']:
        sets = h['sets']; m = 1 + max(max(s) for s in sets); n = len(sets)
        for st in h['starts']:
            key = (json.dumps(sets), json.dumps(st['vals']))
            if key in seen:
                continue
            seen.add(key); C['distinct failing profiles'] += 1
            E = T.Enc(sets, st['vals'], m); outs = set()
            for pi in itertools.permutations(range(n)):
                Y = tuple(T.sd(E, list(pi))[0])
                if all(y is not None for y in Y):
                    outs.add(Y)
            recs = {Y: n - len(T.frozen_set(E, T.base_of(E, Y))) for Y in outs}
            two = [Y for Y in outs if recs[Y] >= 2]
            C['  some perfect outcome has >= 2 receivers' if two else '  EVERY perfect outcome has 1 receiver'] += 1
            if two:
                good = [Y for Y in two if oc1(E, T.base_of(E, Y))]
                C['  ... and every such outcome satisfies OC1' if len(good) == len(two) else
                  '  ... SOME OUTCOME WITH >= 2 RECEIVERS FAILS OC1'] += 1
            else:
                good = [Y for Y in outs if oc1(E, T.base_of(E, Y))]
                C['  one receiver everywhere: some perfect outcome satisfies OC1' if good else
                  '  ONE RECEIVER EVERYWHERE AND NO GOOD PERFECT OUTCOME'] += 1
                top = [max(sets[i], key=lambda g: E.v[i][g]) for i in range(n)]
                cnt = collections.Counter(top)
                C['  one receiver everywhere: every top good shared by >= 2 agents' if all(cnt[t] >= 2 for t in top) else
                  '  one receiver everywhere: some agent has an unshared top'] += 1
                if C['printed'] < 6:
                    C['printed'] += 1
                    print('ALL ONE RECEIVER', json.dumps({'sets': sets, 'vals': st['vals'], 'tops': top,
                                                          'perfect outcomes': len(outs), 'good': len(good)}))
    for k in sorted(C):
        print(k, C[k])
