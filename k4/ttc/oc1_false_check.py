"""The OC1 counterexamples found by head_bign_climb.py ... ends seeded (k4/ttc.md §13): for each distinct (instance,
order) with "OC1 holds": false in results/k4_ttc/head_bign_climb_ends_seeded.log, recheck by SAT (two encodings:
oc_absorb.extends_A over de_free's chains, as the climb did), and record: the number of agents without a pick, whether
the picks have a free completion (OC with zero chains), and whether they have a completion with at most one absorber
among the agents holding a pick (agents without a pick unrestricted: ttclib.extends_A_pickless).

    python3 k4/ttc/oc1_false_check.py"""
import json, collections, os
import ttclib as T

LOG = os.path.join(T.ROOT, 'results', 'k4_ttc', 'head_bign_climb_ends_seeded.log')

if __name__ == '__main__':
    seen = {}
    for line in open(LOG):
        if line.startswith('OC1-HD FAILS'):
            d = json.loads(line[len('OC1-HD FAILS '):])
            if not d['OC1 holds']:
                seen.setdefault(json.dumps((d['sets'], d['vals'], d['order'])), d)
    C = collections.Counter()
    for d in seen.values():
        E = T.Enc(d['sets'], d['vals'], d['m']); Y = tuple(T.sd(E, d['order'])[0]); b = T.base_of(E, Y)
        C['instances'] += 1
        hard = not T.extends_A(E, b, 1)
        oc1 = any(T.extends_A(E, b2, 1) for b2 in set(T.DF.moves(E, b)))
        C['picks without a one-absorber completion'] += hard
        C['OC1 fails (no move of de_free gives one), rechecked'] += hard and not oc1
        C['agents without a pick: %d' % sum(1 for y in Y if y is None)] += 1
        C['picks have a free completion'] += T.DF.extends(E, b)
        C['picks have a completion with one absorber among the agents holding a pick'] += T.extends_A_pickless(E, b, 1)
    for k in sorted(C):
        print(k, C[k])
