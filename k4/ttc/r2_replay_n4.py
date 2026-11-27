"""Independent replay of the certifier's n = 4 export behind K4.SDC.R2.N4 (compute/k4-oc1max-cert,
results/k4_oc1max/two_move_starts_n4.json.gz): recount the receivers of every exported OC1^max-failing (profile, picks)
pair with this workstream's code (ttclib.frozen_set), and on 300 sampled pairs check that the listed order gives the
picks and that no chain or addition gives a one-absorber completion (oc_absorb.extends_A).

    python3 k4/ttc/r2_replay_n4.py two_move_starts_n4.json.gz"""
import gzip, json, random, sys, collections, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ttclib as T
d = json.load(gzip.open(sys.argv[1])); rng = random.Random(1); C = collections.Counter()
allst = [(h, s) for h in d['hypergraphs'] for s in h['starts']]
C['exported pairs'] = len(allst)
for h, s in allst:
    sets = h['sets']; m = 1 + max(max(x) for x in sets); E = T.Enc(sets, s['vals'], m)
    Y = tuple(s['picks']); b = T.base_of(E, Y)
    U = [i for i in range(E.n) if i not in T.frozen_set(E, b)]
    C['receivers recounted: %d' % len(U)] += 1
    C['receiver sets agree' if sorted(U) == sorted(s['receivers']) else 'RECEIVER SETS DIFFER'] += 1
sample = rng.sample(allst, 300)
for h, s in sample:
    sets = h['sets']; m = 1 + max(max(x) for x in sets); E = T.Enc(sets, s['vals'], m)
    Y = tuple(s['picks']); b = T.base_of(E, Y)
    sd_ok = tuple(T.sd(E, s['orders'][0])[0]) == Y
    fails = not T.extends_A(E, b, 1) and not any(T.extends_A(E, b2, 1) for b2 in T.DF.iter_chains(E, b))
    C['sample: order gives the picks' if sd_ok else 'sample: ORDER MISMATCH'] += 1
    C['sample: OC1^max fails (my SAT, chains+additions)' if fails else 'sample: one move repairs (my code)'] += 1
for k in sorted(C): print(k, C[k])
