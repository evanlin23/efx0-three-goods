"""P1 on random instances: SAT climbs (sdclib.climb) from the empty allocation and from random partial EFX0 allocations;
a climb that ends with an unallocated good is a stuck Pareto maximum.
    python3 k4/sdc/p1_sat_rand.py SEED INSTANCES n m k3|k4|k4p CLIMBS"""
import sys, random, json
from sdclib import Enc, climb, random_start, efx0
from p1_rand import rand_inst
seed, n, m, T, kind, R = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], int(sys.argv[6])
sizes = [3] if kind == 'k3' else [4] if kind == 'k4p' else [3, 4]
rng = random.Random(seed); c = 0; runs = 0
for t in range(T):
    Rs, v = rand_inst(rng, n, m, sizes)
    sets = Rs; vals = [[v[i][g] for g in Rs[i]] for i in range(n)]
    E = Enc(sets, vals, m)
    for r in range(R):
        asg, steps = climb(E, rng, random_start(E, rng) if r else None); runs += 1
        if n in asg:
            c += 1
            if c <= 3: print('P1-FAIL', json.dumps((sets, vals, asg)), flush=True)
            break
print(kind, n, m, 'instances', T, 'climbs', runs, 'instances with a stuck maximum', c, flush=True)
