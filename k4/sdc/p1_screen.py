import sys, os, random, json
import _paths
os.chdir(_paths.DE4)
from ss_screen import screen_set

from sdclib import *
rng = random.Random(int(sys.argv[1])); R = int(sys.argv[2])
bad = 0; tot = 0
for name, I in screen_set():
    sets = I.sets; vals = [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)]
    E = Enc(sets, vals, I.m)
    for r in range(R):
        st = random_start(E, rng) if r else None
        asg, steps = climb(E, rng, st)
        tot += 1
        B = [[g for g in range(E.m) if asg[g] == i] for i in range(E.n)]
        assert efx0(E, B)
        if E.n in asg:
            bad += 1
            print('BAD', name, json.dumps((sets, vals, asg)), flush=True)
    print(name, I.n, I.m, 'ok', flush=True)
print('total', tot, 'bad', bad)
