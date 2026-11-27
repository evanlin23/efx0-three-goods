"""OC1 on the K4.MC2 class (k4/oc1_hall.md §17): random strict profiles of connected k = 4 cores in which no agent
has two private goods (a minimal counterexample to TARGET4 has none, K4.MC2).  Every order: one-absorber completion
(SAT, oc_absorb.extends_A) at the picks, else one chain or ring (de_free.moves) then one; counts the starts with two
or more agents without a pick, and prints any OC1 failure.

    python3 k4/oc1_hall/mc2_oc1.py CORES.json.gz[,...] N SEED
"""
import sys, os, json, gzip, random, itertools, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, base_of_picks
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
import _paths
DF.CHAIN_ONLY = False


def two_private(sets):
    for i, S in enumerate(sets):
        if sum(1 for g in S if all(g not in T for j, T in enumerate(sets) if j != i)) >= 2: return True
    return False


if __name__ == '__main__':
    files, N, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed)
    os.chdir(_paths.DE4)
    from de4lib import random_profile
    os.chdir(_paths.ROOT)
    cores = []
    for fn in files.split(','):
        cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
    mc2 = [s for s in cores if not two_private(s)]
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/mc2_oc1.py', *sys.argv[1:], '| cores', len(cores), 'in the K4.MC2 class', len(mc2), flush=True)
    for t in range(N):
        sets = rng.choice(mc2); vals = random_profile(sets, rng); m = 1 + max(max(s) for s in sets)
        I = Inst(sets, vals, m); E = Enc(sets, vals, m); seen = {}
        C['instances'] += 1
        for od in itertools.permutations(range(len(sets))):
            Y = picks(I, od)
            if Y not in seen:
                b = base_of_picks(I, Y)
                if extends_A(E, b, 1): seen[Y] = 'picks'
                elif any(extends_A(E, b2, 1) for b2 in DF.moves(E, b)): seen[Y] = 'one move'
                else:
                    seen[Y] = 'FAIL'
                    print('OC1 FAILS (K4.MC2 class)', json.dumps((sets, vals)), 'order', od, 'picks', Y, flush=True)
                C['distinct starts'] += 1; C['distinct starts: %s' % seen[Y]] += 1
                C['distinct starts with >= 2 agents without a pick'] += sum(1 for y in Y if y is None) >= 2
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
