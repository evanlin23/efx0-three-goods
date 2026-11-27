"""Conjecture NOF at k = 4: when the plain neediest-first run pi fails, which agents' deferral works, and what are they
in pi?  Reports, for the working deferred agents: pick rank, frozen (another agent prefers its pick to its own),
whether it holds its top, position in pi (first agent?), length of its displacement chain (Lemma DC).

    python3 k4/sdc/nof_roles.py cores:FILES N SEED | screen | suite"""
import sys, os, json, random, gzip, collections
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_need import instances, rule_order
from sdf import frozen
from k3_disp import displacement

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/nof_roles.py', *sys.argv[1:])
    if src in ('screen', 'suite'):
        items = instances(src)
    else:
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(s) for s in sets)))
    for name, sets, vals, m in items:
        E = Enc(sets, vals, m); Y0, pi = rule_order(E, 'need2', False)
        if completable(E, Y0): continue
        C['plain run fails'] += 1
        F = frozen(E, Y0)
        work = [o for o in pi if completable(E, sd(E, [i for i in pi if i != o] + [o])[0])]
        C['working deferrals: %d' % len(work)] += 1
        for o in work:
            R = sorted(E.R[o], key=lambda g: (-E.v[o][g], g))
            ch, hole = displacement(E, pi, Y0, o)
            C['working o: pick rank %d' % (R.index(Y0[o]) if Y0[o] is not None else 9)] += 1
            C['working o: frozen %s' % (o in F)] += 1
            C['working o: first in pi %s' % (o == pi[0])] += 1
            C['working o: chain length %d' % (len(ch) - 1)] += 1
        C['some working o is frozen and holds its top'] += any(o in F and Y0[o] == sorted(E.R[o], key=lambda g: (-E.v[o][g], g))[0] for o in work)
    for k in sorted(C, key=str): print(k, C[k])
