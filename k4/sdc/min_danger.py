"""Can the order be chosen to leave at most one dangerous agent (k4/sdc.md §30)?  For an order pi with picks Y and junk
J: an agent is frozen if another agent wants its pick; D = frozen agents valuing some junk good (the agents Theorem DT+
does not handle); D' = frozen agents whose junk goods are worth more in total than their pick (junk alone can form a
danger set).  Per instance: the least |D| and |D'| over all orders, and whether an order with |D| <= 1 also has a
one-absorber completion or a canonical repairing chain.

    python3 k4/sdc/min_danger.py screen|suite|special|logs|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL


def danger(E, Y):
    n, m = E.n, E.m
    picked = set(g for g in Y if g is not None); J = [g for g in range(m) if g not in picked]
    def wants(i, j):
        if Y[j] is None or i == j: return False
        if Y[i] is None: return E.v[i].get(Y[j], 0) > 0
        return E.v[i].get(Y[j], 0) > E.v[i][Y[i]]
    frozen = [j for j in range(n) if any(wants(i, j) for i in range(n))]
    D = [j for j in frozen if any(E.v[j].get(g, 0) > 0 for g in J)]
    D2 = [j for j in frozen if sum(E.v[j].get(g, 0) for g in J) > E.v[j][Y[j]]]
    return D, D2


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/min_danger.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    elif src == 'logs':
        import re, glob
        seen = set(); items = []
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try: sets, vals = json.loads(mt.group(1))
                    except Exception: continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4: continue
                    key = json.dumps((sets, vals))
                    if key in seen: continue
                    seen.add(key); items.append(('log%d' % len(items), sets, vals, 1 + max(max(a) for a in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        n = len(sets)
        if n > 6: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        best = None; best2 = None
        for o in itertools.permutations(range(n)):
            Y = sd(E, list(o))[0]; D, D2 = danger(E, Y)
            best = len(D) if best is None else min(best, len(D)); best2 = len(D2) if best2 is None else min(best2, len(D2))
        C['least |D| over orders = %d' % best] += 1
        C["least |D'| over orders = %d" % best2] += 1
        if best2 >= 1 and C['shown2'] < 3:
            C['shown2'] += 1; print("EVERY ORDER HAS |D'| >= 1", name, json.dumps((sets, vals)), flush=True)
        if best >= 2 and C['shown'] < 0:
            C['shown'] += 1; print('EVERY ORDER HAS |D| >= 2', name, json.dumps((sets, vals)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
