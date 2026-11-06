"""Lemma N in the runs (k4/sdc.md §12): for every frozen agent x of the plain neediest-first run (R1 or not) and every
needer j of x's pick y (j prefers y to its own pick), at the time tau when x took y:
  direct   = y was j's favourite available good at tau;
  need_j   = j's need at tau (top - next two of its available goods).
Lemma N: if direct, then need_x(tau) >= need_j(tau); if moreover need_j(tau) > 0, x's two best other goods available
at tau are worth less than y, so x is exposed (a set of its goods in J + {Y_o} worth more than y) only if x was fresh,
and then one good meets every danger set.  Checks these consequences and counts the other cases.

    python3 k4/sdc/lemma_n_check.py screen|cores:FILES N SEED [--r1]"""
import sys, os, json, random, gzip, itertools, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order, score


def run(E, r1):
    Y, pi = rule_order(E, 'need2', r1)
    left = set(range(E.m)); avail = {}; t_of = {}; snap = {}
    for t, i in enumerate(pi):
        snap[t] = set(left); t_of[i] = t
        if Y[i] is not None: left.discard(Y[i])
    return Y, pi, snap, t_of


if __name__ == '__main__':
    R1 = '--r1' in sys.argv; sys.argv = [a for a in sys.argv if a != '--r1']
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/lemma_n_check.py', *sys.argv[1:], '--r1' if R1 else '')
    if src == 'screen':
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
        E = Enc(sets, vals, m); Y, pi, snap, t_of = run(E, R1)
        o = pi[-1]; picked = set(g for g in Y if g is not None); pool = (set(range(m)) - picked) | ({Y[o]} if Y[o] is not None else set())
        for x in range(E.n):
            if x == o or Y[x] is None: continue
            y = Y[x]; tau = t_of[x]; G = snap[tau]
            needers = [j for j in range(E.n) if j != x and E.v[j].get(y, 0) > (E.v[j][Y[j]] if Y[j] is not None else 0)]
            if not needers: continue
            own = [g for g in E.R[x] if g != y and g in pool]
            Ts = [T for r in range(1, len(own) + 1) for T in itertools.combinations(own, r) if sum(E.v[x][g] for g in T) > E.v[x][y]]
            exposed = bool(Ts)
            for j in needers:
                favj = max((g for g in E.R[j] if g in G), key=lambda h: (E.v[j][h], -h), default=None)
                direct = favj == y
                nj = score(E, j, G, 'need2'); nx = score(E, x, G, 'need2')
                C['pairs'] += 1; C['direct' if direct else 'indirect'] += 1
                if direct:
                    C['direct: need_x >= need_j'] += nx >= nj
                    if nj > 0:
                        C['direct, need_j > 0'] += 1
                        avail_low = sorted((E.v[x][g] for g in E.R[x] if g in G and g != y), reverse=True)
                        C['direct, need_j > 0: x big-top on available'] += sum(avail_low[:2]) < E.v[x][y]
                        if exposed:
                            fresh = all(g in G for g in E.R[x])
                            cost1 = any(all(g in T for T in Ts) for g in own)
                            C['direct, need_j > 0, x exposed'] += 1
                            C['direct, need_j > 0, x exposed: fresh'] += fresh
                            C['direct, need_j > 0, x exposed: cost 1'] += cost1
    for k in sorted(C, key=str): print(k, C[k])
