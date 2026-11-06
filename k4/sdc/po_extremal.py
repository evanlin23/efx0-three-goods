"""An extremal choice of the order (k4/sdc.md §30).  Orders give exactly the Pareto-optimal matchings (Lemma SDPO).
Choose the matching maximizing a potential, and ask whether every maximizer (and some maximizer) has a one-absorber
completion with no chain (oc_absorb.extends_A, A = 1).  Potentials on a Pareto-optimal matching mu with junk J:
  tops     : number of agents holding their top good
  ranks    : sum over agents of (|R_i| - rank of mu_i), unmatched 0
  nofrozen : minus the number of frozen agents (pick wanted by another agent)
  nodanger : minus the number of frozen agents valuing junk
  excess   : minus the total junk excess sum over frozen x of max(0, v_x(J cap R_x) - v_x(mu_x))
  util     : sum of values
  junkval  : minus the total value of junk to all agents (the picks absorb the most value)

    python3 k4/sdc/po_extremal.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from oc_absorb import extends_A


def feats(E, Y):
    n, m = E.n, E.m
    picked = set(g for g in Y if g is not None); J = [g for g in range(m) if g not in picked]
    rank = lambda i, g: sorted(E.R[i], key=lambda h: -E.v[i][h]).index(g)
    def wants(i, j):
        if Y[j] is None or i == j: return False
        if Y[i] is None: return E.v[i].get(Y[j], 0) > 0
        return E.v[i].get(Y[j], 0) > E.v[i][Y[i]]
    frozen = [j for j in range(n) if any(wants(i, j) for i in range(n))]
    return {
        'tops': sum(1 for i in range(n) if Y[i] is not None and rank(i, Y[i]) == 0),
        'ranks': sum(len(E.R[i]) - rank(i, Y[i]) for i in range(n) if Y[i] is not None),
        'nofrozen': -len(frozen),
        'nodanger': -sum(1 for x in frozen if any(E.v[x].get(g, 0) > 0 for g in J)),
        'excess': -sum(max(0, sum(E.v[x].get(g, 0) for g in J) - E.v[x][Y[x]]) for x in frozen),
        'util': sum(E.v[i][Y[i]] for i in range(n) if Y[i] is not None),
        'junkval': -sum(E.v[i].get(g, 0) for i in range(n) for g in J),
    }


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/po_extremal.py', *sys.argv[1:], flush=True)
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
    else:
        items = instances(src)
    names = ['tops', 'ranks', 'nofrozen', 'nodanger', 'excess', 'util', 'junkval']
    for name, sets, vals, m in items:
        n = len(sets)
        if n > 5: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        outs = {}
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y in outs: continue
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            outs[Y] = (feats(E, Y), extends_A(E, tuple(base), 1))
        C['instances where some order works with no chain'] += any(ok for _, ok in outs.values())
        for p in names:
            best = max(f[p] for f, _ in outs.values())
            tied = [ok for f, ok in outs.values() if f[p] == best]
            C[p + ': every maximizer works'] += all(tied)
            C[p + ': some maximizer works'] += any(tied)
        for p, q in (('nofrozen', 'excess'), ('excess', 'nofrozen'), ('nodanger', 'excess'), ('excess', 'junkval'), ('junkval', 'excess')):
            best = max((f[p], f[q]) for f, _ in outs.values())
            tied = [ok for f, ok in outs.values() if (f[p], f[q]) == best]
            C['(%s, %s): every maximizer works' % (p, q)] += all(tied)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
