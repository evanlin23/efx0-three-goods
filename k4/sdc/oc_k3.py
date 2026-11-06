"""OC and OC1 at k = 3 (k4/sdc.md §29): on the certified k = 3 cores with n = 5, 6 (`results/certs_5_6.json.gz`), random
strict balanced profiles (three goods a > b > c with a < b + c), every order (n = 5) or ORD sampled orders (n = 6).
Draft and Exchange needs up to 4n trades from its draft with its one-finisher completion; here: how many improving
chains (de_free.py) before the picks have a free / one-absorber completion?

    python3 k4/sdc/oc_k3.py SEED PROFILES_PER_CORE ORD"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
import de_free as DF
from sdclib import Enc
from sdc_orders import sd
from oc_absorb import extends_A

DF.CHAIN_ONLY = True

if __name__ == '__main__':
    seed, P, ORD = map(int, sys.argv[1:4]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/oc_k3.py', *sys.argv[1:], flush=True)
    cores = json.load(gzip.open(os.path.join(_paths.ROOT, 'results', 'certs_5_6.json.gz')))
    for core in cores:
        sets = core['sets']; n = len(sets); m = core['m']
        for p in range(P):
            vals = []
            for S in sets:
                while True:
                    a, b, c = sorted(rng.sample(range(1, 30), 3), reverse=True)
                    if a < b + c: break
                perm = list(S); rng.shuffle(perm); d = dict(zip(perm, (a, b, c))); vals.append([d[g] for g in S])
            E = Enc(sets, vals, m); C['profiles'] += 1; res = {}
            orders = list(itertools.permutations(range(n))) if n <= 5 else [tuple(rng.sample(range(n), n)) for _ in range(ORD)]
            for o in orders:
                Y = tuple(sd(E, list(o))[0])
                if Y not in res:
                    base = [-1] * m
                    for i, g in enumerate(Y):
                        if g is not None: base[g] = i
                    base = tuple(base); r = {}
                    for nm, t in (('free', lambda b: DF.extends(E, b)), ('one absorber', lambda b: extends_A(E, b, 1))):
                        r[nm] = 0 if t(base) else (1 if any(t(b2) for b2 in DF.iter_chains(E, base)) else None)
                    res[Y] = r
                    if None in r.values(): print('MORE THAN ONE CHAIN', json.dumps((sets, vals)), 'order', o, r, flush=True)
                C['starts'] += 1
                for nm, d in res[Y].items(): C[nm + ': chains needed %s' % d] += 1
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
