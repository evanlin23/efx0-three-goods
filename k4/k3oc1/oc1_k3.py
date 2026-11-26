"""OC1 at k = 3, exact (k3lib's ordinal model): for every ranking profile (or a random sample) of each hypergraph and
every serial-dictatorship order, do the picks have a one-absorber completion, or does one improving chain give one?

    python3 k4/k3oc1/oc1_k3.py SOURCE [PROFILES SEED] [dead=D]
SOURCE: small:N (connected cores of results/certs_small_m.json.gz with n = N), certs:N (results/certs_5_6.json.gz),
        rand:N:M:COUNT (random 3-uniform hypergraphs, n = N agents on M goods).  PROFILES = 0: every profile.
dead=D adds D goods valued by nobody.  Hard starts (no completion of the picks) are printed as HARD lines."""
import sys, os, json, gzip, random, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from k3lib import sd, base_of, completion, chains, vals


def hypergraphs(src, rng):
    kind, *a = src.split(':')
    if kind == 'small':
        for c in json.load(gzip.open(os.path.join(ROOT, 'results', 'certs_small_m.json.gz'))):
            if c['n'] == int(a[0]): yield c['sets'], c['m']
    elif kind == 'certs':
        for c in json.load(gzip.open(os.path.join(ROOT, 'results', 'certs_5_6.json.gz'))):
            if c['n'] == int(a[0]): yield c['sets'], c['m']
    elif kind == 'rand':
        n, m, cnt = map(int, a)
        for _ in range(cnt):
            yield [sorted(rng.sample(range(m), 3)) for _ in range(n)], m


def profiles(sets, P, rng):
    perms = [list(itertools.permutations(s)) for s in sets]
    if P == 0:
        yield from itertools.product(*perms)
    else:
        for _ in range(P): yield tuple(rng.choice(p) for p in perms)


if __name__ == '__main__':
    args = [x for x in sys.argv[1:] if not x.startswith('dead=')]
    dead = int(next((x[5:] for x in sys.argv[1:] if x.startswith('dead=')), 0))
    src = args[0]; P = int(args[1]) if len(args) > 1 else 0; seed = int(args[2]) if len(args) > 2 else 1
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/k3oc1/oc1_k3.py', *sys.argv[1:], flush=True)
    for sets, m in hypergraphs(src, rng):
        m2 = m + dead; n = len(sets); C['hypergraphs'] += 1
        for rk in profiles(sets, P, rng):
            V = vals(rk); C['profiles'] += 1; seen = {}
            for o in itertools.permutations(range(n)):
                Y = tuple(sd(rk, m2, o)); C['starts'] += 1
                if Y not in seen:
                    b = base_of(Y, m2)
                    if completion(rk, m2, b, 1, V) is not None: seen[Y] = 0
                    else:
                        ok = None
                        for nb, d in chains(rk, m2, b, V):
                            if completion(rk, m2, nb, 1, V) is not None: ok = d; break
                        seen[Y] = 1 if ok else None
                        print('HARD', json.dumps([list(r) for r in rk]), m2, 'order', o, 'picks', Y,
                              'chain', ok if ok is None else (ok[0], {k: list(v) for k, v in ok[1].items()}), flush=True)
                        if ok is None: print('COUNTEREXAMPLE', flush=True)
                C['chains needed %s' % seen[Y]] += 1
            C['distinct picks'] += len(seen); C['hard distinct picks'] += sum(1 for v in seen.values() if v)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
