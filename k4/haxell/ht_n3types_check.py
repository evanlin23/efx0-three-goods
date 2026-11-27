"""Independent re-check of ht_n3types.py (P^sub at n = 3 over strict type profiles; k4/haxell.md §6) in pure Python,
sharing only the instance generator: for a random sample of the type-profile classes, every state is enumerated from
the raw EFX0 definition, the number of partial EFX0 states is compared with gstar_measure's, and every partial EFX0
state with a nonempty pool must have a P^sub step: at most two moves (set transfers, swaps with the pool as a holder,
rotations of bundles along cycles of agents) reaching a partial EFX0 allocation with a smaller pool, or with the same
pool where no agent is worse and some agent is strictly better.

    python3 k4/haxell/ht_n3types_check.py [K=3] [MMAX=9] [SAMPLE=300] [SEED=1]"""
import sys, os, itertools, random, subprocess, time
HERE = os.path.dirname(os.path.abspath(__file__))
ARGV = sys.argv[1:]; a = dict(x.split('=') for x in ARGV if '=' in x)
K = a.get('K', '3'); MMAX = a.get('MMAX', '9'); SAMPLE = int(a.get('SAMPLE', '300')); SEED = int(a.get('SEED', '1'))
sys.argv = ['x', 'K=' + K, 'MMAX=' + MMAX]; sys.path.insert(0, HERE)
import ht_n3types as T


def parse(ln):
    w = list(map(int, ln.split())); n, m = w[0], w[1]; t = 2; val = [[0] * m for _ in range(n)]
    for i in range(n):
        d = w[t]; t += 1
        for _ in range(d):
            val[i][w[t]] = w[t + 1]; t += 2
    return n, m, val


def check(n, m, val):
    def bundles(o):
        X = [[] for _ in range(n)]
        for g, h in enumerate(o):
            if h >= 0:
                X[h].append(g)
        return X

    def efx0(o):
        X = bundles(o)
        for i in range(n):
            mine = sum(val[i][g] for g in X[i])
            for j in range(n):
                if j != i and len(X[j]) >= 2 and sum(val[i][g] for g in X[j]) - min(val[i][g] for g in X[j]) > mine:
                    return False
        return True

    def vals(o):
        return [sum(val[i][g] for g in B) for i, B in enumerate(bundles(o))]

    def moves(o):
        for h in list(range(n)) + [-1]:
            G = [g for g in range(m) if o[g] == h]
            for r in range(1, len(G) + 1):
                for S in itertools.combinations(G, r):
                    for b in range(n):
                        if b != h:
                            t = list(o)
                            for g in S:
                                t[g] = b
                            yield tuple(t)
        for g, h in itertools.combinations(range(m), 2):
            if o[g] != o[h]:
                t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t)
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] == min(cyc):
                    to = {cyc[s]: cyc[(s + 1) % L] for s in range(L)}
                    yield tuple(to.get(x, x) if x >= 0 else x for x in o)

    nstates = 0; bad = []
    for o in itertools.product(list(range(n)) + [-1], repeat=m):
        if not efx0(o):
            continue
        nstates += 1
        if -1 not in o:
            continue
        p = o.count(-1); v0 = vals(o)

        def improves(t):
            if t.count(-1) > p or not efx0(t):
                return False
            if t.count(-1) < p:
                return True
            v1 = vals(t)
            return all(x >= y for x, y in zip(v1, v0)) and any(x > y for x, y in zip(v1, v0))
        if any(improves(t) for t in moves(o)):
            continue
        if not any(improves(t2) for t1 in moves(o) for t2 in moves(t1)):
            bad.append(o)
    return nstates, bad


if __name__ == '__main__':
    print('$ python3 k4/haxell/ht_n3types_check.py', *ARGV, flush=True)
    t0 = time.time()
    allinst = [ln for m, key in T.G.shapes() for ln in T.instances(m, key)]
    rng = random.Random(SEED); sample = rng.sample(allinst, min(SAMPLE, len(allinst)))
    out = subprocess.run([os.path.join(HERE, 'gstar_measure'), '2', '1', '19', '1'], input='\n'.join(sample) + '\n',
                         capture_output=True, text=True).stdout.strip().split('\n')
    mism = 0; total = 0; fails = 0
    for ln, o in zip(sample, out):
        n, m, val = parse(ln)
        ns, bad = check(n, m, val); total += ns
        cs = int(o.split()[3]); c19 = int(o.split()[o.split().index('phi19') + 1])
        if ns != cs or bool(bad) != bool(c19):
            mism += 1; print('MISMATCH', ln, 'python states', ns, 'C states', cs, 'python stuck', len(bad), 'C stuck', c19)
        fails += len(bad)
    print('sample %d of %d classes; partial EFX0 states %d; Python P^sub stuck states %d; mismatches with C %d' %
          (len(sample), len(allinst), total, fails, mism))
    print('time %.0f s' % (time.time() - t0))
