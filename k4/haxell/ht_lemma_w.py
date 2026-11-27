"""Independent check of Lemma W (k4/haxell.md §6), written separately from gstar_measure.c (shares only the
definitions).  For every partial EFX0 allocation with a nonempty pool: is there a composite of at most two moves
(move one good to an agent; swap the holders of two goods, the pool counting as a holder; rotate the bundles along a
cycle of two or more agents) giving a partial EFX0 allocation with a smaller pool, or the same pool and strictly
larger total value?  Prints the stuck states (none expected) and a count.

    python3 k4/haxell/ht_lemma_w.py SRC [NMAX=3] [MMAX=6] [LIMIT=200]"""
import sys, itertools, collections, json, time
from ht_lib import instances


def check(sets, vals, m):
    n = len(sets); R = [dict(zip(s, v)) for s, v in zip(sets, vals)]

    def ok(o):
        X = [[g for g in range(m) if o[g] == j] for j in range(n)]
        for i in range(n):
            mine = sum(R[i].get(g, 0) for g in X[i])
            for j in range(n):
                if j != i:
                    for h in X[j]:
                        if sum(R[i].get(g, 0) for g in X[j] if g != h) > mine:
                            return False
        return True

    def welfare(o):
        return sum(R[o[g]].get(g, 0) for g in range(m) if o[g] >= 0)

    cycles = []
    for L in range(2, n + 1):
        for sub in itertools.combinations(range(n), L):
            for rest in itertools.permutations(sub[1:]):
                cycles.append((sub[0],) + rest)

    def moves(o):
        for g in range(m):
            for b in range(n):
                if b != o[g]:
                    t = list(o); t[g] = b; yield tuple(t)
        for g, h in itertools.combinations(range(m), 2):
            if o[g] != o[h]:
                t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t)
        for c in cycles:
            to = {c[i]: c[(i + 1) % len(c)] for i in range(len(c))}
            yield tuple(to.get(x, x) if x >= 0 else x for x in o)

    S = [o for o in itertools.product(range(-1, n), repeat=m) if ok(o)]
    stuck = []
    for s in S:
        p = s.count(-1)
        if p == 0:
            continue
        w = welfare(s); found = False
        for t1 in moves(s):
            for t in itertools.chain([t1], moves(t1)):
                if t.count(-1) <= p and (t.count(-1) < p or welfare(t) > w) and ok(t):
                    found = True; break
            if found:
                break
        if not found:
            stuck.append(s)
    return len(S), stuck


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    nmax = int(args.get('NMAX', '3')); mmax = int(args.get('MMAX', '6')); limit = int(args.get('LIMIT', '200'))
    print('$ python3 k4/haxell/ht_lemma_w.py', *sys.argv[1:], flush=True)
    C = collections.Counter(); t0 = time.time()
    for name, sets, vals, m in instances(sys.argv[1]):
        if len(sets) > nmax or m > mmax:
            continue
        if C['instances'] >= limit:
            break
        nS, stuck = check(sets, vals, m)
        C['instances'] += 1; C['partial EFX0 states'] += nS; C['stuck states'] += len(stuck)
        if stuck:
            print('STUCK', name, json.dumps((sets, vals)), stuck[:3], flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
