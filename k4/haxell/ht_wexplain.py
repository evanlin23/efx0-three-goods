"""Explain W^sub at the hardest states of one instance (k4/haxell.md §6), from the raw EFX0 definition (no shared code
with gstar_measure.c, so it also re-checks the climber's scores).

For every partial EFX0 state with a nonempty pool: the improving single moves (smaller pool, or same pool and larger
welfare, ending EFX0), and at states with none, every improving composite of two moves, named.  Moves (§6): transfer a
nonempty set of one holder's goods to an agent; swap the holders of two goods; rotate bundles along a cycle of agents.
Prints the states with the fewest improving composites and their composites.

    python3 k4/haxell/ht_wexplain.py "n m d g v g v ... d g v ..." [SHOW=3] [SUB=1] [AUG=0]
AUG=1 instead lists the states where no composite of at most two moves shrinks the pool, with their W^sub steps."""
import sys, itertools


def parse(s):
    w = list(map(int, s.split())); n, m = w[0], w[1]; t = 2; val = [[0] * m for _ in range(n)]
    for i in range(n):
        d = w[t]; t += 1
        for _ in range(d):
            val[i][w[t]] = w[t + 1]; t += 2
    return n, m, val


def run(n, m, val, show=3, sub=True, aug=False):
    POOL = -1

    def bundles(o):
        X = [[] for _ in range(n)]
        for g, a in enumerate(o):
            if a >= 0:
                X[a].append(g)
        return X

    def efx0(o):
        X = bundles(o)
        for i in range(n):
            mine = sum(val[i][g] for g in X[i])
            for j in range(n):
                if j != i and len(X[j]) >= 2 and sum(val[i][g] for g in X[j]) - min(val[i][g] for g in X[j]) > mine:
                    return False
        return True

    def welfare(o):
        return sum(val[a][g] for g, a in enumerate(o) if a >= 0)

    def moves(o):
        holders = list(range(n)) + [POOL]
        for h in holders:
            G = [g for g in range(m) if o[g] == h]
            for r in range(1, (len(G) if sub else 1) + 1):
                for S in itertools.combinations(G, r):
                    for b in range(n):
                        if b != h:
                            t = list(o)
                            for g in S:
                                t[g] = b
                            yield tuple(t), ('give', 'pool' if h < 0 else h, S, b)
        for g, h in itertools.combinations(range(m), 2):
            if o[g] != o[h]:
                t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t), ('swap', g, h)
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] != min(cyc):
                    continue
                to = {cyc[s]: cyc[(s + 1) % L] for s in range(L)}
                yield tuple(to.get(a, a) if a >= 0 else a for a in o), ('rotate', cyc)

    def better(o, t):
        p, q = o.count(POOL), t.count(POOL)
        return q < p or (q == p and welfare(t) > welfare(o))

    def shrinks(o, t):
        return t.count(POOL) < o.count(POOL)

    res = []
    for o in itertools.product(list(range(n)) + [POOL], repeat=m):
        if POOL not in o or not efx0(o):
            continue
        if aug:      # states with no pool-shrinking composite of at most two moves, and their W^sub steps
            if any(shrinks(o, t2) and efx0(t2) for t1, _ in moves(o) for t2, _ in moves(t1)) or \
               any(shrinks(o, t) and efx0(t) for t, _ in moves(o)):
                continue
            steps = [(mv, None, t) for t, mv in moves(o) if better(o, t) and efx0(t)]
            if not steps:
                steps = [(mv1, mv2, t2) for t1, mv1 in moves(o) for t2, mv2 in moves(t1) if better(o, t2) and efx0(t2)]
            res.append((len(steps), o, steps)); continue
        one = [mv for t, mv in moves(o) if better(o, t) and efx0(t)]
        if one:
            continue
        two = []
        for t1, mv1 in moves(o):
            for t2, mv2 in moves(t1):
                if better(o, t2) and efx0(t2):
                    two.append((mv1, mv2, t2))
        res.append((len(two), o, two))
    res.sort(key=lambda r: r[0])
    print('states with no pool-shrinking composite of two moves (their W^sub steps listed):' if aug else
          'states with no improving single move:', len(res))
    for cnt, o, two in res[:show]:
        X = bundles(o)
        print('state', X, 'pool', [g for g in range(m) if o[g] < 0], 'welfare', welfare(o),
              'improving two-move composites:', cnt)
        seen = set()
        for mv1, mv2, t2 in two:
            if t2 in seen:
                continue
            seen.add(t2)
            print('   ', mv1, *(['+', mv2] if mv2 else []), '->', bundles(t2), 'pool', [g for g in range(m) if t2[g] < 0],
                  'welfare', welfare(t2))
    return res


if __name__ == '__main__':
    a = dict(x.split('=') for x in sys.argv[2:] if '=' in x)
    n, m, val = parse(sys.argv[1])
    print('$ python3 k4/haxell/ht_wexplain.py', *sys.argv[1:]); print('values', val)
    run(n, m, val, int(a.get('SHOW', '3')), a.get('SUB', '1') == '1', a.get('AUG', '0') == '1')
