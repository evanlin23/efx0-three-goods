"""The n = 2 proof attempt (k4/haxell.md §6): is pure augmentation within two moves enough at n = 2 when values are
strict?  Tested on random instances with real values (ties have probability 0) and any k.

Claim A2.  Let (X_A, X_B) be a partial EFX0 allocation of two agents with a nonempty pool P.  Then some composite of at
most two moves of k4/haxell.md §6 (set transfers from an agent or the pool to an agent, swaps of two goods' holders, the
trade) reaches a partial EFX0 allocation with a smaller pool.  (Strong form: with every pooled g as the placed good.)
If Claim A2 holds, W^sub and L^sub at n = 2 reduce to it for strict values.  The first version of this script tested
only the families "B's bundle grows", "A's bundle grows" and "trade, then place", which miss "swap, then place"; that
is why it reported failures that the exact checkers do not confirm.

States: random allocations of the goods to A, B and the pool, kept when partial EFX0 with a nonempty pool.  For each,
every composite of at most two moves is enumerated; the kind of the first augmenting composite found is counted.

    python3 k4/haxell/ht_n2claim.py N SEED MMAX [KMAX=MMAX] [STATES=200] [RELEVANT=0]"""
import sys, random, itertools, time


def tau(v, B):
    return sum(v[g] for g in B) - min(v[g] for g in B) if len(B) >= 2 else 0.0


def ok(vA, vB, YA, YB):
    return sum(vA[g] for g in YA) >= tau(vA, YB) - 1e-12 and sum(vB[g] for g in YB) >= tau(vB, YA) - 1e-12


def moves(o, m):
    """(new owner tuple, kind) for every move of o (0 = A, 1 = B, -1 = pool)"""
    for h in (0, 1, -1):
        G = [g for g in range(m) if o[g] == h]
        for r in range(1, len(G) + 1):
            for T in itertools.combinations(G, r):
                for b in (0, 1):
                    if b != h:
                        t = list(o)
                        for g in T:
                            t[g] = b
                        yield tuple(t), ('place' if h < 0 else 'give') + ('1' if r == 1 else 'S')
    for g, h in itertools.combinations(range(m), 2):
        if o[g] != o[h]:
            t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t), 'swapP' if -1 in (o[g], o[h]) else 'swapAB'
    yield tuple(1 - x if x >= 0 else x for x in o), 'trade'


def augment(vA, vB, o, m):
    """kind of an augmenting composite of at most two moves, or None"""
    p = o.count(-1)
    def good(t):
        return t.count(-1) < p and ok(vA, vB, [g for g in range(m) if t[g] == 0], [g for g in range(m) if t[g] == 1])
    for t, k in moves(o, m):
        if good(t):
            return k
    for t1, k1 in moves(o, m):
        for t2, k2 in moves(t1, m):
            if good(t2):
                return k1 + '+' + k2
    return None


if __name__ == '__main__':
    N, SEED, MMAX = map(int, sys.argv[1:4])
    a = dict(x.split('=') for x in sys.argv[4:] if '=' in x)
    RELEVANT = a.get('RELEVANT', '0') == '1'; KMAX = int(a.get('KMAX', str(MMAX))); STATES = int(a.get('STATES', '200'))
    print('$ python3 k4/haxell/ht_n2claim.py', *sys.argv[1:], flush=True)
    rng = random.Random(SEED); t0 = time.time(); import collections; C = collections.Counter()
    for t in range(N):
        m = rng.randint(3, MMAX)
        def vals():
            R = rng.sample(range(m), rng.randint(1, min(KMAX, m)))
            sk = rng.random() < 0.5            # half the instances: one or two big goods
            return [(rng.random() * (30 if sk and rng.random() < 0.2 else 1)) if g in R else 0.0 for g in range(m)]
        vA, vB = vals(), vals()
        if RELEVANT and any(vA[g] == 0 and vB[g] == 0 for g in range(m)):
            continue                                   # RELEVANT=1: every good is valued by someone
        for _ in range(STATES):
            own = [rng.choice((0, 1, -1)) for _ in range(m)]
            if -1 not in own:
                continue
            XA = [g for g in range(m) if own[g] == 0]; XB = [g for g in range(m) if own[g] == 1]
            if not ok(vA, vB, XA, XB):
                continue
            C['states'] += 1
            r = augment(vA, vB, tuple(own), m)
            C[r or 'FAIL'] += 1
            if r is None:
                print('FAIL m', m, 'vA', [round(x, 4) for x in vA], 'vB', [round(x, 4) for x in vB], 'XA', XA, 'XB', XB,
                      'pool', [g for g in range(m) if own[g] == -1], flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
