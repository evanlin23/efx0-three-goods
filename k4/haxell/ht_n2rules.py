"""Toward a proof of Claim A2 at n = 2 (k4/haxell.md §6): at strict random states where no single placement of the
pooled good g works, which simple rules give an augmenting step?  Rules (each is at most two moves of §6):

  T     trade, then place g with either agent;
  A1    g to A, then one good of A's (g excluded) to B;        B1  g to B, then one good of B's to A;
  AS    g to A, then a set of A's goods (g excluded) to B;     BS  the same for B;
  Ag    g to B, then a set of A's goods to B (B gets X_B + g + S, A keeps X_A - S);   Bg  symmetric;
  SW    swap a good of A's with a good of B's, then place g with either agent.

Prints, for the hard states, how many each rule solves, which minimal sets of rules cover all of them, and every
state that no rule solves.

    python3 k4/haxell/ht_n2rules.py N SEED MMAX [KMAX=MMAX] [STATES=200] [RELEVANT=0] [POOL1=1]"""
import sys, random, itertools, collections, time


def tau(v, B):
    return sum(v[g] for g in B) - min(v[g] for g in B) if len(B) >= 2 else 0.0


def ok(vA, vB, YA, YB):
    return sum(vA[g] for g in YA) >= tau(vA, YB) - 1e-12 and sum(vB[g] for g in YB) >= tau(vB, YA) - 1e-12


def subsets(G, lo=1):
    for r in range(lo, len(G) + 1):
        yield from itertools.combinations(G, r)


def rules(vA, vB, XA, XB, g):
    R = set()
    if ok(vA, vB, XB + [g], XA) or ok(vA, vB, XB, XA + [g]):
        R.add('T')
    for a in XA:
        if ok(vA, vB, [x for x in XA if x != a] + [g], XB + [a]):
            R.add('A1')
    for b in XB:
        if ok(vA, vB, XA + [b], [x for x in XB if x != b] + [g]):
            R.add('B1')
    for S in subsets(XA, 2):
        if ok(vA, vB, [x for x in XA if x not in S] + [g], XB + list(S)):
            R.add('AS')
    for S in subsets(XB, 2):
        if ok(vA, vB, XA + list(S), [x for x in XB if x not in S] + [g]):
            R.add('BS')
    for S in subsets(XA, 1):
        if ok(vA, vB, [x for x in XA if x not in S], XB + [g] + list(S)):
            R.add('Ag')
    for S in subsets(XB, 1):
        if ok(vA, vB, XA + [g] + list(S), [x for x in XB if x not in S]):
            R.add('Bg')
    for a in XA:
        for b in XB:
            YA = [x for x in XA if x != a] + [b]; YB = [x for x in XB if x != b] + [a]
            if ok(vA, vB, YA + [g], YB) or ok(vA, vB, YA, YB + [g]):
                R.add('SW')
    return R


if __name__ == '__main__':
    N, SEED, MMAX = map(int, sys.argv[1:4])
    a = dict(x.split('=') for x in sys.argv[4:] if '=' in x)
    RELEVANT = a.get('RELEVANT', '0') == '1'; KMAX = int(a.get('KMAX', str(MMAX))); STATES = int(a.get('STATES', '200')); POOL1 = a.get('POOL1', '1') == '1'
    print('$ python3 k4/haxell/ht_n2rules.py', *sys.argv[1:], flush=True)
    rng = random.Random(SEED); t0 = time.time(); C = collections.Counter(); hard = []
    for t in range(N):
        m = rng.randint(3, MMAX)
        def vals():
            R = rng.sample(range(m), rng.randint(1, min(KMAX, m)))
            sk = rng.random() < 0.5
            return [(rng.random() * (30 if sk and rng.random() < 0.2 else 1)) if g in R else 0.0 for g in range(m)]
        vA, vB = vals(), vals()
        if RELEVANT and any(vA[g] == 0 and vB[g] == 0 for g in range(m)):
            continue                                   # RELEVANT=1: every good is valued by someone
        for _ in range(STATES):
            g = rng.randrange(m)
            own = [rng.choice((0, 1)) if x != g else -1 for x in range(m)] if POOL1 else \
                [rng.choice((0, 1, -1)) if x != g else -1 for x in range(m)]
            XA = [x for x in range(m) if own[x] == 0]; XB = [x for x in range(m) if own[x] == 1]
            if not ok(vA, vB, XA, XB):
                continue
            C['states'] += 1
            if ok(vA, vB, XA + [g], XB) or ok(vA, vB, XA, XB + [g]):
                continue
            C['hard states'] += 1
            R = frozenset(rules(vA, vB, XA, XB, g)); hard.append(R)
            for r in R:
                C['solved by ' + r] += 1
            if not R:
                print('NO RULE m', m, 'vA', [round(x, 4) for x in vA], 'vB', [round(x, 4) for x in vB], 'XA', XA,
                      'XB', XB, 'g', g, flush=True)
    for k in sorted(C):
        print(k, C[k])
    names = ['T', 'A1', 'B1', 'AS', 'BS', 'Ag', 'Bg', 'SW']
    covers = []
    for r in range(1, len(names) + 1):
        for menu in itertools.combinations(names, r):
            if all(R & set(menu) for R in hard):
                covers.append(menu)
        if covers:
            break
    print('smallest rule menus covering every hard state:', covers)
    print('time %.0f s' % (time.time() - t0))
