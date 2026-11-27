"""Cross-check rnd.c's two-round count (rnd2_count, Lemma RC2) against a forward simulation (bruter.rounds applied
twice, then every completion enumerated): the NUMBER of complete EFX allocations reachable by <= 2 rounds (free
completion) must agree on every start, and so must the one-round number (rnd.c RNDF).

    python3 kgen/rounds/xcheck2.py T SEED [nmax mmax]
"""
import sys, os, json, random, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, bruter, families


def all_completions(V, bases, out):
    n, m = len(V), len(V[0])
    used = set(g for b in bases for g in b); rest = [g for g in range(m) if g not in used]
    for asg in itertools.product(range(n), repeat=len(rest)):
        X = [set(b) for b in bases]
        for g, a in zip(rest, asg): X[a].add(g)
        Xl = [sorted(x) for x in X]
        if bruter.efx(V, Xl): out.add(tuple(tuple(x) for x in Xl))


def forward_counts(V, order):
    Y = bruter.sd(V, order); b0 = [frozenset([y]) for y in Y]
    S1 = bruter.rounds(V, b0)
    one = set(); two = set(); seen2 = set()
    for s in S1:
        all_completions(V, list(s), one)
        for s2 in bruter.rounds(V, list(s)):
            if s2 in seen2: continue
            seen2.add(s2); all_completions(V, list(s2), two)
    return Y, len(one), len(two | one)


def main():
    T, seed = int(sys.argv[1]), int(sys.argv[2])
    nmax = int(sys.argv[3]) if len(sys.argv) > 3 else 4; mmax = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    rng = random.Random(seed); C = collections.Counter(); bad = 0; t0 = time.time()
    insts = []
    for name, V in families.named():
        if len(V) <= nmax and len(V[0]) <= mmax: insts.append(V)
    for t in range(T):
        n = rng.randint(3, nmax); m = rng.randint(n + 1, mmax)
        insts.append(families.gen(rng.choice(families.KINDS), n, m, rng))
    for V in insts:
        res, _ = rndlib.analyze(V)
        for r in res:
            Y, f1, f2 = forward_counts(V, r['order'])
            c2, md = rndlib.two_rounds(V, list(r['picks']))
            c1 = r['counts']['RNDF']
            C['starts'] += 1; C['2-round < MD'] += (c2 < md); C['1-round < 2-round'] += (c1 < c2)
            if c1 != f1 or c2 != f2:
                bad += 1; print('MISMATCH', json.dumps(V), r['order'], 'rnd.c one/two', c1, c2, 'forward', f1, f2, flush=True)
    print(dict(C)); print('mismatches', bad, 'time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
