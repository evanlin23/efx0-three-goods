"""Unrestricted k (k4/ksens.md §8): every agent values every good (k = m), strict positive values, n = 3, 4.  Every
start is then a maximum-matching start (m >= n, every agent picks).  For every start: the least number of rounds of
vertex-disjoint improving chains (ocsat for 0 and 1, ocseq multi for 2 and 3) after which a one-absorber (A=1) or free
completion exists.  With strictly positive values EFX0 and EFX coincide; for n = 3 an EFX allocation exists
(Chaudhury-Garg-Mehlhorn, arXiv 2002.05119, as recorded in proofs/citations.md item 5; not read here).

    python3 k4/ksens/general_rounds.py rand n mmin mmax T SEED        random profiles
    python3 k4/ksens/general_rounds.py climb n m STEPS ROUNDS SEED [pw5]    climb maximizing the rounds needed (values
    only); pw5: start every round from PW5 lifted to full valuations (n = 5, m = 9; k4/ksens.md §8)"""
import sys, random, json, collections, time
import _paths
import ocsat, ocseq


def full(n, m, rng):
    return [list(range(m)) for _ in range(n)], [rng.sample(range(1, 100), m) for _ in range(n)]


def need(O, Q, b, A, cmax=3):
    if O.holds(b, chain='none', A=A): return 0
    if O.holds(b, chain='any', A=A, multi=True): return 1
    for c in range(2, cmax + 1):
        if Q.holds(b, c, A, multi=True): return c
    return cmax + 1


def profile(sets, vals, A=1):
    m = len(sets[0]); n = len(sets); O = ocsat.OC(sets, vals, m); Q = ocseq.Seq(sets, vals, m); res = {}
    for Y in ocsat.starts(sets, vals, m):
        res[Y] = need(O, Q, ocsat.bases_of(Y, n), A)
    O.close(); Q.close(); return res


if __name__ == '__main__':
    mode = sys.argv[1]; t0 = time.time(); C = collections.Counter()
    print('$ python3 k4/ksens/general_rounds.py', *sys.argv[1:], flush=True)
    if mode == 'rand':
        n, mmin, mmax, T, seed = map(int, sys.argv[2:7]); rng = random.Random(seed)
        for t in range(T):
            m = rng.randint(mmin, mmax); sets, vals = full(n, m, rng)
            for A in (1, None):
                res = profile(sets, vals, A)
                for Y, c in res.items():
                    C['A=%s starts' % A] += 1; C['A=%s starts needing %d rounds' % (A, c)] += 1
                    if c >= 3: print('NEEDS %d ROUNDS (A=%s)' % (c, A), json.dumps(vals), 'picks', Y, flush=True)
        for k in sorted(C): print(k, C[k])
    else:
        n, m, steps, rounds, seed = map(int, sys.argv[2:7]); rng = random.Random(seed)
        def obj(vals):
            res = profile([list(range(m))] * n, vals, 1); mx = max(res.values())
            return (-mx, -sum(1 for c in res.values() if c == mx), -sum(1 for c in res.values() if c >= 1))
        def pw5_full():
            import fam_ladder
            sets0, vals0, m0 = fam_ladder.clean(3, 2, 4); rows = [[0] * m0 for _ in range(5)]
            for i, (s_, v_) in enumerate(zip(sets0, vals0)):
                for g, x in zip(s_, v_): rows[i][g] = 100 * x
            for i in range(5):
                t_ = 1
                for g in range(m0):
                    if rows[i][g] == 0: rows[i][g] = t_; t_ += 1
            return rows
        for r in range(rounds):
            vals = pw5_full() if 'pw5' in sys.argv[7:] else full(n, m, rng)[1]; c = obj(vals)
            for s in range(steps):
                v2 = [list(v) for v in vals]; i = rng.randrange(n); g = rng.randrange(m)
                if rng.random() < 0.7: v2[i][g] = max(1, v2[i][g] + rng.choice([-9, -5, -3, -1, 1, 3, 5, 9]))
                else:
                    h = rng.randrange(m); v2[i][g], v2[i][h] = v2[i][h], v2[i][g]
                if len(set(v2[i])) < m: continue
                c2 = obj(v2)
                if c2 <= c:
                    vals, c = v2, c2
                    if -c[0] >= 3: print('NEEDS 3+ ROUNDS', json.dumps(vals), flush=True); break
            print('round', r, 'final', c, json.dumps(vals), 'time %.0f' % (time.time() - t0), flush=True)
    print('time %.0f s' % (time.time() - t0))
