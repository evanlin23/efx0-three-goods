"""Conjectures K' and K'' (kgen/n3.md §8): two agents, positive generic values.  K': if LPT_b puts y_a and y_b in the
same bundle, the ratio knife (refuted: m = 6 generic; LPT_a separates there).  K'': if NEITHER LPT_a nor LPT_b
separates the picks, the ratio knife (kgen/n2_knife.py: b keeps y_b and takes junk by v_b/v_a decreasing until it does not strongly envy a)
gives an EFX0 allocation, which then has shape A1.  With Lemma 2 (i)-(ii), this would settle the positive generic
two-agent case.  Random test; also with small integer values (ties possible, reported separately).

    python3 kgen/n2_kprime.py SEED N MMIN MMAX"""
import sys, random, collections, json
from oc2 import efx0, sd
from n2_lpt import lpt
from n2_knife import knife
from n2_rules import shape

if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/n2_kprime.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi)
        gen = 'generic' if t % 2 == 0 else 'small'
        v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)] if gen == 'generic' else [[rng.randint(1, 12) for _ in range(m)] for _ in range(2)]
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]; J = [g for g in range(m) if g not in (ya, yb)]
            P, Q = lpt(v[b], range(m))
            if (ya in P) != (yb in P): continue
            C[gen + ": K' hypothesis (LPT_b does not separate)"] += 1
            X = knife(v, b, a, yb, ya, J)
            ok = X is not None and efx0(v, X) and shape(v, X, ya, yb, a, b) == 'A1'
            C[gen + ": K' knife gives A1"] += ok
            P2, Q2 = lpt(v[a], range(m)); open_case = (ya in P2) == (yb in P2)
            if open_case:
                C[gen + ": K'' hypothesis (neither LPT separates)"] += 1; C[gen + ": K'' knife gives A1"] += ok
            if not ok and C[gen + ' shown'] < 3:
                C[gen + ' shown'] += 1
                print("K' FAILS" + (" (and K'')" if open_case else " (not K'': LPT_a separates)"), gen, json.dumps(v), 'order', (a, b), 'picks', ya, yb, flush=True)
    for k in sorted(C):
        if 'shown' not in k: print(k, C[k])
