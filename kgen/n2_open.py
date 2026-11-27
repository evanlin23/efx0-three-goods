"""The open case of Lemma 2 (kgen/n3.md §8): two agents, positive generic values, neither LPT_a nor LPT_b separates the
picks.  Coverage of the ratio knives (b takes by v_b/v_a; a takes by v_a/v_b) and of the LPTs with both picks placed
first (F5: b cuts, a chooses; F6: a cuts, b chooses), alone and together; and whether an A1/B allocation exists
when none of them works (brute force over all 2^m allocations).

    python3 kgen/n2_open.py SEED N MMIN MMAX"""
import sys, random, collections, json, itertools
from oc2 import efx0, sd
from n2_lpt import lpt
from n2_knife import knife
from n2_rules import shape
from n2_fallback import lpt_pre, choose

if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = []
    print('$ python3 kgen/n2_open.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]; J = [g for g in range(m) if g not in (ya, yb)]
            if v[b][ya] > v[b][yb]: continue
            Pb, Pa = lpt(v[b], range(m)), lpt(v[a], range(m))
            if (ya in Pb[0]) != (yb in Pb[0]) or (ya in Pa[0]) != (yb in Pa[0]): continue
            C['open-case starts'] += 1
            ok = {}
            ok['knife b'] = shape(v, knife(v, b, a, yb, ya, J), ya, yb, a, b) in ('A1', 'B')
            ok['knife a'] = shape(v, knife(v, a, b, ya, yb, J), ya, yb, a, b) in ('A1', 'B')
            P, Q = lpt_pre(v[b], range(m), {yb: 0, ya: 1}); ok['F5'] = shape(v, choose(v, P, Q, b, a), ya, yb, a, b) in ('A1', 'B')
            P, Q = lpt_pre(v[a], range(m), {ya: 0, yb: 1}); ok['F6'] = shape(v, choose(v, P, Q, a, b), ya, yb, a, b) in ('A1', 'B')
            for k, x in ok.items(): C[k] += x
            C['knife b or F5 or F6'] += ok['knife b'] or ok['F5'] or ok['F6']
            C['any of the four'] += any(ok.values())
            if not any(ok.values()):
                Xs = [[{g for g in range(m) if q[g] == i} for i in range(2)] for q in itertools.product(range(2), repeat=m)]
                C['none: an A1/B allocation exists'] += any(shape(v, X, ya, yb, a, b) in ('A1', 'B') for X in Xs)
                if len(ex) < 3: ex.append((v, (a, b)))
    for k in sorted(C): print(C[k], k)
    for e in ex: print('none works', json.dumps(e))
