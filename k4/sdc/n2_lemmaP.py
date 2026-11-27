"""Lemma P for two agents (k4/sdc.md §20): for an additive valuation v with top a and second b1, and any third good
b2, is there a partition (P, Q) of M with a in P, b1 and b2 in Q, EFX0 for v in both directions?  If so, SD-C holds
for two agents sharing the top a (agent 1 cuts so, agent 2 chooses; either choice is SD-consistent).

    python3 k4/sdc/n2_lemmaP.py SEED T M"""
import itertools, random, sys, collections
def V(v, S): return sum(v[g] for g in S)
def theta(v, S): return V(v, S) - min(v[g] for g in S) if S else 0
print('$ python3 k4/sdc/n2_lemmaP.py', *sys.argv[1:])
rng = random.Random(int(sys.argv[1])); T = int(sys.argv[2]); M = int(sys.argv[3]); C = collections.Counter()
for t in range(T):
    m = rng.randint(3, M)
    v = [rng.choice([0, 0, 1, 2, 3, 5, 8, 13, rng.randint(1, 40)]) for g in range(m)]
    order = sorted(range(m), key=lambda g: (-v[g], g))
    a, b1 = order[0], order[1]
    for b2 in range(m):
        if b2 in (a, b1): continue
        rest = [g for g in range(m) if g not in (a, b1, b2)]
        ok = False
        for asg in itertools.product(range(2), repeat=len(rest)):
            P = [a] + [g for g, s in zip(rest, asg) if s == 0]; Q = [b1, b2] + [g for g, s in zip(rest, asg) if s == 1]
            if V(v, P) >= theta(v, Q) and V(v, Q) >= theta(v, P): ok = True; break
        C['cases'] += 1; C['Lemma P holds'] += ok
        if not ok and C['shown'] < 4: C['shown'] += 1; print('LEMMA P FAILS', v, 'a', a, 'b1', b1, 'b2', b2)
for k in sorted(C): print(k, C[k])
