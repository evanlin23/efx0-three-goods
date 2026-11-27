"""Two agents: does one of them always have a separating feasible cut, i.e. a partition (P, Q) with y_a in P and y_b in
Q that is EFX0-feasible for that agent in both directions?  If agent b has one: b cuts, a chooses, shape A1 or B
(kgen/n3.md §9, Lemma 2*).  If agent a has one: a cuts, b chooses, shape A1/A2 or B.  Brute force over all
partitions; reports starts where neither agent has one.  Values: generic positive, generic with zeros, or small ints.

    python3 kgen/n2_sepcut.py SEED N MMIN MMAX [zeros|small]"""
import sys, random, itertools, collections, json
from oc2 import sd
from n2_zeros import gen0


def feasible(vc, P, Q):
    def ok(A, B):
        return len(B) < 2 or sum(vc[g] for g in A) >= sum(vc[g] for g in B) - min(vc[g] for g in B)
    return ok(P, Q) and ok(Q, P)


def has_sep_cut(vc, m, ya, yb):
    rest = [g for g in range(m) if g not in (ya, yb)]
    for bits in itertools.product((0, 1), repeat=len(rest)):
        P = {ya} | {g for g, x in zip(rest, bits) if x == 0}; Q = {yb} | {g for g, x in zip(rest, bits) if x == 1}
        if feasible(vc, P, Q): return True
    return False


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); mode = sys.argv[5] if len(sys.argv) > 5 else 'generic'
    rng = random.Random(seed); C = collections.Counter(); ex = []
    print('$ python3 kgen/n2_sepcut.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi)
        if mode == 'zeros': v = gen0(rng, m)
        elif mode == 'small': v = [[rng.randint(1, 9) for _ in range(m)] for _ in range(2)]
        else: v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]
            if yb is None: continue
            C['starts'] += 1
            hb = has_sep_cut(v[b], m, ya, yb); ha = has_sep_cut(v[a], m, ya, yb)
            C['b has a separating feasible cut'] += hb; C['a has one'] += ha; C['a or b has one'] += ha or hb
            if not (ha or hb) and len(ex) < 4: ex.append((v, (a, b), ya, yb))
    for k in sorted(C): print(C[k], k)
    for e in ex: print('neither', json.dumps(e))
