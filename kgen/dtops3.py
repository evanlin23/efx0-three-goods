"""Three agents with distinct tops (kgen/n3.md §10): which OC1 shapes are needed, and how far a pivot construction gets.

Instances: kgen/gen3.py kinds, then good i becomes agent i's unique top (v_i(i) = max_i + 1..10). Every order then
has picks (0, 1, 2), so order (0, 1, 2) is enough. Shapes come from kgen/oc3.c's shapes().
  keep  : the picks, or a t = 0 move, with one absorber (every agent keeps its top)
  t1/z  : a chain x0 -> x1 with the third agent z as the absorber (or no absorber)
  t1/x  : a chain x0 -> x1 with x0 or x1 as the absorber
  t2    : a chain through all three agents
Pivot construction P1: some agent z gets its top plus at most one good g. The other two split the rest by Theorem 2's
case 2 (b = cutter, a = chooser, Lemma M, tops added back). Checked for EFX0 (it is then of shape "keep").

    python3 kgen/dtops3.py SEED N MMIN MMAX [kinds]"""
import sys, random, collections, json
from oc3lib import shapes
from gen3 import gen
from theorem2 import lpt


def efx0(v, X):
    for i in range(3):
        own = sum(v[i][g] for g in X[i])
        for j in range(3):
            if j != i and len(X[j]) >= 2 and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > own: return False
    return True


def split2(v, goods, a, b):
    N = [g for g in goods if g not in (a, b)]
    P, Q = lpt(v[b], N)
    Sa, Sb = (P, Q) if sum(v[a][g] for g in P) >= sum(v[a][g] for g in Q) else (Q, P)
    W = {g for g in Sa if v[a][g] == 0}
    return (Sa - W) | {a}, Sb | W | {b}


def pivot(v):
    m = len(v[0])
    for z in range(3):
        for a in range(3):
            if a == z: continue
            b = 3 - a - z
            for g in [None] + list(range(3, m)):
                Z = {z} | ({g} if g is not None else set())
                Xa, Xb = split2(v, [h for h in range(m) if h not in Z], a, b)
                X = [None] * 3; X[z], X[a], X[b] = Z, Xa, Xb
                if efx0(v, X): return z, a, b, g
    return None


def families(S):
    fam = set()
    for s, ab in S:
        if s[0] in ('none', 't0'): fam.add('keep')
        elif s[0] == 't1': fam.add('t1/z' if ab in (3 - s[1] - s[2], None) else 't1/x')
        else: fam.add('t2')
    return fam


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); shown = 0
    kinds = sys.argv[5].split(',') if len(sys.argv) > 5 else ['general', 'zeros', 'ident', 'junk', 'klim:4', 'ties']
    print('$ python3 kgen/dtops3.py', *sys.argv[1:], flush=True)
    for t in range(N):
        kind = kinds[t % len(kinds)]; m = rng.randint(lo, hi)
        if kind.startswith('klim'): m = min(m, 3 * int(kind[5:]))
        v = gen(kind, m, rng)
        for i in range(3): v[i][i] = max(v[i]) + rng.randint(1, 10)
        fam = families(shapes(v)[0]); p = pivot(v)
        C[kind + ': instances'] += 1
        C[kind + ': some OC1 shape'] += bool(fam)
        C[kind + ': keep'] += 'keep' in fam
        C[kind + ': keep or t1/z'] += bool(fam & {'keep', 't1/z'})
        C[kind + ': pivot P1 works'] += p is not None
        C[kind + ': keep fails, needs a chain'] += 'keep' not in fam
        if not fam & {'keep', 't1/z'} and shown < 5:
            shown += 1; print('NEITHER keep NOR t1/z', json.dumps(v), sorted(fam), flush=True)
    for k in sorted(C): print(C[k], k)
