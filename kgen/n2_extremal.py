"""Two agents: does an extremal EFX0 allocation always have shape A1 or B (kgen/n3.md §4)?  Rules tested, each over all
EFX0 allocations, ties broken by the listed secondary keys and then by the allocation's index:
  maxA:  maximize v_a(X_a), then v_b(X_b)          maxB:  maximize v_b(X_b), then v_a(X_a)
  maxmin: maximize min(v_a(X_a)/v_a(M), v_b(X_b)/v_b(M)) (normalized), then the sum
  maxA_norm: maxA among allocations after moving a-worthless goods of X_a to b when that keeps EFX0 (Lemma M)
A rule passes a start if SOME allocation in its argmax set has shape A1 or B ('any') and if its first one does ('first').

    python3 kgen/n2_extremal.py SEED N MMIN MMAX"""
import sys, random, itertools, collections, json
from oc2 import efx0, sd, gen
from n2_rules import shape

if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = {}
    print('$ python3 kgen/n2_extremal.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); v = gen(rng, m)
        allX = []
        for asg in itertools.product(range(2), repeat=m):
            X = [{g for g in range(m) if asg[g] == i} for i in range(2)]
            if efx0(v, X): allX.append(X)
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]; C['starts'] += 1
            va = lambda X: sum(v[a][g] for g in X[a]); vb = lambda X: sum(v[b][g] for g in X[b])
            Ma, Mb = sum(v[a]), sum(v[b])
            keys = {
                'maxA': lambda X: (va(X), vb(X)),
                'maxB': lambda X: (vb(X), va(X)),
                'maxmin': lambda X: (min(va(X) / Ma, vb(X) / Mb), va(X) / Ma + vb(X) / Mb),
                'maxA_then_fewest_a_goods': lambda X: (va(X), -len(X[a]), vb(X)),
                'maxB_then_fewest_b_goods': lambda X: (vb(X), -len(X[b]), va(X)),
            }
            for name, key in keys.items():
                best = max(key(X) for X in allX); arg = [X for X in allX if key(X) == best]
                sh = [shape(v, X, ya, yb, a, b) for X in arg]
                anyok = any(s in ('A1', 'B') for s in sh); firstok = sh[0] in ('A1', 'B')
                C[name + ' any'] += anyok; C[name + ' first'] += firstok
                if not anyok and name not in ex: ex[name] = (v, (a, b), [sorted(s) for s in arg[0]], sh[0])
    for k in sorted(C): print('%-32s %d' % (k, C[k]))
    for k, e in ex.items(): print('fails', k, json.dumps(e))
