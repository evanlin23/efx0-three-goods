"""Hill-climb on values toward a counterexample to W(k) with f = p - 1 (kgen/charity.md §6): maximise
score = (largest welfare over partial EFX0 allocations leaving >= p goods out) - (largest welfare leaving < p out).
score > 0 means every welfare maximum leaves >= p goods out.  The hypergraph is fixed (S'(sigma, k) or random);
moves change one value by a small amount; equal scores are accepted (plateau moves).

    python3 kgen/charity/w_climb.py SEED STEPS P START [K SIGMA RESTARTS]
START: 'family' (S'(SIGMA, K) with its own values), 'familyrand' (its hypergraph, random values 1..12),
       'rand<n>' (random hypergraph with n agents valuing 3..K goods)."""
import sys, random, json, time
from chlib import Inst, welfare_max, rand_inst, pool_of, efx0


def score(I, p):
    a = welfare_max(I, minpool=p)[0]
    b = welfare_max(I, maxpool=p - 1)[0]
    if a is None:
        return -10 ** 6, a, b
    return a - (b if b is not None else 0), a, b


if __name__ == '__main__':
    seed, STEPS, P = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); start = sys.argv[4]
    RESTARTS = int(sys.argv[7]) if len(sys.argv) > 7 else 1
    K = int(sys.argv[5]) if len(sys.argv) > 5 else 4; SIG = int(sys.argv[6]) if len(sys.argv) > 6 else 3
    rng = random.Random(seed)
    print('$ python3 kgen/charity/w_climb.py', *sys.argv[1:], flush=True)
  best_overall = None
  for rs in range(RESTARTS):
    if start.startswith('family'):
        from stuck_family import build
        I = build(SIG, K, own=True)[0]
        if start == 'familyrand':
            I = Inst(I.n, I.m, [{g: rng.randint(1, 12) for g in vi} for vi in I.v])
    else:
        n = int(start[4:]); I = rand_inst(rng, n, rng.randint(n + 2, 2 * n + 2), 3, K, vmax=12)
    sc, a, b = score(I, P); t0 = time.time()
    print('restart %d: start score %d (>= %d out: %s, < %d out: %s)' % (rs, sc, P, a, P, b), flush=True)
    for step in range(STEPS):
        v = [dict(vi) for vi in I.v]
        i = rng.randrange(I.n); g = rng.choice(sorted(v[i]))
        v[i][g] = max(1, v[i][g] + rng.choice([-3, -2, -1, 1, 2, 3]))
        J = Inst(I.n, I.m, v)
        s2, a2, b2 = score(J, P)
        if s2 >= sc:
            if s2 > sc:
                print('  step %d score %d (>= %d out: %s, < %d out: %s) %.0f s' % (step, s2, P, a2, P, b2,
                                                                                  time.time() - t0), flush=True)
            I, sc = J, s2
        if sc > 0:
            W, p, X = welfare_max(I)
            assert p >= P and efx0(I, X)
            print('FOUND welfare maximum leaving %d out' % p, json.dumps({'inst': I.to_json(),
                  'X': [sorted(B) for B in X], 'pool': sorted(pool_of(I, X)), 'welfare': W}), flush=True)
            break
    best_overall = sc if best_overall is None else max(best_overall, sc)
    print('restart %d final score %d, %.0f s' % (rs, sc, time.time() - t0), flush=True)
    if sc > 0:
        break
  print('best score over restarts', best_overall)
