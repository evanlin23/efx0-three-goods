"""Hard n = 3 starts at every k (kgen/rounds.md §6.2): a climb on instances with zeros (k valued goods per agent, or all
positive) minimising, over perfect starts, rnd.c's zero-aware one-round witness count (RND1Z) and its margin.  Every
start with RND1Z = 0 (one round fails, checked again by verify_k4zero's forward round) is written to OUT as JSONL.
    python3 kgen/rounds/n3_hunt.py OUT ROUNDS STEPS SEED MMIN MMAX KMIN KMAX"""
import sys, os, json, random, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ
out, rounds, steps, seed, mmin, mmax, kmin, kmax = sys.argv[1], *map(int, sys.argv[2:9])
rng = random.Random(seed); n = 3; VMAX = 3000; seen = set(); t0 = time.time()


def rand_inst():
    m = rng.randint(mmin, mmax); k = rng.randint(kmin, min(kmax, m))
    while True:
        V = []
        for i in range(n):
            S = rng.sample(range(m), k); V.append([rng.randint(1, VMAX) if g in S else 0 for g in range(m)])
        if all(any(V[i][g] for i in range(n)) for g in range(m)): return V


def obj(V):
    res, _ = rndlib.oc1z(V); per = [r for r in res if r['perfect'] and r['MD'] > 0]
    if not per: return (1, 0, 0), res
    h = min(per, key=lambda r: (r['RND1Z'], r['ms_RND1Z']))
    return (-sum(1 for r in per if r['RND1Z'] == 0), h['RND1Z'], round(h['ms_RND1Z'], 9)), res


def mutate(V):
    W = [list(r) for r in V]; i = rng.randrange(n); nz = [g for g in range(len(W[0])) if W[i][g] > 0]; u = rng.random()
    g = rng.choice(nz)
    if u < 0.6: W[i][g] = max(1, min(VMAX, W[i][g] + rng.choice([-100, -30, -10, -3, -1, 1, 3, 10, 30, 100])))
    elif u < 0.85: W[i][g] = rng.randint(1, VMAX)
    else:
        z = [h for h in range(len(W[0])) if W[i][h] == 0]
        if z and len(nz) > 1: h = rng.choice(z); W[i][h] = W[i][g]; W[i][g] = 0
    if not all(any(W[a][h] for a in range(n)) for h in range(len(W[0]))): return V
    return W


found = 0
with open(out, 'a') as fo:
    for r in range(rounds):
        V = rand_inst(); c, res = obj(V)
        for s in range(steps):
            W = mutate(V); c2, res2 = obj(W)
            if c2 <= c: V, c, res = W, c2, res2
            if c[0] < 0: break
        for x in res:
            if x['perfect'] and x['MD'] > 0 and x['RND1Z'] == 0:
                key = (json.dumps(V), tuple(x['picks']))
                if key in seen: continue
                seen.add(key)
                b0 = [frozenset([g]) for g in x['picks']]
                if any(VZ.completion(V, list(st), 1) is not None for st in VZ.one_round(V, b0, False)): continue
                k = max(sum(1 for v in row if v > 0) for row in V)
                fo.write(json.dumps({'name': 'hunt_k%d_m%d' % (k, len(V[0])), 'vals': V, 'picks': list(x['picks']), 'order': list(x['order'])}) + '\n'); fo.flush(); found += 1
        if r % 10 == 0: print('round', r, 'found', found, '%.0fs' % (time.time() - t0), flush=True)
print('found', found, 'time %.0f s' % (time.time() - t0))
