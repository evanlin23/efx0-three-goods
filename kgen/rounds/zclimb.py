"""Direct climb on k = 4 CORES with zero values toward OC1^max failures (kgen/rounds.md §4.5), with rnd.c's zero-aware
OC1 (rnd_oc1z, cross-checked against k4/sdc's pipeline by xcheck_z.py).  Instances stay k = 4 cores (K4.CORE of
k4/SCOUT.md, as in stress.is_core, plus connectivity).  Objective (minimized): (-#perfect starts failing ZCLASS, min over
perfect starts of (ZCLASS witness count, ZCLASS margin sum, ...)).  ZSTRICT=1 (default): strict cores (distinct subset
sums per agent).  Every failure is printed (ZFAIL) and appended to $FAILS.
    python3 kgen/rounds/zclimb.py n m STEPS ROUNDS SEED [seeds=FILE.jsonl]"""
import sys, os, json, random, time, zlib
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib
from stress import is_core
VMAX = 3000
ZCLASS = os.environ.get('ZCLASS', 'OC1')   # OC1 (k4/sdc's official move), OC1P (OC1', kgen/rounds.md §4.6),
                                           # RND1Z (one plain round) or RNDPZ (ROUND-P), §4.9


def connected(Z):
    n = len(Z); R = [set(g for g, x in enumerate(r) if x > 0) for r in Z]
    seen, todo = {0}, [0]
    while todo:
        a = todo.pop()
        for b in range(n):
            if b not in seen and R[a] & R[b]: seen.add(b); todo.append(b)
    return len(seen) == n


ZFREE = os.environ.get('ZFREE', '0') == '1'   # no core constraint; random instances all-positive (every start perfect)


ZSTRICT = os.environ.get('ZSTRICT', '1') == '1'   # strict cores: every agent's subset sums of relevant goods distinct


def strict(Z):
    for row in Z:
        r = [x for x in row if x > 0]; sums = set()
        for mask in range(1 << len(r)):
            t = sum(r[k] for k in range(len(r)) if mask >> k & 1)
            if t in sums: return False
            sums.add(t)
    return True


def ok(Z): return True if ZFREE else (is_core(Z) and connected(Z) and (not ZSTRICT or strict(Z)))


def rand_core(n, m, rng):
    if ZFREE: return [rng.sample(range(1, VMAX), m) for _ in range(n)]
    while True:
        Z = []
        for i in range(n):
            k = 4 if rng.random() < 0.8 else 3; S = rng.sample(range(m), k)
            Z.append([rng.randint(1, VMAX) if g in S else 0 for g in range(m)])
        if ok(Z): return Z


def objective(Z):
    res, _ = rndlib.oc1z(Z)
    per = [r for r in res if r['perfect']]
    if not per: return (1, 0, 0.0), res
    fails = sum(1 for r in per if r[ZCLASS] == 0)
    key = lambda r: (r[ZCLASS], round(r['ms_' + ZCLASS], 9), r['RND1Z'], r['OC1P'], r['OC1'])
    return (-fails,) + key(min(per, key=key)), res


def mutate(Z, rng):
    W = [list(r) for r in Z]; n, m = len(W), len(W[0]); i = rng.randrange(n)
    nz = [g for g in range(m) if W[i][g] > 0]; u = rng.random()
    if u < 0.6:
        g = rng.choice(nz); W[i][g] = max(1, min(VMAX, W[i][g] + rng.choice([-100, -30, -10, -3, -1, 1, 3, 10, 30, 100])))
    elif u < 0.8:
        g, h = rng.sample(nz, 2) if len(nz) >= 2 else (nz[0], nz[0]); W[i][g], W[i][h] = W[i][h], W[i][g]
    elif u < 0.92:
        g = rng.choice(nz); W[i][g] = rng.randint(1, VMAX)
    elif not ZFREE:   # move one relevance of agent i to another good
        g = rng.choice(nz); z = [h for h in range(m) if W[i][h] == 0]
        if z: h = rng.choice(z); W[i][h] = W[i][g]; W[i][g] = 0
    else:
        j = rng.randrange(n); W[i] = [max(1, x + rng.randint(-2, 2)) for x in W[j]]
    return W


def main():
    n, m, steps, rounds = map(int, sys.argv[1:5])
    seed = int(sys.argv[5]) if sys.argv[5].isdigit() else zlib.crc32(sys.argv[5].encode())
    seeds = None
    for a in sys.argv[6:]:
        if a.startswith('seeds='): seeds = [json.loads(l)['vals'] for l in open(a[6:])]
    rng = random.Random(seed); t0 = time.time()
    print('$ python3 kgen/rounds/zclimb.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        Z = [list(x) for x in rng.choice(seeds)] if seeds else rand_core(n, m, rng)
        if seeds and not ZFREE: Z = [[x if x > 5 else 0 for x in row] for row in Z]
        if not ok(Z): continue
        c, res = objective(Z)
        for s in range(steps):
            W = mutate(Z, rng)
            if not ok(W): continue
            c2, res2 = objective(W)
            if c2 <= c:
                Z, c, res = W, c2, res2
                if c[0] < 0:
                    for x in res:
                        if x['perfect'] and x[ZCLASS] == 0:
                            print('ZFAIL', ZCLASS, 'vals', json.dumps(Z), 'picks', list(x['picks']), 'order', list(x['order']), flush=True)
                            fp = os.environ.get('FAILS')
                            if fp:
                                with open(fp, 'a') as f: f.write(json.dumps({'class': ZCLASS, 'vals': Z, 'picks': list(x['picks']), 'order': list(x['order'])}) + '\n')
                    break
        print('round', r, 'final', c, 'vals', json.dumps(Z), 'time %.0f' % (time.time() - t0), flush=True)
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
