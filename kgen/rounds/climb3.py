"""Climb toward a start that needs THREE rounds (RD2+ test, kgen/rounds.md §4.1), with rnd.c's exact two-round count.

Objective (minimized): (min over the K hardest starts of the number of complete EFX allocations reachable by <= 2
rounds (free completion), min over all starts of the one-round witness count (RND1), its margin sum).  The K hardest
starts are those with the smallest (RND1, margin).  A start with two-round count 0 is printed as CAND3 and appended to
$FAILS3; it must be confirmed by ocseq (verify_fail.py) and bruter.py's forward two-round simulation.

    python3 kgen/rounds/climb3.py n m STEPS ROUNDS SEED (KIND | seeds=FILE.jsonl) [K]
"""
import sys, os, json, random, time, zlib
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, families
VMAX = int(os.environ.get('VMAX', '6000')); CAP = int(os.environ.get('CAP2', '200'))


def evaluate(V, K):
    res, _ = rndlib.analyze(V)
    order = sorted(res, key=lambda r: (r['counts']['RND1'], r['msum']))
    c2 = []
    for r in order[:K]:
        c, md = rndlib.two_rounds(V, list(r['picks']), CAP); c2.append((c, r))
    best = min(c2, key=lambda x: x[0])
    h = order[0]
    return (best[0], h['counts']['RND1'], round(h['msum'], 9)), best[1], c2


def main():
    n, m, steps, rounds = map(int, sys.argv[1:5])
    seed = int(sys.argv[5]) if sys.argv[5].isdigit() else zlib.crc32(sys.argv[5].encode())
    init = sys.argv[6]; K = int(sys.argv[7]) if len(sys.argv) > 7 else 3
    rng = random.Random(seed); t0 = time.time()
    seeds = [json.loads(l)['vals'] for l in open(init[6:])] if init.startswith('seeds=') else None
    print('$ python3 kgen/rounds/climb3.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        V = [list(x) for x in rng.choice(seeds)] if seeds else families.gen(init, n, m, rng)
        n_, m_ = len(V), len(V[0])
        c, hr, _ = evaluate(V, K)
        for s in range(steps):
            V2 = [list(x) for x in V]; i = rng.randrange(n_); g = rng.randrange(m_); u = rng.random()
            if u < 0.6: V2[i][g] = max(1, min(VMAX, V2[i][g] + rng.choice([-100, -30, -10, -3, -1, 1, 3, 10, 30, 100])))
            elif u < 0.85:
                h = rng.randrange(m_); V2[i][g], V2[i][h] = V2[i][h], V2[i][g]
            elif u < 0.95: V2[i][g] = rng.randint(1, VMAX)
            else:
                j = rng.randrange(n_); V2[i] = [max(1, x + rng.randint(-2, 2)) for x in V2[j]]
            c2, hr2, _ = evaluate(V2, K)
            if c2 <= c:
                V, c, hr = V2, c2, hr2
                if c[0] == 0:
                    print('CAND3 vals', json.dumps(V), 'picks', list(hr['picks']), 'order', list(hr['order']), flush=True)
                    fp = os.environ.get('FAILS3')
                    if fp:
                        with open(fp, 'a') as f: f.write(json.dumps({'vals': V, 'picks': list(hr['picks']), 'order': list(hr['order'])}) + '\n')
                    break
        print('round', r, 'final', c, 'hardest', list(hr['picks']), 'order', list(hr['order']), 'vals', json.dumps(V),
              'time %.0f' % (time.time() - t0), flush=True)
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
