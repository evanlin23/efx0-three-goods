"""Statistics of EP (ep.py, place='greedy') against K3S on a profile set, and a larger random run.

  python3 stats.py small N M        every ranking profile (test_k3s.gen_small)
  python3 stats.py core5            lbx.core_profiles(5, sample=200, minn=5)
  python3 stats.py rand K SEED MAXN random ranking profiles (3 goods each, n 2..MAXN, m n..2n+3), values (4, 3, 2)
Counts: profiles; EP failures; profiles where EP used swap (b) / swap (c) / a valuer move; where the placement of a
pool good needed a non-source; where pool goods went to two or more agents; where K3S rotated; where both EP's swap (c)
fired and K3S rotated.
"""
import sys, random, collections
from common import vals, gen_small, core_profiles, efx0
from ep import ep
from k3s import k3s

def run(src, label):
    c = collections.Counter(); first = None
    for n, m, rank in src:
        v = vals(rank); info = {}; X = ep(n, m, v, info, place='greedy')
        c['profiles'] += 1
        if not efx0(n, m, v, X):
            c['EP failures'] += 1
            if first is None: first = (n, m, rank)
        if info['b']: c['swap (b) used'] += 1
        if info['c']: c['swap (c) used'] += 1
        if info['nonsource']: c['step 3 needed a non-source'] += 1
        if info['up']: c['valuer moves used'] += 1
        if info['receivers'] >= 2: c['pool goods to >= 2 sources'] += 1
        ki = {}; k3s(n, m, v, ki)
        if ki.get('branch') == 'rot': c['K3S rotated'] += 1
        if info['c'] and ki.get('branch') == 'rot': c['both'] += 1
    print(f"{label}: {dict(c)}" + (f"; first EP failure {first}" if first else ""), flush=True)

def rand_profiles(K, seed, maxn):
    rng = random.Random(seed)
    for _ in range(K):
        n = rng.randint(2, maxn); m = rng.randint(max(3, n), 2 * n + 3)
        yield n, m, [tuple(rng.sample(range(m), 3)) for _ in range(n)]

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'small':
        n, m = int(sys.argv[2]), int(sys.argv[3]); run(gen_small(n, m), f"every profile n={n} m={m}")
    elif mode == 'core5':
        run(core_profiles(5, sample=200, minn=5), "core n=5 sample (200/core), values 4,3,2")
    elif mode == 'rand':
        K, seed, maxn = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        run(rand_profiles(K, seed, maxn), f"{K} random profiles n<={maxn} (seed {seed})")
