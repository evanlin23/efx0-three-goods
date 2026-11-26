"""Adversarial climb against Conjecture VM1 on general k-limited instances (no core requirement), for k = 5 tests
(k4/vm.md section 7.5).  Start: a random instance with N agents, each valuing 3..K goods (strict values 1..30).
Mutations: re-draw one agent's values, or swap one of its goods for another good (existing or new).
Objective: VM1's margin (vmx2_climb.vm1_score with unrestricted exchanges); (0, 0.0) would refute VM1.
EVIDENCE only.
    python3 k4/vm/vm1_climb_k.py N K STARTS STEPS SEED"""
import sys, os, json, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import vmx2_climb as C


def compact(sets):
    used = sorted(set(g for S in sets for g in S)); mp_ = {g: k for k, g in enumerate(used)}
    return [[mp_[g] for g in S] for S in sets]


def rand_inst(N, K, rng):
    m = rng.randint(N + 2, 2 * N + 3); sets = []; vals = []
    for i in range(N):
        k = rng.randint(3, K); S = rng.sample(range(m), min(k, m)); sets.append(S); vals.append(rng.sample(range(1, 31), len(S)))
    return compact(sets), vals


def climb(args):
    N, K, steps, seed = args
    V.FREE_Z[0] = True
    rng = random.Random(seed); sets, vals = rand_inst(N, K, rng); best = C.vm1_score(sets, vals)
    for t in range(steps):
        S2 = [list(x) for x in sets]; W2 = [list(x) for x in vals]; i = rng.randrange(N)
        if rng.random() < 0.6:
            W2[i] = rng.sample(range(1, 31), len(S2[i]))
        else:
            m = 1 + max(max(x) for x in S2); k = rng.randrange(len(S2[i])); new = rng.randrange(m + 1)
            if new in S2[i]: continue
            S2[i][k] = new; S2 = compact(S2)
        sc = C.vm1_score(S2, W2)
        if sc <= best:
            sets, vals, best = S2, W2, sc
    return seed, sets, vals, best


if __name__ == '__main__':
    N, K, starts, steps, seed = map(int, sys.argv[1:6])
    print('$ python3 k4/vm/vm1_climb_k.py', ' '.join(sys.argv[1:])); t0 = time.time(); res = []
    with mp.Pool(os.cpu_count()) as pool:
        for r in pool.imap_unordered(climb, [(N, K, steps, seed * 1000 + s) for s in range(starts)]):
            res.append(r)
    res.sort(key=lambda r: r[3])
    print('climbs', len(res), '; reached margin (0, 0.0):', sum(1 for r in res if r[3] == (0, 0.0)))
    for seed_, sets, vals, best in res[:6]:
        m = 1 + max(max(S) for S in sets)
        print('  margin %s %s' % (best, json.dumps({'sets': sets, 'vals': vals, 'm': m})))
    print('time %.0f s' % (time.time() - t0))
