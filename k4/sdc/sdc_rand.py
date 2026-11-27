import sys, os, json, random, time, multiprocessing as mp
import _paths
os.chdir(_paths.DE4)
from sdsat import solve
def gen(src, rng):
    if src == 'rand':
        from dead import random_r1
        I = random_r1(rng); return I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)]
    if src == 'hyper':
        from de4lib import random_profile
        cores = json.load(open(_paths.ROOT + '/results/k4_de4/stuck_hypergraphs.json'))['hypergraphs']
        s = rng.choice(cores); return s, random_profile(s, rng)
    if src.startswith('advt'):
        import adv_t, adv_t3, adv_t4
        I = None
        while I is None:
            I = adv_t3.make(rng) if src == 'advt3x' else adv_t4.make(rng) if src == 'advt4x' else adv_t.make(rng, int(src[4:]))
        return I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)]
    if src.startswith('big'):       # random k=4 core-like hypergraph, n agents, m goods, degrees 3/4, balanced values
        n = int(src[3:]); m = rng.randint(n + 4, 2 * n + n // 2)
        from de4lib import random_profile
        while True:
            sets = [sorted(rng.sample(range(m), rng.choice([3, 4, 4]))) for _ in range(n)]
            if len(set().union(*map(set, sets))) == m: break
        return sets, random_profile(sets, rng)
    if src.startswith('k3_'):
        n = int(src[3:]); m = rng.randint(n + 2, 2 * n)
        while True:
            sets = [sorted(rng.sample(range(m), 3)) for _ in range(n)]
            if len(set().union(*map(set, sets))) == m: break
        vals = []
        for s in sets:
            while True:
                V = rng.sample(range(1, 20), 3)
                if max(V) < sum(V) - max(V): break
            vals.append(V)
        return sets, vals
def job(args):
    src, per, seed = args
    rng = random.Random(seed); bad = []; c = 0
    for _ in range(per):
        sets, vals = gen(src, rng)
        m = 1 + max(max(s) for s in sets)
        ok, w = solve(sets, vals, m); c += 1
        if not ok: bad.append((sets, vals))
    return c, bad
if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    t0 = time.time(); tot = 0; B = []
    with mp.Pool(min(jobs, 3)) as p:
        for c, bad in p.imap_unordered(job, [(src, per, seed + k) for k in range(jobs)]):
            tot += c; B += bad
            for b in bad: print('FAIL', json.dumps(b), flush=True)
    print(src, 'instances', tot, 'SD-C failures', len(B), 'time %.0f' % (time.time() - t0), flush=True)
