"""Adversarial climbs against Conjecture VMX2 (k4/vm.md section 7.2) on strict connected k = 4 cores, n = 5 or 6.
Start: a certified core with a random strict profile.  Mutations: (a) one agent's order type and ranking (a strict
balanced type), (b) one agent swaps one of its goods for another good (an existing one or a new one).  A mutation is
kept only if is_core4 (k4/c4_verify_H/hcore.py: IsCore4 of K4Reduction.lean, strictness, connectivity) passes.
Objective (minimized): the fraction of R random VMX2 runs that end EFX0, with the first DFS run as a tie-break.
At the end, every instance whose sampled fraction is 0 gets a DFS over VMX2's choices (cap --cap) looking for a
success.  EVIDENCE only.
    python3 k4/vm/vmx2_climb.py N STARTS STEPS SEED [--R=60] [--cap=20000] [--obj=vmx2|vm1]
--obj=vm1 minimizes Conjecture VM1's margin instead: (some V-M matching completes by placement alone, fraction of
the states within one move from which some placement order completes); (0, 0.0) would refute VM1."""
import sys, os, json, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import data
sys.path.insert(0, os.path.join(data.ROOT, 'k4', 'c4_verify_H'))
from hcore import is_core4

CORE_KEY = {3: 3, 4: 4, 5: 5, 6: 6}


def dense(sets, vals, m):
    v = [[0] * m for _ in sets]
    for i, (S, W) in enumerate(zip(sets, vals)):
        for g, x in zip(S, W):
            v[i][g] = x
    return v


def ok_core(sets, vals):
    used = sorted(set(g for S in sets for g in S))
    if used != list(range(len(used))):
        return False
    return not is_core4(dense(sets, vals, len(used)))


def compact(sets):
    used = sorted(set(g for S in sets for g in S)); mp_ = {g: k for k, g in enumerate(used)}
    return [[mp_[g] for g in S] for S in sets]


OBJ = ['vmx2']


def vm1_score(sets, vals):
    """Conjecture VM1's margin: (does some V-M matching complete by placement alone, fraction of successful
    Phase-B leaves over every state within one move of a V-M matching).  (0, 0.0) refutes VM1 (within the caps)."""
    import vmx2_phases as P
    m = 1 + max(max(S) for S in sets); I = V.Inst(sets, vals, m)
    ok = tot = 0; zero = 0; seen = set()
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if isinstance(r, V.Stuck): continue
        X = [list(b) for b in r[0]]; pool = set(range(m)) - set(g for b in X for g in b)
        Y = [list(b) for b in X]; V.l3_source(I, Y)
        cand = [(Y, pool, 0)] + [P.apply_move(Y, pool, mv) + (1,) for mv in V.exchanges(I, Y, pool)]
        for Z, Pz, d in cand:
            k = P.key(Z)
            if k in seen: continue
            seen.add(k)
            W = [list(b) for b in Z]; V.l3_source(I, W)
            s_, e_, runs = P.phase_b(I, W, Pz, 400)
            if s_ and d == 0: zero = 1
            ok += s_; tot += 1
    return zero, ok / max(tot, 1)


def frac(sets, vals, R, seed):
    if OBJ[0] == 'vm1':
        return vm1_score(sets, vals)
    m = 1 + max(max(S) for S in sets); I = V.Inst(sets, vals, m); rng = random.Random(seed); ok = 0
    for t in range(R):
        try:
            V.vm6x_run(I, V.Chooser((), rng=rng), mode='choice', phase3=False); ok += 1
        except V.Stuck:
            pass
    try:
        V.vm6x_run(I, V.Chooser(()), mode='choice', phase3=False); first = 1
    except V.Stuck:
        first = 0
    return ok / R, first


def mutate(sets, vals, rng):
    sets = [list(S) for S in sets]; vals = [list(W) for W in vals]; n = len(sets)
    i = rng.randrange(n)
    if rng.random() < 0.7:
        S = sets[i]; T = rng.choice(data.TYPES[len(S)]); perm = list(S); rng.shuffle(perm); d = dict(zip(perm, T))
        vals[i] = [d[g] for g in S]
    else:
        m = 1 + max(max(S) for S in sets)
        k = rng.randrange(len(sets[i])); new = rng.randrange(m + 1)
        if new in sets[i]:
            return None
        sets[i][k] = new
        sets = compact(sets)
    return sets, vals


def climb(args):
    N, steps, seed, R, cap = args
    rng = random.Random(seed)
    while True:
        sets = rng.choice(data.cores(CORE_KEY[N])); vals = data.random_core_profile(sets, rng)
        if ok_core(sets, vals): break
    best = frac(sets, vals, R, seed); tried = kept = 0
    for t in range(steps):
        mu = mutate(sets, vals, rng)
        if mu is None or not ok_core(*mu):
            continue
        tried += 1
        sc = frac(mu[0], mu[1], R, seed + t + 1)
        if sc <= best:
            sets, vals = mu; best = sc; kept += 1
    m = 1 + max(max(S) for S in sets)
    found = None
    if OBJ[0] == 'vm1':
        found = 'VM1 margin %s' % (best,)
    elif best[0] == 0:
        I = V.Inst(sets, vals, m); k = 0; found = False
        for ch, r in V.all_runs(V.vm6x_run, I, limit=cap, mode='choice', phase3=False):
            k += 1
            if not isinstance(r, V.Stuck):
                found = k; break
        if found is False:
            found = 'none in %d runs%s' % (k, ' (exhaustive)' if k < cap else '')
    return seed, sets, vals, m, best, tried, kept, found


if __name__ == '__main__':
    N, starts, steps, seed = map(int, sys.argv[1:5])
    opt = dict(a[2:].split('=') for a in sys.argv[5:] if a.startswith('--'))
    R = int(opt.get('R', 60)); cap = int(opt.get('cap', 20000)); OBJ[0] = opt.get('obj', 'vmx2')
    print('$ python3 k4/vm/vmx2_climb.py', ' '.join(sys.argv[1:])); t0 = time.time(); res = []
    with mp.Pool(os.cpu_count()) as pool:
        for r in pool.imap_unordered(climb, [(N, steps, seed * 1000 + s, R, cap) for s in range(starts)]):
            res.append(r)
    res.sort(key=lambda r: r[4])
    print('climbs', len(res), '; mutations tried (core-checked)', sum(r[5] for r in res), '; kept', sum(r[6] for r in res))
    print('climbs ending at sampled fraction 0:', sum(1 for r in res if r[4][0] == 0))
    for seed_, sets, vals, m, best, tried, kept, found in res[:10]:
        print('  fraction %.3f first-run %d  DFS: %s  %s' % (best[0], best[1], found, json.dumps({'sets': sets, 'vals': vals, 'm': m})))
    print('time %.0f s' % (time.time() - t0))
