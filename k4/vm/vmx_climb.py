"""Adversarial search for a counterexample to Conjecture VMX (k4/vm.md section 7): hill-climb over strict profiles of
certified k = 4 cores, minimizing the fraction of VMx runs (vmlib.vm6x_run, mode choice) that end EFX0 (DFS up to
--limit runs; a profile whose runs are not all enumerated counts its sampled fraction).  A profile with fraction 0
(exhaustively) would refute VMX.  EVIDENCE only.
    python3 k4/vm/vmx_climb.py K STARTS STEPS SEED [--limit=N] [--phase3=0]   (--phase3=0: climb against VMX2)"""
import sys, os, json, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import data


KW = {}


def score(sets, vals, m, limit):
    I = V.Inst(sets, vals, m); ok = tot = 0
    for ch, r in V.all_runs(V.vm6x_run, I, limit=limit, mode='choice', **KW):
        tot += 1; ok += not isinstance(r, V.Stuck)
    return ok / tot, ok, tot, tot < limit


def mutate(sets, vals, rng):
    vals = [list(v) for v in vals]; i = rng.randrange(len(sets)); S = sets[i]
    T = rng.choice(data.TYPES[len(S)]); perm = list(S); rng.shuffle(perm); d = dict(zip(perm, T))
    vals[i] = [d[g] for g in S]
    return vals


def climb(args):
    K, steps, seed, limit = args
    rng = random.Random(seed); sets = rng.choice(data.cores(K)); m = 1 + max(max(x) for x in sets)
    vals = data.random_core_profile(sets, rng)
    best = score(sets, vals, m, limit)
    for t in range(steps):
        nv = mutate(sets, vals, rng); sc = score(sets, nv, m, limit)
        if sc[0] <= best[0]:
            vals, best = nv, sc
        if best[1] == 0 and best[3]:
            break
    return seed, sets, vals, m, best


if __name__ == '__main__':
    K, starts, steps, seed = map(int, sys.argv[1:5])
    opt = dict(a[2:].split('=') for a in sys.argv[5:] if a.startswith('--')); limit = int(opt.get('limit', 400))
    if opt.get('phase3') == '0': KW['phase3'] = False
    print('$ python3 k4/vm/vmx_climb.py', ' '.join(sys.argv[1:])); t0 = time.time(); res = []
    with mp.Pool(os.cpu_count()) as pool:
        for r in pool.imap_unordered(climb, [(K, steps, seed * 1000 + s, limit) for s in range(starts)]):
            res.append(r)
    res.sort(key=lambda r: r[4][0])
    zero = [r for r in res if r[4][1] == 0]
    print('climbs', len(res), 'reached fraction 0:', len(zero), '(exhaustive: %d)' % sum(r[4][3] for r in zero))
    for seed_, sets, vals, m, (fr, ok, tot, exh) in res[:8]:
        print('  fraction %.3f (%d/%d%s) %s' % (fr, ok, tot, '' if exh else ', capped', json.dumps({'sets': sets, 'vals': vals, 'm': m})))
    print('time %.0f s' % (time.time() - t0))
