"""PS (prescribed source) tests for k4/induct.md, with k4/induct.c's early-exit search (task Q).

PS(I, w): some EFX0 allocation of I leaves w unenvied (no agent j has v_j(X_w) > v_j(X_j)).
For every profile of every core in the given certificate files it tests
  - PS(I, w) for every agent w (all allocations, and D2 allocations), and
  - PS(I - p, w) for every 4-good agent w with a private good p (the private-insertion step, k4/induct.md Lemma 2).
Profiles: every strict profile (--all, or when the product of the domains is at most --max-all), else --samples random
ones per core. Cores: k = 4 certificates ({'cores': [...]}) or k = 3 certificates (list of records with 'sets').

Usage: python3 k4/induct_ps.py FILE [FILE ...] [--samples=S] [--seed=K] [--jobs=J] [--all] [--max-all=N]
         [--max-cores=C] [--log=OUT]
       python3 k4/induct_ps.py --general [--per=N] [--seed=K] [--jobs=J] [--log=OUT]
  --general: random general additive instances (not cores), n = 3 (m = 4..8) and n = 4 (m = 4..7), values 0..R
  (R = 2, 3, 10; each value 0 with probability pz = 0, 0.3, 0.6), N per (n, m, R, pz); PS(I, w) for every agent.
"""
import gzip, json, os, random, subprocess, sys, itertools, tempfile, time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from induct_run import domain, build, BIN


def load_cores(fn):
    data = json.load(gzip.open(fn))
    cores = data if isinstance(data, list) else data['cores']
    return [(c['sets'], c['m']) for c in cores]


def run(batch):
    inp = []; meta = []
    for sets, m, prof in batch:
        deg = [sum(g in S for S in sets) for g in range(m)]
        V = [[0] * m for _ in sets]
        for i, (S, t) in enumerate(zip(sets, prof)):
            for g, x in zip(S, t): V[i][g] = x
        T = [(w, -1) for w in range(len(sets))]
        T += [(w, p) for w, S in enumerate(sets) if len(S) == 4 for p in S if deg[p] == 1]
        inp.append(f'{len(sets)} {m}'); inp += [' '.join(map(str, r)) for r in V]; inp.append(str(len(T)))
        inp += [f'Q {w} {p}' for w, p in T]
        meta.append((sets, m, prof, T))
    out = [l for l in subprocess.run([BIN], input='\n'.join(inp) + '\n', capture_output=True, text=True,
                                     check=True).stdout.split('\n') if l.startswith('TASK')]
    res = []; k = 0
    for sets, m, prof, T in meta:
        rows = []
        for w, p in T:
            f = out[k].split('|')[1].split(); k += 1
            rows.append((w, p, int(f[1]), int(f[3])))
        res.append((sets, m, prof, rows))
    return res


def run_general(args):
    n, m, R, pz, N, seed = args
    rng = random.Random(seed)
    inp = []; insts = []
    for _ in range(N):
        V = [[(0 if rng.random() < pz else rng.randint(1, R)) for g in range(m)] for i in range(n)]
        insts.append(V)
        inp.append(f'{n} {m}'); inp += [' '.join(map(str, r)) for r in V]; inp.append(str(n))
        inp += [f'Q {w} -1' for w in range(n)]
    out = [l for l in subprocess.run([BIN], input='\n'.join(inp) + '\n', capture_output=True, text=True,
                                     check=True).stdout.split('\n') if l.startswith('TASK')]
    fails = []; k = 0
    for V in insts:
        for w in range(n):
            f = out[k].split('|')[1].split(); k += 1
            if not int(f[1]): fails.append((w, V))
    return (n, m, R, pz, N, fails)


def general(opt, log):
    per = int(opt.get('per', 400)); seed = int(opt.get('seed', 1)); jobs = int(opt.get('jobs', 4))
    tasks = []; s = seed * 1000
    for n in (3, 4):
        for m in range(4, 9 if n == 3 else 8):
            for R in (2, 3, 10):
                for pz in (0.0, 0.3, 0.6):
                    s += 1; tasks.append((n, m, R, pz, per, s))
    tot = tests = nf = 0
    with Pool(jobs) as pool:
        for n, m, R, pz, N, fails in pool.imap_unordered(run_general, tasks):
            tot += N; tests += N * n; nf += len(fails)
            for f in fails[:2]: log(f'  FAIL n={n} m={m} R={R} pz={pz}: w={f[0]} V={f[1]}')
    log(f'general instances: {tot}, PS tests (every agent): {tests}, failures: {nf}')


def main():
    argv = sys.argv[1:]
    if '--general' in argv:
        opt = {a.split('=')[0][2:]: (a.split('=', 1)[1] if '=' in a else True) for a in argv if a.startswith('--')}
        logf = open(opt['log'], 'w') if 'log' in opt else None
        def log(s):
            print(s, flush=True)
            if logf: logf.write(s + '\n'); logf.flush()
        build()
        log('command: python3 k4/induct_ps.py ' + ' '.join(argv))
        t0 = time.time(); general(opt, log); log(f'time {time.time() - t0:.1f}s')
        return
    files = [a for a in argv if not a.startswith('--')]
    opt = {a.split('=')[0][2:]: (a.split('=', 1)[1] if '=' in a else True) for a in argv if a.startswith('--')}
    samples = int(opt.get('samples', 20)); seed = int(opt.get('seed', 1)); jobs = int(opt.get('jobs', 4))
    max_all = int(opt.get('max-all', 0)); maxc = int(opt.get('max-cores', 10 ** 9))
    logf = open(opt['log'], 'w') if 'log' in opt else None
    def log(s):
        print(s, flush=True)
        if logf: logf.write(s + '\n'); logf.flush()
    build()
    log('command: python3 k4/induct_ps.py ' + ' '.join(argv))
    rng = random.Random(seed)
    work = []; nall = 0
    for fn in files:
        for sets, m in load_cores(fn)[:maxc]:
            deg = [sum(g in S for S in sets) for g in range(m)]
            doms = [domain(S, deg) for S in sets]
            tot = 1
            for D in doms: tot *= len(D)
            if opt.get('all') or tot <= max_all:
                nall += 1
                work += [(sets, m, p) for p in itertools.product(*doms)]
            else:
                work += [(sets, m, tuple(rng.choice(D) for D in doms)) for _ in range(samples)]
    log(f'{len(work)} (core, profile) pairs ({nall} cores exhaustively)')
    t0 = time.time()
    cnt = dict(ps=0, ps_fail=0, psd2_fail=0, priv=0, priv_fail=0, privd2_fail=0)
    ex = []
    with Pool(jobs) as pool:
        for res in pool.imap_unordered(run, [work[i:i + 50] for i in range(0, len(work), 50)], chunksize=4):
            for sets, m, prof, rows in res:
                for w, p, a, b in rows:
                    key = 'ps' if p < 0 else 'priv'
                    cnt[key] += 1
                    if not a: cnt[key + '_fail'] += 1
                    if not b: cnt[key + 'd2_fail'] += 1
                    if (not a or not b) and len(ex) < 10: ex.append((key, w, p, a, b, sets, [list(t) for t in prof]))
    log(f'time {time.time() - t0:.1f}s')
    log(f'PS(I, w), every agent w: {cnt["ps"]} tests, failures: {cnt["ps_fail"]} (all allocations), '
        f'{cnt["psd2_fail"]} (D2 allocations)')
    log(f'PS(I - p, w), w 4-good with private p: {cnt["priv"]} tests, failures: {cnt["priv_fail"]} (all), '
        f'{cnt["privd2_fail"]} (D2)')
    for e in ex: log('  FAIL ' + str(e))


if __name__ == '__main__':
    main()
