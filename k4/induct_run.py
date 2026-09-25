"""Driver for k4/induct.c: the insertion lemma of k4/induct.md on certified k = 4 cores and random strict profiles.

For every sampled strict core profile I and every 4-good agent w it runs the tasks
  G w d  (remove good d in R_w), for every d in R_w,
  A w    (remove agent w; its goods stay),
  B w d  (remove agent w and good d),
and records R(task) = max over EFX0 allocations X' of the smaller instance of the repair distance r(X') (the fewest goods
of I - d, other than d, that must change owner to reach an EFX0 allocation of I). The per-profile summaries are:
  best_G   = min over (w, d) of R(G w d)            (the best good to remove)
  priv_G   = min over (w, d), d private to w          (a private good; None if no 4-good agent has one)
  least_G  = min over w of R(G w d_w), d_w = w's least good
  best_A, best_B likewise.

Usage: python3 k4/induct_run.py CERTS.json.gz [...] [--samples=S] [--seed=K] [--jobs=J] [--rmax=R] [--quick]
         [--d2] [--only-g] [--max-cores=C] [--log=FILE]
  --samples: random strict profiles per core (default 20); --all: every profile (only for tiny domains).
  --d2: only D2-shaped X' (at most one bundle of more than 2 goods).
"""
import gzip, json, os, random, subprocess, sys, itertools, tempfile, time
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
OT = json.load(open(os.path.join(HERE, 'order_types.json')))
STRICT_BAL = {k: [tuple(t['rep']) for t in OT[str(k)]['types'] if t['strict'] and t['balanced']] for k in (3, 4)}
BIN = os.environ.get('INDUCT_BIN', os.path.join(tempfile.gettempdir(), 'k4_induct'))


def build():
    src = os.path.join(HERE, 'induct.c')
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-o', BIN, src], check=True)


def domain(S, deg):
    priv = [p for p, g in enumerate(S) if deg[g] == 1]
    dom = STRICT_BAL[len(S)]
    if len(priv) == 2:
        dom = [v for v in dom if v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
    return dom


def values(sets, m, prof):
    V = [[0] * m for _ in sets]
    for i, (S, t) in enumerate(zip(sets, prof)):
        for p, g in enumerate(S): V[i][g] = t[p]
    return V


def tasks_for(sets, m, V, only_g):
    deg = [sum(g in S for S in sets) for g in range(m)]
    T = []
    for w, S in enumerate(sets):
        if len(S) != 4: continue
        for d in S: T.append(('G', w, d))
        if not only_g:
            T.append(('A', w, None))
            for d in S: T.append(('B', w, d))
    return T, deg


def run_batch(args):
    batch, opts = args
    inp = []
    meta = []
    for (sets, m, prof) in batch:
        V = values(sets, m, prof)
        T, deg = tasks_for(sets, m, V, opts['only_g'])
        inp.append(f'{len(sets)} {m}')
        inp += [' '.join(map(str, row)) for row in V]
        inp.append(str(len(T)))
        inp += [f'{k} {w}' + (f' {d}' if d is not None else '') for k, w, d in T]
        meta.append((sets, m, prof, T, deg))
    cmd = [BIN, '-r', str(opts['rmax'])] + (['-q'] if opts['quick'] else []) + (['-D'] if opts['d2'] else [])
    out = subprocess.run(cmd, input='\n'.join(inp) + '\n', capture_output=True, text=True, check=True).stdout
    lines = [l for l in out.split('\n') if l.startswith('TASK')]
    res = []
    k = 0
    for sets, m, prof, T, deg in meta:
        recs = []
        for (kind, w, d) in T:
            f = lines[k].split('|'); k += 1
            maxr = int(f[2].split()[1]); maxrd2 = int(f[2].split()[3])
            nE = int(f[1].split()[1])
            worst = f[5].split()[1:]
            recs.append(dict(kind=kind, w=w, d=d, maxr=maxr, maxrd2=maxrd2, nE=nE, worst=worst,
                             priv=(d is not None and deg[d] == 1),
                             least=(d is not None and prof[w][sets[w].index(d)] == min(prof[w]))))
        res.append((sets, m, prof, recs))
    return res


def summarize(recs, kind, pred=lambda r: True, key='maxr'):
    vals = [r[key] for r in recs if r['kind'] == kind and pred(r)]
    return min(vals) if vals else None


def main():
    argv = sys.argv[1:]
    files = [a for a in argv if not a.startswith('--')]
    opt = {a.split('=')[0][2:]: (a.split('=', 1)[1] if '=' in a else True) for a in argv if a.startswith('--')}
    samples = int(opt.get('samples', 20)); seed = int(opt.get('seed', 1)); jobs = int(opt.get('jobs', 4))
    opts = dict(rmax=int(opt.get('rmax', 3)), quick=bool(opt.get('quick')), d2=bool(opt.get('d2')),
                only_g=bool(opt.get('only-g')))
    maxcores = int(opt.get('max-cores', 10 ** 9))
    logf = open(opt['log'], 'w') if 'log' in opt else None
    def log(s):
        print(s, flush=True)
        if logf: logf.write(s + '\n'); logf.flush()
    build()
    log('command: python3 k4/induct_run.py ' + ' '.join(argv))
    rng = random.Random(seed)
    work = []
    for fn in files:
        data = json.load(gzip.open(fn))
        cores = data['cores'][:maxcores]
        for c in cores:
            sets, m = c['sets'], c['m']
            deg = [sum(g in S for S in sets) for g in range(m)]
            doms = [domain(S, deg) for S in sets]
            if opt.get('all'):
                profs = list(itertools.product(*doms))
            else:
                profs = [tuple(rng.choice(D) for D in doms) for _ in range(samples)]
            for p in profs: work.append((sets, m, p))
    log(f'{len(work)} (core, profile) pairs; options {opts}')
    B = 20
    batches = [(work[i:i + B], opts) for i in range(0, len(work), B)]
    stats = {k: Counter() for k in ('best_G', 'priv_G', 'least_G', 'best_A', 'best_B', 'best_G_d2', 'worst_G')}
    worst_examples = {}
    t0 = time.time()
    with Pool(jobs) as pool:
        for res in pool.imap_unordered(run_batch, batches):
            for sets, m, prof, recs in res:
                s = dict(best_G=summarize(recs, 'G'), priv_G=summarize(recs, 'G', lambda r: r['priv']),
                         least_G=summarize(recs, 'G', lambda r: r['least']),
                         best_A=summarize(recs, 'A'), best_B=summarize(recs, 'B'),
                         best_G_d2=summarize(recs, 'G', key='maxrd2'),
                         worst_G=max((r['maxr'] for r in recs if r['kind'] == 'G'), default=None))
                for k, x in s.items(): stats[k][x] += 1
                key = (s['best_G'], len(sets), m)
                if s['best_G'] is not None and s['best_G'] >= 1 and key not in worst_examples:
                    worst_examples[key] = (sets, prof, [(r['kind'], r['w'], r['d'], r['maxr'], r['maxrd2'], r['nE'], ' '.join(r['worst'])) for r in recs if r['kind'] == 'G'])
    log(f'time {time.time() - t0:.1f}s')
    for k, c in stats.items():
        log(f'{k:10s} ' + ', '.join(f'{x}: {c[x]}' for x in sorted(c, key=lambda z: (z is None, z if z is not None else 0))))
    for key in sorted(worst_examples, key=lambda z: (z[0], z[1], z[2]))[:12]:
        sets, prof, rows = worst_examples[key]
        log(f'example best_G={key[0]} n={key[1]} m={key[2]} sets={sets} prof={[list(p) for p in prof]}')
        for row in rows: log('   ' + str(row))


if __name__ == '__main__':
    main()
