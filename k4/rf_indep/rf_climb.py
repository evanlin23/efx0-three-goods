"""Climb to OC1^max-failing starts off the certifier's exports, then test RF there (k4/rf_indep/rf_rand.py's (a)-(c)).
Workstream compute/k4-rf-offexport.

Uniform random strict profiles almost never have an OC1-failing maximum-matching start (0 in 2.8M at n = 5), so this
climbs to them.  A profile's score is the minimum over its maximum-matching SD vectors Y (all n! orders) of
- (1000, number of one-absorber completions at the picks) if Y's picks complete, else
- (repairing post-chain states, completions over them) (rf_oc1.c countall; exhaustive),
lower is closer to failure; (0, 0) means OC1 fails at some maximum-matching start.  Mutations as in rkmax_climb.py
(strict profiles, values below 256); a move is accepted when the score does not rise.  Every failing start reached is
deduplicated by (core, ordinal type of every agent, picks) and analysed with rf_rand.analyze: OC1 at every
maximum-matching vector of the profile (witnesses re-checked) and RF (a), (b), (c) for every receiver.

    python3 k4/rf_indep/rf_climb.py --seeds 4000 --steps 2000 [--cores FILE --any-n --min4 2] [--dump FILE]
"""
import sys, os, gzip, json, itertools, collections, time, argparse, tempfile, subprocess, random
import gc as gc_mod
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import rf_check as R
import rf_rand as RR
from rkmax_rand import strict_vals
from rkmax_climb import mutate

G = RR.G


def init_worker(cores, binpath):
    RR.init_worker(cores, {}, binpath)                      # line-mode coprocess for analyze()
    G['pc'] = subprocess.Popen([binpath, 'countall'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)


def score(c, vals):
    sets, m, nu = c['sets'], c['m'], c['nu']; n = len(sets)
    pref = R.prefs(sets, vals)
    M = sorted(set(Y for Y in (R.sd(pref, o) for o in G['perms'][n]) if sum(1 for y in Y if y is not None) == nu), key=str)
    lines = [R.task_line('s%d' % j, sets, vals, m, [[y] if y is not None else [] for y in Y]) for j, Y in enumerate(M)]
    G['pc'].stdin.write('\n'.join(lines) + '\n'); G['pc'].stdin.flush()
    best = None; fails = []
    for j, Y in enumerate(M):
        a = G['pc'].stdout.readline().split()
        if a[0] != 's%d' % j: raise SystemExit('coprocess out of step')
        sc = (1000, int(a[2])) if a[1] == 'Q' else (int(a[2]), int(a[4]))
        if a[1] == 'N' and int(a[2]) == 0: fails.append(Y)
        best = sc if best is None or sc < best else best
    return best, fails


def typesig(vals):
    out = []
    for v in vals:
        k = len(v); sums = [(sum(v[q] for q in range(k) if mask >> q & 1), mask) for mask in range(1 << k)]
        out.append(tuple(mask for _, mask in sorted(sums)))
    return tuple(out)


def climb(job):
    sid, cid, V, steps, init = job
    c = G['cores'][cid]; rnd = random.Random('rfclimb/%d/%d/%d' % (sid, cid, V))
    vals = [list(v) for v in init] if init else [strict_vals(rnd, V, len(s)) for s in c['sets']]
    cur, fails = score(c, vals)
    C = collections.Counter(); recs = []; seen = set(); first = None
    def record(vals, fails, step):
        nonlocal first
        new = []
        for Y in fails:
            key = (typesig(vals), Y)
            if key in seen: continue
            seen.add(key); new.append(Y)
        if new:
            if first is None: first = step
            before = len(recs)
            RR.analyze(c, vals, C, recs, only=set(new))
            for r in recs[before:]: r['climb'] = dict(seed=sid, step=step, V=V); r['type'] = typesig(vals)
    if fails: record(vals, fails, 0)
    for step in range(1, steps + 1):
        new = mutate(rnd, vals, V)
        if new is None: break
        s, f = score(c, new)
        if f: record(new, f, step)
        if s <= cur: vals, cur = new, s
    C['seeds'] += 1; C['seeds reaching a failing start'] += first is not None
    return sid, cid, C, recs, cur


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seeds', type=int, default=4000); ap.add_argument('--steps', type=int, default=2000)
    ap.add_argument('--vmax', default='20,60', help='value ranges, cycled over the seeds')
    ap.add_argument('--seed', type=int, default=1); ap.add_argument('--procs', type=int, default=os.cpu_count() or 4)
    ap.add_argument('--cores', default=os.path.join(ROOT, 'results', 'k4_certs_5_pure.json.gz'))
    ap.add_argument('--any-n', action='store_true'); ap.add_argument('--min4', type=int, default=0)
    ap.add_argument('--min-m', type=int, default=0, help='only cores with at least this many goods')
    ap.add_argument('--bin', default=None); ap.add_argument('--dump', default=None)
    ap.add_argument('--seeds-file', default=None, help='start from these profiles (JSONL: core_m, core_idx, vals); '
                    'one climb per line, value range max(V, the largest value)')
    args = ap.parse_args(); t0 = time.time()
    print('$ python3 k4/rf_indep/rf_climb.py --seeds %d --steps %d --vmax %s --seed %d --procs %d --cores %s%s%s%s'
          % (args.seeds, args.steps, args.vmax, args.seed, args.procs, os.path.basename(args.cores),
             ' --any-n' if args.any_n else '', ' --min4 %d' % args.min4 if args.min4 else '',
             ' --min-m %d' % args.min_m if args.min_m else ''))
    binpath = args.bin or os.path.join(tempfile.gettempdir(), 'rf_oc1_bin_climb')
    subprocess.check_call(['gcc', '-O2', '-o', binpath, os.path.join(HERE, 'rf_oc1.c')])
    raw = json.load(gzip.open(args.cores))
    raw = raw['cores'] if isinstance(raw, dict) else [dict(c, idx=i) for i, c in enumerate(raw)]
    if args.min4: raw = [c for c in raw if sum(1 for s in c['sets'] if len(s) == 4) >= args.min4]
    if args.min_m: raw = [c for c in raw if c['m'] >= args.min_m]
    cores = [dict(sets=c['sets'], m=c['m'], idx=c['idx'], nu=R.nu_kuhn(c['sets']), export=c.get('export')) for c in raw]
    if not args.any_n and any(len(c['sets']) != 5 or any(len(s) != 4 for s in c['sets']) for c in cores):
        raise SystemExit('not a pure n = 5 list')
    print('cores %d from %s (sha256 %s); m %s' % (len(cores), os.path.basename(args.cores), R.sha(args.cores),
          dict(sorted(collections.Counter(c['m'] for c in cores).items()))), flush=True)
    rnd = random.Random('rfclimb-main/%d' % args.seed); Vs = [int(x) for x in args.vmax.split(',')]
    if args.seeds_file:
        pos = {(c['m'], c['idx']): i for i, c in enumerate(cores)}; jobs = []
        for line in gzip.open(args.seeds_file, 'rt'):
            r = json.loads(line)
            if (r['core_m'], r['core_idx']) not in pos: continue
            V = max(Vs[len(jobs) % len(Vs)], max(max(v) for v in r['vals']))
            jobs.append((len(jobs), pos[(r['core_m'], r['core_idx'])], V, args.steps, r['vals']))
        print('seeds from %s: %d' % (os.path.relpath(args.seeds_file, ROOT), len(jobs)), flush=True)
    else:
        jobs = [(i, rnd.randrange(len(cores)), Vs[i % len(Vs)], args.steps, None) for i in range(args.seeds)]
    T = collections.Counter(); rows = []; final = collections.Counter()
    gc_mod.collect(); gc_mod.freeze()
    with Pool(args.procs, initializer=init_worker, initargs=(cores, binpath)) as pool:
        for k, (sid, cid, C, recs, cur) in enumerate(pool.imap_unordered(climb, jobs)):
            T.update(C); rows += recs; final[cur[0] if cur[0] < 1000 else 'picks complete'] += 1
            for r in recs:
                if r.get('flag'): print('FLAG', json.dumps(r), flush=True)
            if (k + 1) % 500 == 0:
                print('  %d seeds, %d failing starts so far, %.0f s' % (k + 1, T['failing starts'], time.time() - t0), flush=True)
    gc_mod.unfreeze()
    print('done %.0f s' % (time.time() - t0))
    print()
    print('(per-seed counts; a failing start reached from two seeds is counted twice here)')
    for k in sorted(T, key=lambda k: (k.startswith(' '), k)): print('   %-72s %d' % (k, T[k]))
    uniq = {}
    for r in rows: uniq.setdefault((r['core_m'], r['core_idx'], json.dumps(r['type']), tuple(r['picks'])), r)
    rows = list(uniq.values())
    U = collections.Counter()
    for r in rows:
        U['failing starts'] += 1
        for u, x in r['per_receiver'].items():
            U['(start, receiver) pairs'] += 1; U['  (a)'] += x['a']; U['  (b)'] += x['b']; U['  (c)'] += x['c']
        for k in 'abc': U["  (%s') some receiver" % k] += r['some_receiver'][k]
        U['  receivers per start %d' % len(r['receivers'])] += 1
    print('globally distinct failing starts (core, ordinal types, picks):')
    for k in sorted(U, key=lambda k: (k.startswith(' '), k)): print('   %-72s %d' % (k, U[k]))
    fs = collections.Counter()
    for k, v in final.items(): fs[k if isinstance(k, str) else str(min(k, 9))] += v
    print('final score of the seeds (repairing states of the closest vector, capped at 9):', dict(sorted(fs.items())))
    cores_with = collections.Counter((r['core_m'], r['core_idx']) for r in rows)
    print('distinct failing starts (core, types, picks): %d on %d cores; m of those cores %s'
          % (len(rows), len(cores_with), dict(sorted(collections.Counter(m for m, _ in cores_with).items()))))
    EXPORT = {(9, 38), (10, 419), (11, 447), (8, 164), (8, 374), (8, 379), (8, 464), (9, 778), (9, 808)}
    if not args.any_n:
        ex = sum(v for k, v in cores_with.items() if k in EXPORT)
        print('  on the 9 export hypergraphs: %d; on other cores: %d (%d cores)'
              % (ex, len(rows) - ex, sum(1 for k in cores_with if k not in EXPORT)))
    if args.dump:
        with gzip.open(args.dump, 'wt') as f:
            for r in rows: f.write(json.dumps(r) + '\n')
        print('dumped %d failing starts to %s' % (len(rows), os.path.relpath(args.dump, ROOT)))
    P = U['(start, receiver) pairs']; flags = [r for r in rows if r.get('flag')]
    print('RESULT RF at climbed failing starts (globally distinct): %d failing starts, %d (start, receiver) pairs; '
          "(a) %d, (b) %d, (c) %d of %d; (a') %d, (b') %d, (c') %d of %d starts; starts with a (b) or (c) failure: %d"
          % (U['failing starts'], P, U['  (a)'], U['  (b)'], U['  (c)'], P, U["  (a') some receiver"],
             U["  (b') some receiver"], U["  (c') some receiver"], U['failing starts'], len(flags)))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
