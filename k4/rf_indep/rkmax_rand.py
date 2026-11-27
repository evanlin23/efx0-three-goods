"""Random hunt for a counterexample to Conjecture RKMAX (k4/sdc.md section 31 end, K4.SDC.RKMAX) on every pure n = 5
core.  Workstream compute/k4-rf-indep; same own code as rkmax_check.py (SD, nu, ranks, OC1 search rf_oc1.c with every
witness re-checked by k4/d1/d1lib.py, F answers re-checked in pure Python).

Cores: the 4,674 pure n = 5 cores of results/k4_certs_5_pure.json.gz (k4/frontier), named (m, idx) as there; the
certifier's "5_pure #k" with m goods is the core (m, k).  Profiles: strict (all 16 subset sums of each agent distinct),
each agent's four values a random 4-subset of 1..V in random order; V = 20 is the distribution of k4/oc1_hall.md
section 24.14 (60 profiles per core there).  Seeds are fixed per (V, seed, core).

For each profile: the SD picks of all 120 orders, the maximum matchings among them, the sigma-maximal ones, and OC1 at
each.  Also counted: the receivers of each sigma-maximal vector (agents with a pick whose pick no other agent prefers to
its own), for comparison with Hall's census.

    python3 k4/rf_indep/rkmax_rand.py --per-core 600 --vmax 20 --seed 1 [--procs 4]
"""
import sys, os, gzip, json, itertools, collections, time, argparse, tempfile, subprocess, random
import gc as gc_mod
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import rf_check as R
from rkmax_check import sigma

G = {}


def strict_vals(rnd, vmax, k):
    while True:
        v = rnd.sample(range(1, vmax + 1), k)
        sums = [sum(v[i] for i in range(k) if mask >> i & 1) for mask in range(1 << k)]
        if len(set(sums)) == len(sums): return v


def init_worker(cores, args):
    G['cores'] = cores; G['args'] = args
    G['perms'] = {n: list(itertools.permutations(range(n))) for n in set(len(c['sets']) for c in cores)}


def work(cid):
    c = G['cores'][cid]; a = G['args']
    sets, m, nu = c['sets'], c['m'], c['nu']; n = len(sets)
    rnd = random.Random('%d/%d/%d/%d' % (a['vmax'], a['seed'], c['m'], c['idx']))
    C = collections.Counter(); keys = []
    for _ in range(a['per_core']):
        vals = [strict_vals(rnd, a['vmax'], len(s)) for s in sets]
        pref = R.prefs(sets, vals)
        vecs = set(R.sd(pref, o) for o in G['perms'][n])
        mm = [Y for Y in vecs if sum(1 for y in Y if y is not None) == nu]
        C['profiles'] += 1
        if not mm: C['PROFILES WITHOUT A MAXIMUM-MATCHING SD VECTOR'] += 1; continue
        sig = {Y: sigma(sets, vals, Y) for Y in mm}
        best = max(sig.values())
        top = [Y for Y in mm if sig[Y] == best]
        C['sigma-maximal vectors'] += len(top)
        pk = R.prof_key(vals)
        for Y in top:
            nrec = len(R.receivers(sets, vals, Y))
            C['sigma-maximal vectors with %d receiver(s)' % nrec] += 1
            keys.append((nrec, pk + R.ybytes(Y)))
    return cid, C, keys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--per-core', type=int, default=600); ap.add_argument('--vmax', type=int, default=20)
    ap.add_argument('--seed', type=int, default=1); ap.add_argument('--procs', type=int, default=os.cpu_count() or 4)
    ap.add_argument('--cores', default=os.path.join(ROOT, 'results', 'k4_certs_5_pure.json.gz'))
    ap.add_argument('--bin', default=None); ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--dump', default=None, help='write the one-receiver sigma-maximal vectors (JSONL, gzip) here')
    ap.add_argument('--any-n', action='store_true', help='allow a core list that is not pure n = 5')
    args = ap.parse_args(); t0 = time.time()
    print('$ python3 k4/rf_indep/rkmax_rand.py --per-core %d --vmax %d --seed %d --procs %d'
          % (args.per_core, args.vmax, args.seed, args.procs))
    binpath = args.bin or os.path.join(tempfile.gettempdir(), 'rf_oc1_bin')
    subprocess.check_call(['gcc', '-O2', '-o', binpath, os.path.join(HERE, 'rf_oc1.c')])
    raw = json.load(gzip.open(args.cores))['cores']
    if args.limit: raw = raw[:args.limit]
    cores = []
    for c in raw:
        nu = R.nu_kuhn(c['sets'])
        if nu != R.nu_brute(c['sets']): raise SystemExit('nu mismatch')
        cores.append(dict(sets=c['sets'], m=c['m'], idx=c['idx'], nu=nu))
    print('cores %d from %s (sha256 %s); nu distribution %s' % (len(cores), os.path.relpath(args.cores, ROOT),
          R.sha(args.cores), dict(collections.Counter(c['nu'] for c in cores))))
    if not args.any_n and (any(len(s) != 4 for c in cores for s in c['sets']) or any(len(c['sets']) != 5 for c in cores)):
        raise SystemExit('not a pure n = 5 list')
    print('agents per core %s, goods per core %s' % (dict(collections.Counter(len(c['sets']) for c in cores)),
          dict(sorted(collections.Counter(c['m'] for c in cores).items()))))
    T = collections.Counter(); tops = {}
    gc_mod.collect(); gc_mod.freeze()
    a = dict(vmax=args.vmax, seed=args.seed, per_core=args.per_core)
    with Pool(args.procs, initializer=init_worker, initargs=(cores, a)) as pool:
        for cid, C, keys in pool.imap_unordered(work, range(len(cores)), chunksize=8):
            T.update(C); tops[cid] = keys
    gc_mod.unfreeze()
    print('orders and signatures done %.0f s' % (time.time() - t0), flush=True)

    def gen():
        for cid in sorted(tops):
            c = cores[cid]; n = len(c['sets'])
            for j, (nrec, key) in enumerate(tops[cid]):
                B = [[y] if y != 255 else [] for y in key[-n:]]
                vals = []; flat = list(key[:-n]); p = 0
                for s in c['sets']: vals.append(flat[p:p + len(s)]); p += len(s)
                yield R.task_line('r%d:%d:%d' % (nrec, cid, j), c['sets'], vals, c['m'], B)
    shards, ntasks = R.run_shards(gen(), args.procs, binpath, 'rkr')
    print('OC1 search on %d sigma-maximal vectors done %.0f s' % (ntasks, time.time() - t0), flush=True)
    ver = collections.defaultdict(collections.Counter); fails = []; percore = collections.Counter()
    gc_mod.collect(); gc_mod.freeze()
    with Pool(args.procs) as pool:
        for out, F in pool.imap(R.verify_shard, shards):
            for (gcl, cid), C in out.items():
                ver[gcl].update(C)
                percore[cid] += sum(v for k, v in C.items() if k.startswith('C '))
            fails += F
        second = pool.map(R.py_from_line, fails) if fails else []
    gc_mod.unfreeze()
    print('witnesses verified %.0f s' % (time.time() - t0), flush=True)
    if args.dump:
        nd = 0
        with gzip.open(args.dump, 'wt') as f:
            for fifo in shards:
                for line, a in R.pairs(*fifo):
                    if not line.startswith('r1:'): continue
                    tid, sets, vals, m, B = R.parse_task(line); c = cores[int(tid.split(':')[1])]
                    Y = [b[0] if b else None for b in B]
                    f.write(json.dumps(dict(core_m=c['m'], core_idx=c['idx'], sets=sets, vals=vals, picks=Y,
                                            sigma=sigma(sets, vals, Y), receivers=R.receivers(sets, vals, Y),
                                            oc1=' '.join(a))) + '\n'); nd += 1
        print('dumped %d one-receiver sigma-maximal vectors to %s' % (nd, os.path.relpath(args.dump, ROOT)), flush=True)

    print()
    for k in sorted(T): print('   %-70s %d' % (k, T[k]))
    print('OC1 at the sigma-maximal vectors, by number of receivers:')
    tot = collections.Counter()
    for gcl in sorted(ver):
        print('   %-6s %s' % (gcl, dict(sorted(ver[gcl].items()))))
        tot.update(ver[gcl])
    print('   all    %s' % dict(sorted(tot.items())))
    print('cores with a sigma-maximal vector that needs a move: %d' % sum(1 for v in percore.values() if v))
    for line, r2 in zip(fails, second):
        tid, sets, vals, m, B = R.parse_task(line)
        c = cores[int(tid.split(':')[1])]
        print('F core (m %d, idx %d) sets %s vals %s picks %s receivers %s; second implementation: %s'
              % (c['m'], c['idx'], json.dumps(sets), json.dumps(vals), [b[0] if b else None for b in B], tid.split(':')[0], r2))
    bad = sum(v for k, v in tot.items() if 'INVALID' in k)
    print('RESULT RKMAX random: %d cores x %d profiles (V = %d, seed %d): %d sigma-maximal vectors, OC1 F answers %d '
          '(confirmed by the second implementation: %d), invalid witnesses %d'
          % (len(cores), args.per_core, args.vmax, args.seed, T['sigma-maximal vectors'], tot['F'],
             sum(1 for r in second if r == 'F'), bad))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
