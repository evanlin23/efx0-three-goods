"""Driver for k4/dl2.c (compute/k4-dl2): Conjecture DL2 of k4/strategy.md §3 on data. EVIDENCE only.

  python3 k4/dl2_run.py certs FILE [--sample=P] [--seed=S] [--cores=A:B] [--jobs=J] [--rec=R] [--ckpt=PATH] [--dump=PATH]
  python3 k4/dl2_run.py catalog FILE [--every=E] [--max=N] [--jobs=J] [--rec=R] [--dump=PATH]
  python3 k4/dl2_run.py suite [IDS...] [--maxn=N] [--rec=R] [--dump=PATH]
  python3 k4/dl2_run.py inst FILE.json [--sample=P] [--seed=S] [--rec=R] [--dump=PATH]   (a {"sets", "vals"|"m"} list)
  python3 k4/dl2_run.py ht T [--sample=P] [--seed=S] [--wide] [--rec=R] [--dump=PATH]     (H_T of k4/c4_chain.py)

certs: every strict profile (check4.core_domains: one integer representative per strict balanced type, with the
private-pair condition) of every core of a certificate file results/k4_certs_*.json.gz, or P random ones per core.
catalog: the profiles of a catalogue written by k4/gap_run.py (records with "core" and "vals"), every E-th record.
suite: the complete instances of k4/suite/instances (local configurations skipped).
inst: a JSON list of instances {"id", "sets", "vals"} (one profile each), or with --sample=P and "m", P random strict
profiles of each instance's hypergraph.
ht: the core H_T of k4/c4.md §7 (k4/c4_chain.py build(T)) with §7's values, or with --sample=P, P random strict
profiles of it (H_3 has m = 33: use --wide).

--wide builds dl2.c with 64-bit masks (m <= 64; H_3 has m = 33).
Prints the command, the SHA-256 of dl2.c, per file the counters of dl2.c (k* histogram: 0, 1, 2, >= 3, inf; profiles with
omega >= 1; P with def > 0; the largest least deficit), and the repair table (k4/dl2.c's header defines the
signature, the repair type and the roles). --dump writes dl2.c's "D" records (every profile with k* >= 3 or inf, every
R-th profile with k* = 1 for --rec=R (default 0: none), every Q-th with k* = 2 for --rec2=Q (default 1: all)) as gzip
JSON lines with the core and the values added. --ckpt appends one
JSON line per finished core and skips the cores already in it (resume after a restart). --tables=PATH writes the
merged T/A tables as JSON."""
import gzip, hashlib, json, os, random, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

SRC = os.path.join(HERE, 'dl2.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()
WIDE = '--wide' in sys.argv                     # 64-bit masks (m <= 64), for H_3
BIN = os.path.join(tempfile.gettempdir(), 'k4_dl2_' + SHA[:16] + ('_w' if WIDE else ''))
KEYS = ('prof om1 small kstar0 kstar1 kstar2 kstar3 kstar4 kstarinf kstarn kiso ktrap pos pd1 pd2 pd3 pd4 pdinf piso '
        'ptrap pmpos pm3 maxmin').split()


def build():
    if not os.path.exists(BIN):
        subprocess.run(['gcc', '-O2'] + (['-DWIDE'] if WIDE else []) + ['-o', BIN + '.tmp', SRC], check=True)
        os.replace(BIN + '.tmp', BIN)


def block(sets, m, doms, tag, P, profs=None):
    out = [f"{len(sets)} {m} {tag}"]
    out += [f"{len(S)} {' '.join(map(str, S))}" for S in sets]
    out.append(' '.join(str(len(D)) for D in doms))
    for S, D in zip(sets, doms):
        out += [' '.join(str(d[g]) for g in S) for d in D]
    if profs is None: out.append(str(P))
    else: out.append(str(-len(profs))); out += [' '.join(map(str, p)) for p in profs]
    return '\n'.join(out) + '\n'


def parse(stdout):
    """dl2.c output -> list of blocks {tag, K, T, A, D, V, W}"""
    blocks, curb = [], {'D': [], 'V': [], 'W': []}
    state = 'pre'
    for l in stdout.splitlines():
        if l.startswith('K '):
            w = l.split(); curb['tag'] = int(w[1])
            curb['K'] = {k: int(x) for k, x in zip(w[2::2], w[3::2])}
            curb['T'], curb['A'] = {}, {}
            blocks.append(curb); state = 'post'
            curb = {'D': [], 'V': [], 'W': []}
            continue
        if l.startswith('T ') or l.startswith('A '):
            key, c = l[2:].rsplit(' ', 1)
            blocks[-1][l[0]][key] = blocks[-1][l[0]].get(key, 0) + int(c)
            continue
        if l.startswith('D '): curb['D'].append(json.loads(l[2:]))
        elif l.startswith('V '): curb['V'].append([int(x) for x in l.split()[1:]]); curb['W'].append([])
        elif l.startswith('W '): curb['W'][-1].append([int(x) for x in l.split()[1:]])
    return blocks


def run_blocks(inp, opts):
    r = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if r.returncode: raise RuntimeError(r.stderr)
    return parse(r.stdout)


def run_core(task):
    tag, sets, m, P, opts, seed = task
    t0 = time.time()
    doms = check4.core_domains(sets, m, False)
    b = run_blocks(block(sets, m, doms, tag, P), opts + [f'-S{seed}'])[0]
    for d in b['D']:
        d['vals'] = [[D[p][g] for g in S] for S, D, p in zip(sets, doms, d['prof'])]
    return tag, b, time.time() - t0


def merge(tot, b):
    for k in KEYS:
        if k == 'maxmin':
            if b['K']['om1']: tot[k] = max(tot.get(k, -10 ** 9), b['K'][k])
        else: tot[k] = tot.get(k, 0) + b['K'][k]
    for t in 'TA':
        for key, c in b[t].items(): tot.setdefault(t, {})[key] = tot.setdefault(t, {}).get(key, 0) + c


def report(name, tot, secs):
    K = {k: tot.get(k, 0) for k in KEYS}
    print(f"{name}: profiles {K['prof']}, omega >= 1: {K['om1']}; k* = 0: {K['kstar0']}, 1: {K['kstar1']}, "
          f"2: {K['kstar2']}, 3: {K['kstar3']}, >= 4: {K['kstar4']}, inf: {K['kstarinf']} (k* = n: {K['kstarn']}; "
          f"k* >= 3 isolated / trapped: {K['kiso']} / {K['ktrap']}); P with def > 0: {K['pos']}, at distance 1: {K['pd1']}, "
          f"2: {K['pd2']}, 3: {K['pd3']}, >= 4: {K['pd4']}, inf: {K['pdinf']} (distance >= 3, isolated / trapped: "
          f"{K['piso']} / {K['ptrap']}; Pareto-maximal: {K['pmpos']}, at distance >= 3: {K['pm3']}); largest least deficit {K['maxmin'] if K['om1'] else '-'} [{secs:.0f} s]", flush=True)


def print_tables(tot):
    T, A = tot.get('T', {}), tot.get('A', {})
    print('repair table (canonical witness per P with def > 0): signature | type | roles : count', flush=True)
    for key, c in sorted(T.items(), key=lambda x: -x[1]):
        print(f'  T {key} : {c}')
    print('available repair types (counted once per P): signature | type : count', flush=True)
    for key, c in sorted(A.items(), key=lambda x: -x[1]):
        print(f'  A {key} : {c}')


def main():
    argv = sys.argv[1:]
    mode = argv[0]
    args = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    print('# command: python3 k4/dl2_run.py ' + ' '.join(argv), flush=True)
    print(f'# dl2.c sha256 {SHA}', flush=True)
    build()
    rec = int(opt.get('rec', 0)); jobs = int(opt.get('jobs', 2))
    copts = [f'-r{rec}', f"-q{int(opt.get('rec2', 1))}"]
    dumpf = gzip.open(opt['dump'], 'at') if 'dump' in opt else None
    tot = {}
    t0 = time.time()
    if mode == 'certs':
        P, seed = int(opt.get('sample', 0)), int(opt.get('seed', 1))
        for f in args:
            cores = json.load(gzip.open(f, 'rt'))['cores']
            lo, hi = 0, len(cores)
            if 'cores' in opt: a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
            done = set()
            ck = opt.get('ckpt')
            ftot = {}
            if ck and os.path.exists(ck):
                for l in open(ck):
                    d = json.loads(l)
                    if d['file'] == os.path.basename(f) and d['P'] == P and d['seed'] == seed:
                        done.add(d['pos']); merge(ftot, d['block'])
            tasks = [(k, cores[k]['sets'], cores[k]['m'], P, copts, seed) for k in range(lo, hi) if k not in done]
            print(f'# {os.path.basename(f)}: cores {lo}..{hi - 1} ({len(tasks)} to run, {len(done & set(range(lo, hi)))} '
                  f'from the checkpoint), {"every profile" if not P else f"{P} random profiles per core, seed {seed}"}', flush=True)
            ft = time.time()
            with Pool(jobs) as pool:
                for tag, b, secs in pool.imap_unordered(run_core, tasks):
                    merge(ftot, b)
                    for d in b['D']:
                        c = cores[tag]
                        d['core'] = {'file': os.path.basename(f), 'pos': tag, 'idx': c.get('idx', tag), 'm': c['m'], 'sets': c['sets']}
                        if dumpf: dumpf.write(json.dumps(d, separators=(',', ':')) + '\n')
                    if dumpf: dumpf.flush()
                    if ck:
                        with open(ck, 'a') as fo:
                            fo.write(json.dumps({'file': os.path.basename(f), 'pos': tag, 'P': P, 'seed': seed, 'secs': round(secs, 1),
                                                 'block': {'K': b['K'], 'T': b['T'], 'A': b['A']}}) + '\n')
                    if 'progress' in opt: print(f'#   core {tag}: {b["K"]} [{secs:.1f} s]', flush=True)
            report(os.path.basename(f) + (f' cores {lo}..{hi - 1}' if 'cores' in opt else ''), ftot, time.time() - ft)
            merge_tot(tot, ftot)
    else:
        insts = []
        if mode == 'catalog':
            recs = json.load(gzip.open(args[0], 'rt'))['records'][::int(opt.get('every', 1))]
            if 'max' in opt: recs = recs[:int(opt['max'])]
            insts = [{'id': f"{r['core']['file']}#{r['core']['pos']}:{r['prof']}", 'sets': r['core']['sets'], 'm': r['core']['m'],
                      'vals': r['vals']} for r in recs]
        elif mode == 'suite':
            import glob
            ids = set(args)
            for fn in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
                d = json.load(open(fn))
                if 'kind' in d or (ids and d['id'] not in ids): continue
                if len(d['sets']) > int(opt.get('maxn', 16)): continue
                insts.append(d)
        elif mode == 'inst':
            insts = json.load(open(args[0]))
        elif mode == 'ht':
            import c4_chain
            t = int(args[0]); sets, vals, m = c4_chain.build(t)
            insts = [{'id': f'H_{t}', 'sets': sets, 'vals': vals, 'm': m}]
            if int(opt.get('sample', 0)):              # split the sample over the workers (distinct tags, distinct streams)
                insts = [dict(insts[0], id=f'H_{t}#{j}') for j in range(jobs)]
                opt['sample'] = str(-(-int(opt['sample']) // jobs))
        P = int(opt.get('sample', 0)); seed = int(opt.get('seed', 1))
        out = []
        tasks = []
        for k, d in enumerate(insts):
            sets = d['sets']; m = d.get('m') or 1 + max(g for S in sets for g in S)
            if P:
                doms = check4.core_domains(sets, m, False)
                tasks.append((k, block(sets, m, doms, k, P), doms))
            else:
                doms = [[dict(zip(S, V))] for S, V in zip(sets, d['vals'])]
                tasks.append((k, block(sets, m, doms, k, 0), doms))
        chunks = [tasks[i::jobs] for i in range(jobs)]
        rec2 = int(opt.get('rec2', 1)); seen = {1: 0, 2: 0}
        topts = (copts if P else ['-r1', '-q1']) + [f'-S{seed}'] + (['-v'] if not P else [])
        with Pool(jobs) as pool:
            res = pool.map(_run_chunk, [(c, topts) for c in chunks])
        bymap = {}
        for blocks in res:
            for b in blocks: bymap[b['tag']] = b
        for k, d in enumerate(insts):
            b = bymap[k]; merge(tot, b)
            doms = tasks[k][2]
            if not P:
                ks = b['V'][0][n_of(d)] if b['V'] else None
                ks = None if ks == -2 else ('inf' if ks == -1 else ks)
                if mode != 'catalog' or opt.get('verbose'):
                    print(f"{d['id']:<44} n={len(d['sets'])}  k*={ks}  " + (f"{b['V'][0][n_of(d) + 1]} min-frozen P, {b['V'][0][n_of(d) + 2]} with def > 0, least def {b['V'][0][n_of(d) + 3]}" if ks is not None else 'omega<=0'), flush=True)
            for r in b['D']:
                if not P and r['kstar'] in (1, 2):         # one profile per block: sample here
                    seen[r['kstar']] += 1; every = rec if r['kstar'] == 1 else rec2
                    if every <= 0 or (seen[r['kstar']] - 1) % every: continue
                r['vals'] = [[D[p][g] for g in S] for S, D, p in zip(d['sets'], doms, r['prof'])]
                r['core'] = {'id': d.get('id'), 'm': d.get('m') or 1 + max(g for S in d['sets'] for g in S), 'sets': d['sets']}
                if dumpf: dumpf.write(json.dumps(r, separators=(',', ':')) + '\n')
        report(mode + (' ' + args[0] if args and mode != 'suite' else ''), tot, time.time() - t0)
        if mode in ('catalog', 'suite', 'inst', 'ht') and not P:
            print(f'# dumped: every profile with k* >= 3, every {rec}-th with k* = 1 (0: none), every {rec2}-th with k* = 2',
                  flush=True)
    if mode == 'certs' and len(args) > 1: report('total', tot, time.time() - t0)
    print_tables(tot)
    if 'tables' in opt:
        json.dump({'command': 'python3 k4/dl2_run.py ' + ' '.join(argv), 'dl2_c_sha256': SHA,
                   'counters': {k: tot.get(k, 0) for k in KEYS}, 'T': tot.get('T', {}), 'A': tot.get('A', {})},
                  open(opt['tables'], 'w'), indent=0, sort_keys=True)
    if dumpf: dumpf.close()


def merge_tot(tot, ftot):
    for k in KEYS:
        if k not in ftot: continue
        if k == 'maxmin': tot[k] = max(tot.get(k, -10 ** 9), ftot[k])
        else: tot[k] = tot.get(k, 0) + ftot[k]
    for t in 'TA':
        for key, c in ftot.get(t, {}).items(): tot.setdefault(t, {})[key] = tot.setdefault(t, {}).get(key, 0) + c


def n_of(d): return len(d['sets']) + 1


def _run_chunk(arg):
    chunk, opts = arg
    if not chunk: return []
    return run_blocks(''.join(t[1] for t in chunk), opts)


if __name__ == '__main__':
    main()
