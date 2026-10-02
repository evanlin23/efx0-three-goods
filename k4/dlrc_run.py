"""Driver for k4/dlrc.c (compute/k4-rc): Conjecture DL_RC (R_C = RT4 + the frozen-chain role swap T3c) on data, and its
key-graph form. EVIDENCE only.

A copy of k4/dlrt4_run.py (compute/k4-rt4, unchanged) that builds and runs k4/dlrc.c instead of k4/dlrt4.c, with the same
modes and options. It reports dlrt4.c's counters and tables (dlrc.c computes them with dlrt4.c's code) and, besides,
dlrc.c's "LC" counters (DL_RC, the chain states, the least |W|, the key-graph form) and its table W (k4/dlrc.c's header
defines them). Its "--src" default is dlrc.c; --cores=A:B:S takes every S-th core of A..B-1.

The rest of this docstring is dlrt4_run.py's (read dlrc for dlrt4 and DL_RC for DL_RT4 where it applies).

  python3 k4/dlrc_run.py certs FILE... [--sample=P] [--seed=S] [--cores=A:B[:S]] [--bt=all|one] [--jobs=J] [--ckpt=PATH]
  python3 k4/dlrc_run.py catalog FILE [--every=E] [--max=N] [--chunk=C] [--jobs=J] [--ckpt=PATH]
  python3 k4/dlrc_run.py suite [IDS...] [--minn=N] [--maxn=N] [--sample=P] [--seed=S] [--bt=...]
  python3 k4/dlrc_run.py inst FILE.json [--sample=P] [--seed=S]       (a JSON list of {"id", "sets", "vals"|"m"})
  python3 k4/dlrc_run.py ht T [--sample=P] [--seed=S] [--wide]           (H_T of k4/c4_chain.py)
common: [--dump=PATH.jsonl.gz] [--tables=PATH.json] [--rt=R] [--ro=O] [--progress] [--src=OTHER.c] [--bigpp=B]

certs: every strict profile (check4.core_domains: one integer representative per strict balanced type, with the
private-pair condition) of every core of a certificate file results/k4_certs_*.json.gz, or P random ones per core
(dlrt4.c's generator = dl13.c's = dl2.c's, seeded by --seed and the core's position; so --sample=P --seed=S draws the
same profiles as dl13_run.py with the same options). --bt=all restricts every 4-good agent to its big-top types
(top > second + third: 48 of the 288 types); --bt=one runs, per core, one block per 4-good agent with only that agent
restricted (profiles with two big-top agents are then counted in two blocks).
catalog: the profiles of a catalogue of k4/gap_run.py (records with "core" and "vals"), every E-th record, in chunks
of C records (default 2000), one dlrt4.c process per chunk.
suite: the complete instances of k4/suite/instances (their profile), or --sample=P random strict profiles of each
instance's hypergraph (cores only).
inst: a JSON list of single profiles {"id", "sets", "vals", "m"} (k4/dlrt4_ref.py writes such lists).

Each unit (a core, a block of a core, a chunk of a catalogue) is one dlrt4.c process; --ckpt appends one JSON line per
finished unit and skips the units already in it (resume after a restart; the dump is written before the checkpoint
line, one gzip member per unit). --dump writes dlrt4.c's "D" records (every f >= 1 state where DL_RT4 fails, with every
better min-frozen P' (at most 400); the first f >= 1 state of each (signature, branch) cell per process; every R-th
state that needs a branch outside R_13 (no T1 or T3 move, DL_RT4 holding) for --rt=R (default 50); every O-th other
state for --ro=O (default 0: none); the first 5 f = 0 states where RT4 fails) with the core and the values added.
--tables writes the merged counters and tables as JSON.
Prints the command, the SHA-256 of dlrt4.c, per file dl2.c's counters (dlrt4.c computes them with dl2.c's code) and
DL_RT4's counters, then the tables."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

WIDE = '--wide' in sys.argv
BIGPP = next((a.split('=', 1)[1] for a in sys.argv if a.startswith('--bigpp=')), None)   # test builds only


def configure(src):
    """the C source to build and run: k4/dlrt4.c (default), or another source with the same output format (--src)"""
    global SRC, SHA, BIN
    SRC = os.path.join(HERE, src)
    SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()
    BIN = os.path.join(tempfile.gettempdir(), 'k4_dlrc_' + SHA[:16] + ('_w' if WIDE else '') + (f'_b{BIGPP}' if BIGPP else ''))


configure(next((a.split('=', 1)[1] for a in sys.argv if a.startswith('--src=')), 'dlrc.c'))
KEYS = ('prof om1 small kstar0 kstar1 kstar2 kstar3 kstar4 kstarinf kstarn kiso ktrap pos pd1 pd2 pd3 pd4 pdinf piso '
        'ptrap pmpos pm3 maxmin').split()
LKEYS = ('st0 st1 fail0 fail1 t1 t2 t3p t3h t4 t1only t2only t3only t4only rtfail r13fail r134fail anom anom4 rdnone rd1 '
         'rd2 rd3 rd4').split()
CKEYS = ('st1 rcfail rt4fail chain chain3 t3c t3w t3wonly w0 w1 w2 w3 cw1 cw2 cw3 keyfail keyfailk keyfailw keyspos rcnokey '
         'anomc').split()


def build():
    if not os.path.exists(BIN):
        subprocess.run(['gcc', '-O2'] + (['-DWIDE'] if WIDE else []) + ([f'-DBIGPP={BIGPP}'] if BIGPP else [])
                       + ['-o', BIN + '.tmp', SRC], check=True)
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
    """dlrc.c output -> list of blocks {tag, K, L, LC, tab, D, V, S, H}"""
    blocks, curb = [], {'D': [], 'V': [], 'S': [], 'H': []}
    for l in stdout.splitlines():
        if l.startswith('K '):
            w = l.split(); curb['tag'] = int(w[1])
            curb['K'] = {k: int(x) for k, x in zip(w[2::2], w[3::2])}
            curb['tab'] = {}
            blocks.append(curb)
            curb = {'D': [], 'V': [], 'S': [], 'H': []}
        elif l.startswith('L '):
            w = l.split(); blocks[-1]['L'] = {k: int(x) for k, x in zip(w[2::2], w[3::2])}
        elif l.startswith('LC '):
            w = l.split(); blocks[-1]['LC'] = {k: int(x) for k, x in zip(w[2::2], w[3::2])}
        elif l.startswith('H '): curb['H'].append([int(x) for x in l.split()[1:]])
        elif l[:2] in ('B ', 'G ', 'M ', 'Z ', 'C ', 'Y ', 'W '):
            key, c = l.rsplit(' ', 1)
            blocks[-1]['tab'][key] = blocks[-1]['tab'].get(key, 0) + int(c)
        elif l.startswith('D '): curb['D'].append(json.loads(l[2:]))
        elif l.startswith('V '): curb['V'].append([int(x) for x in l.split()[1:]]); curb['S'].append([])
        elif l.startswith('S '): curb['S'][-1].append(l.split()[1:])
    return blocks


def run_blocks(inp, opts):
    r = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if r.returncode: raise RuntimeError(r.stderr)
    return parse(r.stdout)


def bt_dom(D, S):
    """the big-top types of a 4-good agent's domain"""
    if len(S) != 4: return D
    return [d for d in D if (lambda w: w[3] > w[2] + w[1])(sorted(d[g] for g in S))]


def unit_certs(task):
    """one core (or one block of it): every profile, or P random ones"""
    key, sets, m, P, seed, bt, opts = task
    t0 = time.time()
    doms = check4.core_domains(sets, m, False)
    if bt == 'all': doms = [bt_dom(D, S) for D, S in zip(doms, sets)]
    elif bt is not None: doms = [bt_dom(D, S) if i == bt else D for i, (D, S) in enumerate(zip(doms, sets))]
    b = run_blocks(block(sets, m, doms, key['pos'], P), opts + [f'-S{seed}'])[0]
    for d in b['D']:
        d['vals'] = [[D[p][g] for g in S] for S, D, p in zip(sets, doms, d['prof'])]
    return key, [b], time.time() - t0


def unit_list(task):
    """a list of single profiles (catalogue chunk, suite, instances): one block each"""
    key, insts, opts = task
    t0 = time.time()
    inp = []
    for k, d in enumerate(insts):
        doms = [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])]
        inp.append(block(d['sets'], d['m'], doms, k, 0))
    bl = run_blocks(''.join(inp), opts) if inp else []
    for b in bl:
        d = insts[b['tag']]
        for r in b['D']:
            r['vals'] = d['vals']; r['core'] = {'id': d['id'], 'm': d['m'], 'sets': d['sets']}
    return key, bl, time.time() - t0


def merge(tot, b):
    for k in KEYS:
        if k == 'maxmin':
            if b['K']['om1']: tot[k] = max(tot.get(k, -10 ** 9), b['K'][k])
        else: tot[k] = tot.get(k, 0) + b['K'][k]
    for k in LKEYS: tot[k] = tot.get(k, 0) + b['L'][k]
    for k in CKEYS: tot['c_' + k] = tot.get('c_' + k, 0) + b['LC'][k]
    for key, c in b['tab'].items(): tot.setdefault('tab', {})[key] = tot.setdefault('tab', {}).get(key, 0) + c


def merge_tot(tot, ftot):
    for k in KEYS + LKEYS + ['c_' + x for x in CKEYS]:
        if k not in ftot: continue
        if k == 'maxmin': tot[k] = max(tot.get(k, -10 ** 9), ftot[k])
        else: tot[k] = tot.get(k, 0) + ftot[k]
    for key, c in ftot.get('tab', {}).items(): tot.setdefault('tab', {})[key] = tot.setdefault('tab', {}).get(key, 0) + c


def report(name, tot, secs):
    K = {k: tot.get(k, 0) for k in KEYS + LKEYS}
    print(f"{name}: profiles {K['prof']}, omega >= 1: {K['om1']}; k* = 0: {K['kstar0']}, 1: {K['kstar1']}, "
          f"2: {K['kstar2']}, 3: {K['kstar3']}, >= 4: {K['kstar4']}, inf: {K['kstarinf']}; P with def > 0: {K['pos']}, at "
          f"distance 1: {K['pd1']}, 2: {K['pd2']}, 3: {K['pd3']}, >= 4: {K['pd4']}, inf: {K['pdinf']}; Pareto-maximal: "
          f"{K['pmpos']}; largest least deficit {K['maxmin'] if K['om1'] else '-'}", flush=True)
    print(f"  DL_RT4: states (def > 0) with f = 0: {K['st0']} (RT4 fails at {K['fail0']}), with f >= 1: {K['st1']}; "
          f"DL_RT4 FAILS at {K['fail1']} of the f >= 1 states; with an improving move T1 {K['t1']}, T2 {K['t2']}, "
          f"T3p {K['t3p']}, T3h {K['t3h']}, T4 {K['t4']}; only T1 {K['t1only']}, only T2 {K['t2only']}, only T3 "
          f"{K['t3only']}, only T4 {K['t4only']}; R_T fails at {K['rtfail']}, R_13 at {K['r13fail']}, R_13 + T4 at "
          f"{K['r134fail']}; smallest RT4 move size 1 / 2 / 3 / >= 4 / none: {K['rd1']} / {K['rd2']} / {K['rd3']} / "
          f"{K['rd4']} / {K['rdnone']}; anomalies {K['anom']} + {K['anom4']} "
          f"[{secs:.0f} s]", flush=True)
    C = {k: tot.get('c_' + k, 0) for k in CKEYS}
    print(f"  DL_RC: f >= 1 states {C['st1']}; DL_RC FAILS at {C['rcfail']}; DL_RT4 fails at {C['rt4fail']}, of which "
          f"{C['chain']} are chain states (only T3c moves improve; {C['chain3']} with f >= 3; by least |W| 1 / 2 / >= 3: "
          f"{C['cw1']} / {C['cw2']} / {C['cw3']}); with an improving T3c move {C['t3c']}, weak T3+ {C['t3w']} (the only "
          f"repair at {C['t3wonly']}); least improving |W| 0 / 1 / 2 / >= 3: {C['w0']} / {C['w1']} / {C['w2']} / {C['w3']}; "
          f"key graph: keys with def* > 0: {C['keyspos']}, the key form FAILS at {C['keyfailk']} keys ({C['keyfail']} "
          f"states; weak edges: {C['keyfailw']} states); DL_RC without the key form {C['rcnokey']}; T3+/T3 "
          f"inconsistencies {C['anomc']}", flush=True)


def print_tables(tot):
    tab = tot.get('tab', {})
    for t, title in (('B', 'f >= 1 states by f | signature | branch'), ('G', 'f >= 1 states by f | nearest distance k | branch'),
                     ('M', 'f >= 1 states by f | branch | smallest RT4 move size'),
                     ('Z', 'f >= 1 states by f | branch available | its smallest move size'),
                     ('C', 'f >= 1 states with T4 by f | smallest T4 size | cycle types at that size'),
                     ('Y', 'f >= 1 states by f | branch | move type available'),
                     ('W', 'f >= 1 states by f | R_C branch | least improving |W| (-1: no T3+ move)')):
        print(f'table {t}: {title} : count', flush=True)
        for key, c in sorted(((k, c) for k, c in tab.items() if k[0] == t), key=lambda x: (-x[1], x[0])):
            print(f'  {key} : {c}')


def dump_write(path, recs):
    """append the records to PATH as one complete gzip member (a killed run loses at most the member being written)"""
    if not path or not recs: return
    with gzip.open(path, 'at') as fo:
        for r in recs: fo.write(json.dumps(r, separators=(',', ':')) + '\n')


def run_units(fn, tasks, jobs, ck, ckey, onres):
    """run the units through a pool, checkpointing each finished one"""
    if not tasks: return
    with Pool(jobs) as pool:
        for key, bl, secs in pool.imap_unordered(fn, tasks):
            onres(key, bl, secs)
            if ck:                     # one merged block per unit (a catalogue chunk has one block per record)
                u = {}
                for b in bl: merge(u, b)
                mb = {'K': {k: u.get(k, 0) for k in KEYS}, 'L': {k: u.get(k, 0) for k in LKEYS},
                      'LC': {k: u.get('c_' + k, 0) for k in CKEYS}, 'tab': u.get('tab', {})}
                if 'maxmin' not in u: mb['K']['maxmin'] = 0
                with open(ck, 'a') as fo:
                    fo.write(json.dumps({'ckey': ckey, 'key': key, 'secs': round(secs, 1), 'blocks': [mb]}) + '\n')


def load_ckpt(ck, ckey):
    done = {}
    if ck and os.path.exists(ck):
        for l in open(ck):
            try: d = json.loads(l)
            except ValueError: continue                       # a line cut by a kill
            if d['ckey'] == ckey: done[json.dumps(d['key'], sort_keys=True)] = d['blocks']
    return done


def main():
    argv = sys.argv[1:]
    mode = argv[0]
    args = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    print('# command: python3 k4/dlrc_run.py ' + ' '.join(argv), flush=True)
    print(f'# {os.path.basename(SRC)} sha256 {SHA}', flush=True)
    build()
    jobs = int(opt.get('jobs', 2)); ck = opt.get('ckpt'); dump = opt.get('dump')
    copts = [f"-r{int(opt.get('rt', 50))}", f"-o{int(opt.get('ro', 0))}"]
    P, seed = int(opt.get('sample', 0)), int(opt.get('seed', 1))
    bt = opt.get('bt')
    tot = {}
    t0 = time.time()
    if mode == 'certs':
        for f in args:
            cores = json.load(gzip.open(f, 'rt'))['cores']
            lo, hi = 0, len(cores)
            step = 1
            if 'cores' in opt:
                w = opt['cores'].split(':'); lo, hi = int(w[0] or 0), int(w[1] or len(cores))
                if len(w) > 2: step = int(w[2])
            ckey = {'mode': 'certs', 'file': os.path.basename(f), 'P': P, 'seed': seed, 'bt': bt, 'copts': copts}
            done = load_ckpt(ck, ckey)
            ftot = {}
            tasks = []
            for k in range(lo, hi, step):
                c = cores[k]
                if bt == 'one':
                    blks = [i for i, S in enumerate(c['sets']) if len(S) == 4]
                else: blks = [None]
                for bi in blks:
                    key = {'pos': k, 'blk': bi}
                    kj = json.dumps(key, sort_keys=True)
                    if kj in done:
                        for b in done[kj]: merge(ftot, b)
                        continue
                    tasks.append((key, c['sets'], c['m'], P, seed, 'all' if bt == 'all' else bi, copts))
            print(f'# {os.path.basename(f)}: cores {lo}..{hi - 1}' + (f' (every {step}th)' if step > 1 else '') + f', {len(tasks)} units to run, {len(done)} from the '
                  f'checkpoint; {"every profile" if not P else f"{P} random profiles per unit, seed {seed}"}'
                  + (f'; big-top restriction {bt}' if bt else ''), flush=True)
            ft = time.time()

            def onres(key, bl, secs, f=f):
                for b in bl:
                    merge(ftot, b)
                    c = cores[key['pos']]
                    for d in b['D']:
                        d['core'] = {'file': os.path.basename(f), 'pos': key['pos'], 'idx': c.get('idx', key['pos']),
                                     'm': c['m'], 'sets': c['sets']}
                        if key.get('blk') is not None: d['btagent'] = key['blk']
                    dump_write(dump, b['D'])
                    if b['LC']['rcfail']: print(f"#   DL_RC FAILS: core {key}: {b['LC']['rcfail']} states", flush=True)
                    if b['LC']['keyfail']: print(f"#   KEY FORM FAILS: core {key}: {b['LC']['keyfail']} states", flush=True)
                    if b['LC']['chain']: print(f"#   chain states (DL_RT4 fails, DL_RC holds): core {key}: {b['LC']['chain']}", flush=True)
                if 'progress' in opt:
                    L = bl[0]['L']; K = bl[0]['K']; C = bl[0]['LC']
                    print(f"#   unit {key}: om1 {K['om1']} pos {K['pos']} st1 {L['st1']} fail1 {L['fail1']} t4 {L['t4']} "
                          f"t4only {L['t4only']} t2only {L['t2only']} rtfail {L['rtfail']} rcfail {C['rcfail']} chain "
                          f"{C['chain']} t3c {C['t3c']} keyfail {C['keyfail']} [{secs:.1f} s]", flush=True)
            run_units(unit_certs, tasks, jobs, ck, ckey, onres)
            report(os.path.basename(f) + (f' cores {lo}..{hi - 1}' if 'cores' in opt else ''), ftot, time.time() - ft)
            merge_tot(tot, ftot)
        if len(args) > 1: report('total', tot, time.time() - t0)
    else:
        insts = []
        if mode == 'catalog':
            recs = json.load(gzip.open(args[0], 'rt'))['records'][::int(opt.get('every', 1))]
            if 'max' in opt: recs = recs[:int(opt['max'])]
            insts = [{'id': f"{r['core']['file']}#{r['core'].get('pos')}[m={r['core']['m']},idx={r['core'].get('idx')}]:"
                            f"{','.join(map(str, r['prof']))}", 'sets': r['core']['sets'], 'm': r['core']['m'],
                      'vals': r['vals']} for r in recs]
        elif mode == 'suite':
            import glob
            ids = set(args)
            for fn in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
                d = json.load(open(fn))
                if 'kind' in d or (ids and d['id'] not in ids): continue
                if not int(opt.get('minn', 1)) <= len(d['sets']) <= int(opt.get('maxn', 16)): continue
                if P and not d.get('is_core', True): continue
                d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
                if d['m'] > (64 if WIDE else 32): continue          # the build's limit (--wide: m <= 64)
                insts.append(d)
        elif mode == 'inst':
            insts = json.load(open(args[0]))
        elif mode == 'ht':
            import c4_chain
            t = int(args[0]); sets, vals, m = c4_chain.build(t)
            insts = [{'id': f'H_{t}', 'sets': sets, 'vals': vals, 'm': m}]
        for d in insts: d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
        ckey = {'mode': mode, 'args': args, 'P': P, 'seed': seed, 'bt': bt, 'copts': copts,
                'every': opt.get('every'), 'max': opt.get('max')}
        done = load_ckpt(ck, ckey)
        if P:                     # random profiles of each instance's hypergraph, one unit per instance (or per job for ht)
            tasks = []
            reps = jobs if mode == 'ht' else 1
            for k, d in enumerate(insts):
                for r in range(reps):
                    key = {'pos': k * reps + r, 'inst': k, 'id': d['id']}
                    if json.dumps(key, sort_keys=True) in done: continue
                    tasks.append((key, d['sets'], d['m'], -(-P // reps), seed, 'all' if bt == 'all' else None, copts))
            fn = unit_certs
        else:
            C = int(opt.get('chunk', 2000))
            tasks = [({'chunk': i}, insts[i * C:(i + 1) * C], copts) for i in range(-(-len(insts) // C))]
            tasks = [t for t in tasks if json.dumps(t[0], sort_keys=True) not in done]
            fn = unit_list
        for kj, bl in done.items():
            for b in bl: merge(tot, b)
        print(f'# {mode} {" ".join(args)}: {len(insts)} instances, {len(tasks)} units to run, {len(done)} from the checkpoint'
              + (f'; {P} random profiles each, seed {seed}' if P else ''), flush=True)

        def onres(key, bl, secs):
            for b in bl:
                merge(tot, b)
                if P:
                    for d in b['D']:
                        ins = insts[key['inst']]
                        d['core'] = {'id': ins['id'], 'm': ins['m'], 'sets': ins['sets']}
                dump_write(dump, b['D'])
                if b['LC']['rcfail']: print(f"#   DL_RC FAILS: {key} block {b['tag']}: {b['LC']['rcfail']} states", flush=True)
                if b['LC']['keyfail']: print(f"#   KEY FORM FAILS: {key} block {b['tag']}: {b['LC']['keyfail']} states", flush=True)
                if b['LC']['chain']: print(f"#   chain states: {key} block {b['tag']}: {b['LC']['chain']}", flush=True)
            if 'progress' in opt: print(f'#   unit {key} done [{secs:.1f} s]', flush=True)
        run_units(fn, tasks, jobs, ck, ckey, onres)
        report(mode + (' ' + ' '.join(args) if args else ''), tot, time.time() - t0)
    print_tables(tot)
    if 'tables' in opt:
        json.dump({'command': 'python3 k4/dlrc_run.py ' + ' '.join(argv), 'src': os.path.basename(SRC), 'src_sha256': SHA,
                   'counters': {k: tot.get(k, 0) for k in KEYS + LKEYS + ['c_' + x for x in CKEYS]}, 'tab': tot.get('tab', {})},
                  open(opt['tables'], 'w'), indent=0, sort_keys=True)


if __name__ == '__main__':
    main()
