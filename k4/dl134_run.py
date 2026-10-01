"""Driver for k4/dl134.c (compute/k4-dl134): Conjecture DL134 (DL13 of k4/dl2.md §3 with the frozen permutations T4
added; k4/dl134.c's header) on data. EVIDENCE only. A copy of k4/dl13_run.py (unchanged) that builds k4/dl134.c.

  python3 k4/dl134_run.py certs FILE... [--sample=P] [--seed=S] [--cores=A:B] [--bt=all|one] [--jobs=J] [--ckpt=PATH]
  python3 k4/dl134_run.py catalog FILE [--every=E] [--max=N] [--chunk=C] [--jobs=J] [--ckpt=PATH]
  python3 k4/dl134_run.py suite [IDS...] [--maxn=N] [--sample=P] [--seed=S] [--bt=...]
  python3 k4/dl134_run.py inst FILE.json [--sample=P] [--seed=S]       (a JSON list of {"id", "sets", "vals"|"m"})
  python3 k4/dl134_run.py ht T [--sample=P] [--seed=S] [--wide]           (H_T of k4/c4_chain.py)
  python3 k4/dl134_run.py tsv FILE.tsv... [--out=PATH.tsv] [--jobs=J]    (the failing profiles of results/k4_dl13)
common: [--dump=PATH.jsonl.gz] [--tables=PATH.json] [--rt=R] [--ro=O] [--rq=Q] [--progress]

certs: every strict profile (check4.core_domains: one integer representative per strict balanced type, with the
private-pair condition) of every core of a certificate file results/k4_certs_*.json.gz, or P random ones per core
(dl134.c's generator, seeded by --seed and the core's position). --bt=all restricts every 4-good agent to its big-top
types (top > second + third: 48 of the 288 types); --bt=one runs, per core, one block per 4-good agent with only that
agent restricted (profiles with two big-top agents are then counted in two blocks).
catalog: the profiles of a catalogue of k4/gap_run.py (records with "core" and "vals"), every E-th record, in chunks
of C records (default 2000), one dl134.c process per chunk.
suite: the complete instances of k4/suite/instances (their profile), or --sample=P random strict profiles of each
instance's hypergraph (cores only).
tsv: the (core, profile) lines of results/k4_dl13/n4_failures_*.tsv (written by results/k4_dl13/n4_failures_list.py).
Every profile is run with -s; besides the usual counters (over all states of those profiles), each listed failing state
(column "bases") is looked up and its R_134 branch, the T4 cycle types of its improving moves and its distances are
printed per core and, with --out, written one line per state.

Each unit (a core, a block of a core, a chunk of a catalogue) is one dl134.c process; --ckpt appends one JSON line per
finished unit and skips the units already in it (resume after a restart; the dump is written before the checkpoint
line, one gzip member per unit). --dump writes dl134.c's "D" records (every f >= 1 state where DL134 fails, every Q-th
f >= 1 state repaired by T4 only for --rq=Q (default 1: all), the first f >= 1 state of each (signature, branch) cell
per process, every R-th state without T1 for --rt=R (default 50), every O-th other state for --ro=O (default 0: none),
the first 5 f = 0 states where R_134 fails) with the core and the values added. --tables writes the merged counters and
tables as JSON.
Prints the command, the SHA-256 of dl134.c, per file dl2.c's counters (dl134.c computes them with dl2.c's code), DL13's
counters (dl13.c's "L" line) and DL134's ("M" line), then the tables (dl134.c's header defines them)."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

SRC = os.path.join(HERE, 'dl134.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()
WIDE = '--wide' in sys.argv
BIGPP = next((a.split('=', 1)[1] for a in sys.argv if a.startswith('--bigpp=')), None)   # test builds only
BIN = os.path.join(tempfile.gettempdir(), 'k4_dl134_' + SHA[:16] + ('_w' if WIDE else '') + (f'_b{BIGPP}' if BIGPP else ''))
KEYS = ('prof om1 small kstar0 kstar1 kstar2 kstar3 kstar4 kstarinf kstarn kiso ktrap pos pd1 pd2 pd3 pd4 pdinf piso '
        'ptrap pmpos pm3 maxmin').split()
LKEYS = 'st0 st1 fail0 fail1 t1only t3only both t3p t3h t3hOnly anom r13dnone r13d1 r13d2 r13d3'.split()
MKEYS = 'fail0 fail1 t1 t3 t4 t4only t4only2 t4onlyL t4sw rdnone rd1 rd2 rd3 rd4'.split()
# the names of the counters in the totals: dl13.c's "L" line (R_13) with fail0 / fail1 renamed, and the "M" line (R_134)
LNAME = dict((k, k) for k in LKEYS); LNAME.update(fail0='fail13_0', fail1='fail13_1')
CKEYS = [LNAME[k] for k in LKEYS] + MKEYS


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
    """dl134.c output -> list of blocks {tag, K, L, M, tab, D, V, S}"""
    blocks, curb = [], {'D': [], 'V': [], 'S': []}
    for l in stdout.splitlines():
        if l.startswith('K '):
            w = l.split(); curb['tag'] = int(w[1])
            curb['K'] = {k: int(x) for k, x in zip(w[2::2], w[3::2])}
            curb['tab'] = {}
            blocks.append(curb)
            curb = {'D': [], 'V': [], 'S': []}
        elif l.startswith('L '):
            w = l.split(); blocks[-1]['L'] = {k: int(x) for k, x in zip(w[2::2], w[3::2])}
        elif l.startswith('M '):
            w = l.split(); blocks[-1]['M'] = {k: int(x) for k, x in zip(w[2::2], w[3::2])}
        elif l[:2] in ('B ', 'G ', 'Y ', 'Q '):
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
        if 'fail' in d: b['X'] = listed_states(d, b['S'][0] if b['S'] else [])
        b['S'] = b['V'] = None
    return key, bl, time.time() - t0


SFIELDS = 'def dist r13d rd t1 t3p t3h t4 t1m t3m t4m dT1 dT3 dT4 pm'.split()
CYCNAME = ["2", "3", "4", "2+2", "5", "3+2", "6", "4+2", "3+3", "2+2+2", "7", "5+2", "4+3", "3+2+2", "8", "6+2", "5+3",
           "4+4", "4+2+2", "3+3+2", "2+2+2+2", "other"]                     # dl134.c's CYCNAME


def sline(w, n):
    """an "S" line of dl134.c (split, without the "S") -> dict"""
    r = {'f': int(w[0]), 'B': [sorted(g for g in range(64) if int(b) >> g & 1) for b in w[1:1 + n]]}
    r.update(zip(SFIELDS, map(int, w[1 + n:1 + n + len(SFIELDS)])))
    r['sig'] = w[-1]
    br = [b for b, k in (('T1', 't1'), ('T3p', 't3p'), ('T3h', 't3h'), ('T4', 't4')) if r[k]]
    r['branch'] = '+'.join(br) or 'none'
    r['t4types'] = [c for i, c in enumerate(CYCNAME) if r['t4m'] >> i & 1]
    return r


def listed_states(d, S):
    """tsv mode: the dl134.c record of every failing state listed for this profile"""
    n = len(d['sets'])
    byB = {}
    for w in S:
        r = sline(w, n); byB[json.dumps(r['B'])] = r
    out = []
    for B in d['fail']:
        r = byB.get(json.dumps([sorted(x) for x in B]))
        rec = dict(d['src'], B=B, found=r is not None)
        if r: rec.update({k: r[k] for k in ('f', 'def', 'dist', 'r13d', 'rd', 'branch', 't4types', 'dT4', 'sig')})
        out.append(rec)
    return out


def merge(tot, b):
    for k in KEYS:
        if k == 'maxmin':
            if b['K']['om1']: tot[k] = max(tot.get(k, -10 ** 9), b['K'][k])
        else: tot[k] = tot.get(k, 0) + b['K'][k]
    for k in LKEYS: tot[LNAME[k]] = tot.get(LNAME[k], 0) + b['L'][k]
    for k in MKEYS: tot[k] = tot.get(k, 0) + b['M'][k]
    for key, c in b['tab'].items(): tot.setdefault('tab', {})[key] = tot.setdefault('tab', {}).get(key, 0) + c


def merge_tot(tot, ftot):
    for k in KEYS + CKEYS:
        if k not in ftot: continue
        if k == 'maxmin': tot[k] = max(tot.get(k, -10 ** 9), ftot[k])
        else: tot[k] = tot.get(k, 0) + ftot[k]
    for key, c in ftot.get('tab', {}).items(): tot.setdefault('tab', {})[key] = tot.setdefault('tab', {}).get(key, 0) + c


def report(name, tot, secs):
    K = {k: tot.get(k, 0) for k in KEYS + CKEYS}
    print(f"{name}: profiles {K['prof']}, omega >= 1: {K['om1']}; k* = 0: {K['kstar0']}, 1: {K['kstar1']}, "
          f"2: {K['kstar2']}, 3: {K['kstar3']}, >= 4: {K['kstar4']}, inf: {K['kstarinf']}; P with def > 0: {K['pos']}, at "
          f"distance 1: {K['pd1']}, 2: {K['pd2']}, 3: {K['pd3']}, >= 4: {K['pd4']}, inf: {K['pdinf']}; Pareto-maximal: "
          f"{K['pmpos']}; largest least deficit {K['maxmin'] if K['om1'] else '-'}", flush=True)
    print(f"  DL13 (dl13.c's counters): states (def > 0) with f = 0: {K['st0']} (R_13 fails at {K['fail13_0']}), with "
          f"f >= 1: {K['st1']}; DL13 fails at {K['fail13_1']} of the f >= 1 states; T1 only {K['t1only']}, T3 only "
          f"{K['t3only']} (of which T3 with a helper only {K['t3hOnly']}), both {K['both']}; with a plain T3 move "
          f"{K['t3p']}, with a helper T3 move {K['t3h']}; nearest R_13 improvement at distance 1 / 2 / 3: {K['r13d1']} / "
          f"{K['r13d2']} / {K['r13d3']}; anomalies {K['anom']}", flush=True)
    print(f"  DL134: R_134 fails at {K['fail0']} of the f = 0 states; DL134 FAILS at {K['fail1']} of the {K['st1']} f >= 1 "
          f"states; f >= 1 states with an improving T1 move {K['t1']}, T3 move {K['t3']}, T4 move {K['t4']} (a 2-swap "
          f"{K['t4sw']}); repaired by T4 only {K['t4only']} (= the DL13 failures repaired; with a 2-swap {K['t4only2']}, "
          f"longer cycles only {K['t4onlyL']}); nearest R_134 improvement at distance 1 / 2 / 3 / >= 4 / none: "
          f"{K['rd1']} / {K['rd2']} / {K['rd3']} / {K['rd4']} / {K['rdnone']} [{secs:.0f} s]", flush=True)


def report_listed(listed, out=None):
    """tsv mode: the listed failing states, per core and in total; --out: one line per state"""
    import collections
    listed.sort(key=lambda r: (r['file'], r['pos'], r['prof'], r['B']))
    per = collections.OrderedDict()
    for r in listed: per.setdefault((r['file'], r['pos'], r['idx'], r['m']), []).append(r)

    def counts(rs):
        c = collections.Counter()
        for r in rs:
            c['states'] += 1
            if not r['found']: c['not found'] += 1; continue
            c['f >= 1'] += r['f'] >= 1
            c['DL13 holds (T1 or T3)'] += any(b in r['branch'] for b in ('T1', 'T3'))
            c['T4 repairs'] += 'T4' in r['branch']
            c['DL134 fails'] += r['branch'] == 'none'
            if 'T4' in r['branch']:
                c['a 2-swap repairs' if '2' in r['t4types'] else 'only longer cycles repair'] += 1
                c['nearest R_134 distance %d' % r['rd']] += 1
                c['T4 types ' + ','.join(r['t4types'])] += 1
        return c
    print(f'listed failing states (DL13 failures of results/k4_dl13): {len(listed)} in {len(per)} cores', flush=True)
    for (f, pos, idx, m), rs in per.items():
        c = counts(rs)
        print(f'  {f} pos {pos} (idx {idx}, m {m}): profiles {len(set(tuple(r["prof"]) for r in rs))}; '
              + ', '.join(f'{k} {v}' for k, v in sorted(c.items())), flush=True)
    c = counts(listed)
    print('  total: ' + ', '.join(f'{k} {v}' for k, v in sorted(c.items())), flush=True)
    if out:
        with open(out, 'w') as fo:
            fo.write('file\tpos\tidx\tm\tprofile\tbases\tfound\tf\tdef\tk\tr13dist\trdist\tbranch\tt4types\tdT4\tsig\n')
            for r in listed:
                fo.write('\t'.join(map(str, [r['file'], r['pos'], r['idx'], r['m'], ','.join(map(str, r['prof'])),
                                             json.dumps(r['B']), int(r['found'])] +
                                    ([r['f'], r['def'], r['dist'], r['r13d'], r['rd'], r['branch'],
                                      ','.join(r['t4types']) or '-', r['dT4'], r['sig']] if r['found'] else [''] * 9))) + '\n')


def print_tables(tot):
    tab = tot.get('tab', {})
    for t, title in (('B', 'f >= 1 states by f | signature | R_134 branch'),
                     ('G', 'f >= 1 states by f | nearest distance k | R_134 branch'),
                     ('Y', 'f >= 1 states by f | R_134 branch | move type available'),
                     ('Q', 'f >= 1 states repaired by T4 only, by f | k | T4 cycle types available')):
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
            if ck:
                with open(ck, 'a') as fo:
                    fo.write(json.dumps({'ckey': ckey, 'key': key, 'secs': round(secs, 1),
                                         'blocks': [dict({'K': b['K'], 'L': b['L'], 'M': b['M'], 'tab': b['tab']},
                                                         **({'X': b['X']} if 'X' in b else {})) for b in bl]}) + '\n')


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
    print('# command: python3 k4/dl134_run.py ' + ' '.join(argv), flush=True)
    print(f'# dl134.c sha256 {SHA}', flush=True)
    build()
    jobs = int(opt.get('jobs', 2)); ck = opt.get('ckpt'); dump = opt.get('dump')
    copts = [f"-r{int(opt.get('rt', 50))}", f"-o{int(opt.get('ro', 0))}", f"-q{int(opt.get('rq', 1))}"]
    P, seed = int(opt.get('sample', 0)), int(opt.get('seed', 1))
    bt = opt.get('bt')
    tot = {}
    t0 = time.time()
    if mode == 'certs':
        for f in args:
            cores = json.load(gzip.open(f, 'rt'))['cores']
            lo, hi = 0, len(cores)
            if 'cores' in opt: a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
            ckey = {'mode': 'certs', 'file': os.path.basename(f), 'P': P, 'seed': seed, 'bt': bt, 'copts': copts}
            done = load_ckpt(ck, ckey)
            ftot = {}
            tasks = []
            for k in range(lo, hi):
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
            print(f'# {os.path.basename(f)}: cores {lo}..{hi - 1}, {len(tasks)} units to run, {len(done)} from the '
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
                    if b['M']['fail1']: print(f"#   DL134 FAILS: core {key}: {b['M']['fail1']} states", flush=True)
                if 'progress' in opt:
                    L = bl[0]['L']; K = bl[0]['K']; Mc = bl[0]['M']
                    print(f"#   unit {key}: om1 {K['om1']} pos {K['pos']} st1 {L['st1']} fail13 {L['fail1']} fail134 "
                          f"{Mc['fail1']} t4only {Mc['t4only']} (2-swap {Mc['t4only2']}, longer {Mc['t4onlyL']}) t4 {Mc['t4']} "
                          f"[{secs:.1f} s]", flush=True)
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
                if len(d['sets']) > int(opt.get('maxn', 16)): continue
                if P and not d.get('is_core', True): continue
                d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
                insts.append(d)
        elif mode == 'inst':
            insts = json.load(open(args[0]))
        elif mode == 'tsv':
            import csv
            for fn in args:
                for row in csv.DictReader(open(fn), delimiter='\t'):
                    src = {'file': row['file'], 'pos': int(row['pos']), 'idx': int(row['idx']), 'm': int(row['m']),
                           'prof': [int(x) for x in row['profile'].split(',')]}
                    insts.append({'id': f"{row['file']}#{row['pos']}:{row['profile']}", 'sets': json.loads(row['sets']),
                                  'm': int(row['m']), 'vals': json.loads(row['vals']), 'fail': json.loads(row['bases']),
                                  'src': src})
            copts = copts + ['-s']
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
        listed = []                                              # tsv mode: the listed states
        for kj, bl in done.items():
            for b in bl: merge(tot, b); listed += b.get('X') or []
        print(f'# {mode} {" ".join(args)}: {len(insts)} instances, {len(tasks)} units to run, {len(done)} from the checkpoint'
              + (f'; {P} random profiles each, seed {seed}' if P else ''), flush=True)

        def onres(key, bl, secs):
            for b in bl:
                merge(tot, b); listed.extend(b.get('X') or [])
                if P:
                    for d in b['D']:
                        ins = insts[key['inst']]
                        d['core'] = {'id': ins['id'], 'm': ins['m'], 'sets': ins['sets']}
                dump_write(dump, b['D'])
                if b['M']['fail1']: print(f"#   DL134 FAILS: {key} block {b['tag']}: {b['M']['fail1']} states", flush=True)
            if 'progress' in opt: print(f'#   unit {key} done [{secs:.1f} s]', flush=True)
        run_units(fn, tasks, jobs, ck, ckey, onres)
        report(mode + (' ' + ' '.join(args) if args else ''), tot, time.time() - t0)
        if mode == 'tsv': report_listed(listed, opt.get('out'))
    print_tables(tot)
    if 'tables' in opt:
        json.dump({'command': 'python3 k4/dl134_run.py ' + ' '.join(argv), 'dl134_c_sha256': SHA,
                   'counters': {k: tot.get(k, 0) for k in KEYS + CKEYS}, 'tab': tot.get('tab', {})},
                  open(opt['tables'], 'w'), indent=0, sort_keys=True)


if __name__ == '__main__':
    main()
