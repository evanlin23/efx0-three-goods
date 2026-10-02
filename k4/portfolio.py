"""The k = 4 deficit-descent portfolio: one pass over the data evaluates a lattice of DL statements (compute/k4-portfolio).
EVIDENCE only.

Why: DL2, DL_T, DL13, DL134 and DL_RT4 were tested one at a time and refuted in turn (ledger K4.DL2.*, K4.DL13.KEY).
Here every candidate of k4/portfolio_preds.py (single-step forms DL_R and key-graph forms) is evaluated on the same
states in one pass, and the output is a survival table with, for each survivor, the distribution of the smallest
repair (which move does the work).

Fast path (implementation (a)). k4/portfolio_dump.c (dlrt4.c's enumeration and deficit, copied verbatim) writes, for
every profile with f >= 1, omega >= 1 and a state, the WHOLE min-frozen class with every deficit; the predicates are
evaluated here in Python (k4/portfolio_preds.py computes N_i, NA and the frozen agents from the bases and the values).
dlrt4.c's own dumps are not used: they list the better states only at DL_RT4 failures (and at most 400), so they cannot
feed the portfolio; the profiles of those dumps are re-evaluated here instead (mode `dumps`). Since the class is
complete, there is no truncation, and def*(K) of every key K is the least deficit over all min-frozen P of key K
(the union of the profile's min-frozen states is the whole class by construction: portfolio_dump.c prints every P
that dlrt4.c's dfsP enumerates).
Reference (implementation (b)): k4/portfolio_ref.py, on main's k4/c4x_check.py enumeration (no portfolio_dump.c, no
dlrt4.c, no model.py) with separately written predicate tests; `python3 k4/portfolio_ref.py compare ...` checks that
both give the same verdict for every predicate at every state and key.

  python3 k4/portfolio.py certs FILE... [--sample=P] [--seed=S] [--cores=A:B] [--every=E] [--bt=all] [--fmin=F]
  python3 k4/portfolio.py inst FILE.json [FILE.json ...]      (JSON lists of {"id", "sets", "vals", "m"})
  python3 k4/portfolio.py suite
  python3 k4/portfolio.py dumps FILE.jsonl.gz ...            (the f >= 1 profiles of dlrt4.c / dl13.c / dl2.c D records)
  python3 k4/portfolio.py catalog FILE [--every=E]           (a k4/gap_run.py catalogue: records with core and vals)
  python3 k4/portfolio.py table                              (results/k4_portfolio/*.json -> TABLE.md)
  python3 k4/portfolio.py selftest                           (deficits of portfolio_dump.c = dlrt4.c's -s lines)
common: --name=LABEL (the dataset; writes results/k4_portfolio/LABEL.json, the aggregate, and LABEL_fails.jsonl.gz,
every failing state or key with its profile) --jobs=J --ckpt (resume from results/k4_portfolio/ckpt_LABEL.jsonl)
--chunk=C (profiles per unit in the list modes, default 300) --maxst=S (skip profiles with more than S states,
counted) --maxpairs=X (skip profiles with more than X (state, P) pairs, counted; not part of the checkpoint key)
--byf=A,B (also the smallest-repair shapes of these predicates by f)
--progress

The aggregate per dataset: profiles screened, dumped, states and keys with def* > 0 by f; per predicate the states
(keys) tested, the failures, the least margin (repairs at the worst state), the smallest-repair shapes "U|W|Z|Y"
(with "~" if NA changes); the verdict vectors (one per state / key, for the implications); per state f and the nearest
distance."""
import collections, glob, gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import portfolio_preds as PR

SRC = os.path.join(HERE, 'portfolio_dump.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()
OUT = os.path.join(HERE, '..', 'results', 'k4_portfolio')
INF = 999999
HARDK = 40            # profiles kept per aggregate as hunt seeds (least RC3, RC_W1, K3b margins)


def binpath(wide=False):
    return os.path.join(tempfile.gettempdir(), 'k4_pdump_' + SHA[:16] + ('_w' if wide else ''))


def build(wide=False):
    b = binpath(wide)
    if not os.path.exists(b):
        subprocess.run(['gcc', '-O2'] + (['-DWIDE'] if wide else []) + ['-o', b + '.tmp', SRC], check=True)
        os.replace(b + '.tmp', b)
    return b


def block(sets, m, doms, tag, P, profs=None):
    out = [f"{len(sets)} {m} {tag}"]
    out += [f"{len(S)} {' '.join(map(str, S))}" for S in sets]
    out.append(' '.join(str(len(D)) for D in doms))
    for S, D in zip(sets, doms):
        out += [' '.join(str(d[g]) for g in S) for d in D]
    if profs is None: out.append(str(P))
    else: out.append(str(-len(profs))); out += [' '.join(map(str, p)) for p in profs]
    return '\n'.join(out) + '\n'


def bt_dom(D, S):
    """the big-top types of a 4-good agent's domain (as k4/dlrt4_run.py --bt)"""
    if len(S) != 4: return D
    return [d for d in D if (lambda w: w[3] > w[2] + w[1])(sorted(d[g] for g in S))]


def run_c(inp, opts, wide=False):
    """portfolio_dump.c on the blocks -> (A records, K counters per block)"""
    r = subprocess.run([build(wide)] + opts, input=inp, capture_output=True, text=True)
    if r.returncode: raise RuntimeError(r.stderr)
    A, Ks = [], []
    for l in r.stdout.splitlines():
        if l.startswith('A '):
            a, b, c = l.split(' | ')
            w = a.split(); tag = int(w[1]); prof = [int(x) for x in w[2:]]
            f, om, npp = map(int, b.split())
            cls = []
            for it in c.split():
                bs, d = it.split(':')
                cls.append((tuple(int(x) for x in bs.split('.')), int(d)))
            assert len(cls) == npp
            A.append({'tag': tag, 'prof': prof, 'f': f, 'omega': om, 'cls': cls})
        elif l.startswith('K '):
            w = l.split(); Ks.append({'tag': int(w[1]), **{k: int(x) for k, x in zip(w[2::2], w[3::2])}})
    return A, Ks


def masks_to_lists(B): return [[g for g in range(64) if b >> g & 1] for b in B]


def new_agg():
    return {'profiles': 0, 'om1': 0, 'dumped': 0, 'skipped_big': 0, 'states': 0, 'keys_pos': 0, 'by_f': {}, 'dist': {},
            'single': {name: {'tested': 0, 'fail': 0, 'margin': None, 'small': {}, 'smallest_fail': None}
                       for name in PR.SNAMES},
            'keyg': {name: {'tested': 0, 'fail': 0, 'margin': None, 'small': {}, 'smallest_fail': None}
                     for name in PR.KNAMES},
            'svec': {}, 'kvec': {}, 'hard': [], 'secs': 0.0}


def _inc(d, k, c=1): d[k] = d.get(k, 0) + c


def fail_key(rec):
    """order of 'smallest failure': n, m, f, def, then the id"""
    return (rec['n'], rec['m'], rec['f'], rec['def'] if rec['def'] is not None else INF, rec['id'])


def nearest(pd, p):
    """the least |ch| of any min-frozen Q with a smaller deficit (dl2.c's k(P)); None if none"""
    ds = [pd.move(p, q).nch for q in range(len(pd.P)) if pd.d[q] < pd.d[p]]
    return min(ds) if ds else None


MAXPAIRS = None       # --maxpairs: skip (and count) profiles with more than this many (state, min-frozen P) pairs
BYF = []              # --byf=A,B: also count the smallest-repair shapes of these predicates by f (agg['small_f'])


def eval_into(agg, fails, ident, sets, vals, m, cls, maxst=None):
    """evaluate one profile (the class cls from portfolio_dump.c) into the aggregate; failures appended to `fails`"""
    nst = sum(1 for _, d in cls if d > 0)
    if (maxst is not None and nst > maxst) or (MAXPAIRS is not None and nst * len(cls) > MAXPAIRS):
        agg['skipped_big'] += 1; return None
    pd = PR.ProfData(sets, vals, m, [(B, (INF if d >= INF else d)) for B, d in cls])
    r = PR.evaluate(pd)
    agg['dumped'] += 1; agg['states'] += r['states']; agg['keys_pos'] += r['keys_pos']
    fk = str(pd.f)
    bf = agg['by_f'].setdefault(fk, {'profiles': 0, 'states': 0, 'keys_pos': 0})
    bf['profiles'] += 1; bf['states'] += r['states']; bf['keys_pos'] += r['keys_pos']
    st = [p for p in range(len(pd.P)) if pd.d[p] > 0]
    for p in st: _inc(agg['dist'], '%d|%s' % (pd.f, nearest(pd, p)))
    n = len(sets)
    base = {'id': ident, 'n': n, 'm': m, 'f': pd.f, 'sets': sets, 'vals': vals}
    for kind, names in (('single', PR.SNAMES), ('keyg', PR.KNAMES)):
        for name in names:
            e, a = r[kind][name], agg[kind][name]
            a['tested'] += len(e['nrep'])
            a['fail'] += len(e['fail'])
            if e['margin'] is not None and (a['margin'] is None or e['margin'] < a['margin']): a['margin'] = e['margin']
            for s, c in e['small'].items(): _inc(a['small'], s, c)
            if name in BYF:
                for s, c in e['small'].items(): _inc(agg.setdefault('small_f', {}).setdefault(name, {}).setdefault(fk, {}), s, c)
            for x in e['fail']:
                if kind == 'single':
                    rec = dict(base, pred=name, kind=kind, B=masks_to_lists(pd.P[x]), **{'def': pd.d[x] if pd.d[x] != INF else None},
                               k=nearest(pd, x), frozen=[i for i in range(n) if pd.F[x] >> i & 1])
                else:
                    NA, fz = x
                    rec = dict(base, pred=name, kind=kind, NA=[g for g in range(64) if NA >> g & 1],
                               frozen={str(i): [g for g in range(64) if b >> g & 1] for i, b in enumerate(fz) if b >= 0},
                               **{'def': r['dstar'][x] if r['dstar'][x] != INF else None},
                               nstates=sum(1 for q in range(len(pd.P)) if pd.key[q] == x))
                fails.append(rec)
                if a['smallest_fail'] is None or fail_key(rec) < fail_key(a['smallest_fail']):
                    a['smallest_fail'] = {k: rec[k] for k in rec}
    # the hardest profiles for the hunt seeds: least RC3 / RC_W1 / K3b margins, larger f first
    hk = (r['single']['RC3']['margin'], r['single']['RC_W1']['margin'], r['keyg']['K3b']['margin'], -(pd.f or 0))
    agg['hard'].append({'score': [x if x is not None else 99 for x in hk], 'id': ident, 'sets': sets, 'vals': vals, 'm': m, 'f': pd.f})
    agg['hard'] = sorted(agg['hard'], key=lambda h: h['score'])[:HARDK]
    # verdict vectors
    for i in range(len(st)):
        v = ''.join('1' if r['single'][nm]['nrep'][i] else '0' for nm in PR.SNAMES)
        _inc(agg['svec'], v)
    for i in range(r['keys_pos']):
        v = ''.join('1' if r['keyg'][nm]['nrep'][i] else '0' for nm in PR.KNAMES)
        _inc(agg['kvec'], v)
    return r


def merge(tot, a):
    for k in ('profiles', 'om1', 'dumped', 'skipped_big', 'states', 'keys_pos', 'secs'): tot[k] += a[k]
    for fk, b in a['by_f'].items():
        t = tot['by_f'].setdefault(fk, {'profiles': 0, 'states': 0, 'keys_pos': 0})
        for k in b: t[k] += b[k]
    for k, c in a['dist'].items(): _inc(tot['dist'], k, c)
    for kind in ('single', 'keyg'):
        for name, e in a[kind].items():
            t = tot[kind].setdefault(name, {'tested': 0, 'fail': 0, 'margin': None, 'small': {}, 'smallest_fail': None})
            t['tested'] += e['tested']; t['fail'] += e['fail']
            if e['margin'] is not None and (t['margin'] is None or e['margin'] < t['margin']): t['margin'] = e['margin']
            for s, c in e['small'].items(): _inc(t['small'], s, c)
            if e['smallest_fail'] is not None and (t['smallest_fail'] is None or fail_key(e['smallest_fail']) < fail_key(t['smallest_fail'])):
                t['smallest_fail'] = e['smallest_fail']
    for k in ('svec', 'kvec'):
        for v, c in a[k].items(): _inc(tot[k], v, c)
    for nm, byf in a.get('small_f', {}).items():
        for fk, sm in byf.items():
            for s, c in sm.items(): _inc(tot.setdefault('small_f', {}).setdefault(nm, {}).setdefault(fk, {}), s, c)
    tot['hard'] = sorted(tot.get('hard', []) + a.get('hard', []), key=lambda h: h['score'])[:HARDK]


# ---------------- units ----------------
def unit_certs(task):
    """one core: P random profiles (dlrt4.c's stream, so --seed S draws dlrt4_run.py's profiles), or all (P = 0)"""
    key, fname, sets, m, P, seed, bt, fmin, maxst = task
    t0 = time.time()
    doms = check4.core_domains(sets, m, False)
    if bt == 'all': doms = [bt_dom(D, S) for D, S in zip(doms, sets)]
    A, Ks = run_c(block(sets, m, doms, key['pos'], P), [f'-S{seed}', f'-f{fmin}'], wide=m > 32)
    agg, fails = new_agg(), []
    for K in Ks: agg['profiles'] += K['prof']; agg['om1'] += K['om1']
    for a in A:
        vals = [[doms[i][p][g] for g in S] for i, (S, p) in enumerate(zip(sets, a['prof']))]
        ident = f"{fname}#{key['pos']}:{','.join(map(str, a['prof']))}" + ('[bt]' if bt == 'all' else '')
        eval_into(agg, fails, ident, sets, vals, m, a['cls'], maxst)
    agg['secs'] = time.time() - t0
    return key, agg, fails


def unit_list(task):
    """a list of single profiles {"id", "sets", "vals", "m"}"""
    key, insts, fmin, maxst = task
    t0 = time.time()
    agg, fails = new_agg(), []
    by_wide = collections.defaultdict(list)
    for k, d in enumerate(insts): by_wide[d['m'] > 32].append(k)
    for wide, ks in by_wide.items():
        inp = ''.join(block(insts[k]['sets'], insts[k]['m'], [[dict(zip(S, V))] for S, V in zip(insts[k]['sets'], insts[k]['vals'])],
                            k, 0) for k in ks)
        A, Ks = run_c(inp, [f'-f{fmin}'], wide=wide)
        for K in Ks: agg['profiles'] += K['prof']; agg['om1'] += K['om1']
        for a in A:
            d = insts[a['tag']]
            eval_into(agg, fails, d['id'], d['sets'], d['vals'], d['m'], a['cls'], maxst)
    agg['secs'] = time.time() - t0
    return key, agg, fails


def load_ckpt(ck, ckey):
    done = {}
    if ck and os.path.exists(ck):
        for l in open(ck):
            try: d = json.loads(l)
            except ValueError: continue
            if d['ckey'] == ckey: done[json.dumps(d['key'], sort_keys=True)] = d['agg']
    return done


def dump_profiles(files):
    """the distinct f >= 1 profiles of D-record dumps (dlrt4.c, dl13.c, dl2.c; records with core and vals)"""
    seen, out = set(), []
    for fn in files:
        try:
            fh = gzip.open(fn, 'rt')
            for l in fh:
                try: r = json.loads(l)
                except ValueError: continue
                if 'core' not in r or 'vals' not in r or not isinstance(r['core'], dict) or 'sets' not in r['core']: continue
                if r.get('f', 1) < 1: continue
                c = r['core']
                k = json.dumps([c['sets'], r['vals']])
                if k in seen: continue
                seen.add(k)
                m = c.get('m') or 1 + max(g for S in c['sets'] for g in S)
                out.append({'id': '%s#%s:%s' % (c.get('file', c.get('id', os.path.basename(fn))), c.get('pos', c.get('idx', '?')),
                                                ','.join(map(str, r.get('prof') or []))),
                            'sets': c['sets'], 'vals': r['vals'], 'm': m})
        except (OSError, EOFError) as ex:
            print('# could not read all of', fn, ex, flush=True)
    return out


def summarize(name, tot, out=sys.stdout):
    pr = lambda *a: print(*a, file=out, flush=True)
    pr(f"{name}: profiles {tot['profiles']} (omega >= 1: {tot['om1']}), evaluated (f >= 1 with a state) {tot['dumped']}"
       f" (skipped as too large: {tot['skipped_big']}); states {tot['states']}, keys with def* > 0 {tot['keys_pos']}; "
       f"by f: {json.dumps(tot['by_f'], sort_keys=True)}; {tot['secs']:.0f} s CPU")
    pr('  nearest distance of the states (f|k: count): ' + ', '.join('%s: %d' % kv for kv in sorted(tot['dist'].items())))
    for kind, names in (('single', PR.SNAMES), ('keyg', PR.KNAMES)):
        for nm in names:
            e = tot[kind][nm]
            sm = ', '.join('%s %d' % kv for kv in sorted(e['small'].items(), key=lambda x: -x[1])[:8])
            sf = e['smallest_fail']
            sfs = '' if not sf else (f" | smallest failure n={sf['n']} m={sf['m']} f={sf['f']} def={sf['def']} {sf['id']} "
                                     + (f"B={sf['B']}" if kind == 'single' else f"NA={sf['NA']} frozen={sf['frozen']}"))
            pr(f"  {kind:6s} {nm:10s} tested {e['tested']:8d} FAILS {e['fail']:6d} margin {e['margin']} | smallest repairs: {sm}{sfs}")


def main():
    argv = sys.argv[1:]
    mode = argv[0]
    args = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    if mode == 'table': return table()
    if mode == 'selftest': return selftest()
    name = opt.get('name', mode)
    os.makedirs(OUT, exist_ok=True)
    print('# command: python3 k4/portfolio.py ' + ' '.join(argv), flush=True)
    print(f'# portfolio_dump.c sha256 {SHA}; portfolio_preds.py sha256 '
          f'{hashlib.sha256(open(os.path.join(HERE, "portfolio_preds.py"), "rb").read()).hexdigest()}', flush=True)
    build(); build(True)
    jobs = int(opt.get('jobs', os.cpu_count() or 2)); fmin = int(opt.get('fmin', 1))
    maxst = int(opt['maxst']) if 'maxst' in opt else None
    global MAXPAIRS, BYF
    if 'maxpairs' in opt: MAXPAIRS = int(opt['maxpairs'])
    if 'byf' in opt: BYF = opt['byf'].split(',')
    ck = os.path.join(OUT, f'ckpt_{name}.jsonl') if 'ckpt' in opt else None
    fails_path = os.path.join(OUT, f'{name}_fails.jsonl.gz')
    P, seed = int(opt.get('sample', 0)), int(opt.get('seed', 1))
    ckey = {'mode': mode, 'args': args, 'P': P, 'seed': seed, 'bt': opt.get('bt'), 'cores': opt.get('cores'),
            'every': opt.get('every'), 'fmin': fmin, 'maxst': maxst}
    done = load_ckpt(ck, ckey)
    tot = new_agg()
    for a in done.values(): merge(tot, a)
    if not done and os.path.exists(fails_path): os.remove(fails_path)
    tasks = []
    if mode == 'certs':
        for f in args:
            cores = json.load(gzip.open(f, 'rt'))['cores']
            lo, hi = 0, len(cores)
            if 'cores' in opt: a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
            for k in range(lo, hi, int(opt.get('every', 1))):
                key = {'file': os.path.basename(f), 'pos': k}
                if json.dumps(key, sort_keys=True) in done: continue
                tasks.append((key, os.path.basename(f), cores[k]['sets'], cores[k]['m'], P, seed, opt.get('bt'), fmin, maxst))
        fn = unit_certs
    else:
        if mode == 'inst':
            insts = [d for fn_ in args for d in json.load(open(fn_))]
        elif mode == 'suite':
            insts = []
            for fn_ in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
                d = json.load(open(fn_))
                if 'kind' in d or 'vals' not in d: continue
                d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
                if d['m'] > 64 or len(d['sets']) > 16: continue
                insts.append({'id': d['id'] + ('' if d.get('is_core', True) else '[not a core]'), 'sets': d['sets'],
                              'vals': d['vals'], 'm': d['m']})
        elif mode == 'dumps':
            insts = dump_profiles(args)
        elif mode == 'catalog':
            recs = json.load(gzip.open(args[0], 'rt'))['records'][::int(opt.get('every', 1))]
            insts = [{'id': f"{r['core']['file']}#{r['core'].get('pos')}:{','.join(map(str, r['prof']))}", 'sets': r['core']['sets'],
                      'm': r['core']['m'], 'vals': r['vals']} for r in recs]
        else: raise SystemExit('unknown mode ' + mode)
        for d in insts: d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
        C = int(opt.get('chunk', 300))
        for i in range(-(-len(insts) // C)):
            key = {'chunk': i}
            if json.dumps(key, sort_keys=True) in done: continue
            tasks.append((key, insts[i * C:(i + 1) * C], fmin, maxst))
        fn = unit_list
        print(f'# {mode}: {len(insts)} profiles', flush=True)
    print(f'# {len(tasks)} units to run, {len(done)} from the checkpoint; jobs {jobs}', flush=True)
    t0 = time.time()
    with Pool(jobs) as pool:
        for key, agg, fails in pool.imap_unordered(fn, tasks):
            merge(tot, agg)
            if fails:
                with gzip.open(fails_path, 'at') as fo:
                    for r in fails: fo.write(json.dumps(r, separators=(',', ':')) + '\n')
            if ck:
                with open(ck, 'a') as fo: fo.write(json.dumps({'ckey': ckey, 'key': key, 'agg': agg}) + '\n')
            if 'progress' in opt or any(agg['single'][nm]['fail'] for nm in PR.SNAMES[1:]):
                newf = {nm: agg[k][nm]['fail'] for k, names in (('single', PR.SNAMES), ('keyg', PR.KNAMES)) for nm in names
                        if agg[k][nm]['fail']}
                print(f"#   unit {key}: dumped {agg['dumped']} states {agg['states']} fails {newf} [{agg['secs']:.1f} s; "
                      f"{time.time() - t0:.0f} s wall]", flush=True)
    summarize(name, tot)
    json.dump({'name': name, 'command': 'python3 k4/portfolio.py ' + ' '.join(argv), 'portfolio_dump_sha256': SHA,
               'agg': tot}, open(os.path.join(OUT, f'{name}.json'), 'w'), sort_keys=True)
    print(f'# wrote {os.path.join("results/k4_portfolio", name + ".json")}; {time.time() - t0:.0f} s wall', flush=True)


def selftest():
    """portfolio_dump.c's deficits of the states (def > 0) = dlrt4.c's -s lines, on the 10 failing n = 5 profiles, the
    suite (n <= 6) and random n = 3, 4 profiles"""
    import dlrt4_run as DR
    DR.build()
    insts = [d for f in ('n5b_failures_inst.json', 'n5c_fail_inst.json') for d in json.load(open(os.path.join(HERE, '..', 'results', 'k4_rt4', f)))]
    for fn_ in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
        d = json.load(open(fn_))
        if 'kind' in d or 'vals' not in d or len(d['sets']) > 6: continue
        d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
        if d['m'] <= 32: insts.append(d)
    blocks = [block(d['sets'], d['m'], [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])], k, 0) for k, d in enumerate(insts)]
    for f, P in (('k4_certs_3.json.gz', 40), ('k4_certs_4_pure.json.gz', 40), ('k4_certs_4_n4_3.json.gz', 20)):
        cores = json.load(gzip.open(os.path.join(HERE, '..', 'results', f), 'rt'))['cores']
        for k, c in enumerate(cores[::3]):
            blocks.append(block(c['sets'], c['m'], check4.core_domains(c['sets'], c['m'], False), 1000 + len(blocks), P))
    inp = ''.join(blocks)
    A, _ = run_c(inp, ['-S7', '-f0'])
    mine = collections.Counter()
    for a in A:
        for B, d in a['cls']:
            if d > 0: mine[(a['tag'], tuple(a['prof']), B, d)] += 1
    theirs = collections.Counter()
    for b in DR.run_blocks(inp, ['-v', '-s', '-r0', '-o0', '-S7']):
        for V, S in zip(b['V'], b['S']):
            for s in S:
                B = tuple(int(x) for x in s[1:1 + len(V) - 5])
                theirs[(b['tag'], tuple(V[1:1 + len(B)]), B, int(s[1 + len(B)]))] += 1
    ok = mine == theirs
    print(f'selftest: {len(blocks)} blocks, {sum(mine.values())} states (def > 0) from portfolio_dump.c, '
          f'{sum(theirs.values())} from dlrt4.c -s; identical: {ok}', flush=True)
    if not ok:
        print('only portfolio_dump.c:', list((mine - theirs).items())[:5]); print('only dlrt4.c:', list((theirs - mine).items())[:5])
    return 0 if ok else 1


ORDER_NOTE = ('Rows are ordered from the strongest statement to the weakest along the lattice: RC3 < RC_W1 < RC < '
              '{RC_noneed, RC_Yfree, RC_Yany} < RC_U0 < NA1 < NAbal = NAall; RC3 < NA3 < NAall; NA1 < U1Z1; D2 < D3 < D4; '
              'NA3 < D3; FR3 apart; RT4 (control) is not inside RC3 (its rotations and T4 moves may change more than three '
              'agents); RC3_noT4 < RC3 is a probe (is T4 needed?). Key-graph: K3b_noT4 (probe) < K3b < K3 < K2 < {K2_noneed, K2_Yany} < K4 < K5; K4 < KU1; K1 (control).')


def esc(x): return str(x).replace('|', '\\|')


def table():
    """results/k4_portfolio/*.json -> results/k4_portfolio/TABLE.md"""
    aggs, byf = [], None
    for fn in sorted(glob.glob(os.path.join(OUT, '*.json'))):
        d = json.load(open(fn))
        if not isinstance(d, dict): continue
        if 'agg' in d and not d['name'].endswith('_byf'): aggs.append(d)
        elif 'agg' in d: byf = d
    order = ['suite', 'validate10', 'dumps']
    aggs.sort(key=lambda d: (order.index(d['name']) if d['name'] in order else 99, d['name']))
    L = ['# The portfolio survival table (compute/k4-portfolio)', '',
         'Made by `python3 k4/portfolio.py table` from `results/k4_portfolio/*.json`. EVIDENCE only. Each cell: failures / '
         'states tested (single-step forms) or failures / keys with def* > 0 tested (key-graph forms). ' + ORDER_NOTE, '']
    L.append('## Datasets'); L.append('')
    L.append('| dataset | command | profiles | evaluated profiles | states | keys def* > 0 | states by f |')
    L.append('|---|---|---:|---:|---:|---:|---|')
    tot = new_agg()
    for d in aggs:
        a = d['agg']; merge(tot, a)
        L.append(f"| {d['name']} | `{esc(d['command'].replace('python3 k4/portfolio.py ', ''))}` | {a['profiles']:,} | {a['dumped']:,} | "
                 f"{a['states']:,} | {a['keys_pos']:,} | {', '.join('f=%s: %d' % (k, v['states']) for k, v in sorted(a['by_f'].items()))} |")
    L.append(f"| **all** (summed over the datasets; validate10 and part of suite repeat profiles of dumps) | | {tot['profiles']:,} | {tot['dumped']:,} | {tot['states']:,} | {tot['keys_pos']:,} | "
             f"{', '.join('f=%s: %d' % (k, v['states']) for k, v in sorted(tot['by_f'].items()))} |")
    L.append('')
    for kind, reg, title in (('single', PR.SINGLE, 'Single-step forms DL_R'), ('keyg', PR.KEYG, 'Key-graph forms')):
        L.append(f'## {title}'); L.append('')
        L.append('| predicate | definition | ' + ' | '.join(d['name'] for d in aggs) + ' | **all** | least margin |')
        L.append('|---|---|' + '---:|' * (len(aggs) + 2))
        for nm, doc, _ in reg:
            cells = []
            for d in aggs:
                e = d['agg'][kind].get(nm)
                cells.append('-' if not e else (f"**{e['fail']}**/{e['tested']}" if e['fail'] else f"0/{e['tested']}"))
            e = tot[kind][nm]
            L.append(f"| {nm} | {esc(doc)} | " + ' | '.join(cells) + f" | {'**%d**' % e['fail'] if e['fail'] else 0}/{e['tested']} | {e['margin']} |")
        L.append('')
        L.append('Smallest failure and smallest-repair distribution (all datasets):'); L.append('')
        L.append('| predicate | smallest failure (n, m, f, def; id) | smallest repairs "U\\|W\\|Z\\|Y" (count) |')
        L.append('|---|---|---|')
        for nm, doc, _ in reg:
            e = tot[kind][nm]; sf = e['smallest_fail']
            sfs = '-' if not sf else (f"n={sf['n']}, m={sf['m']}, f={sf['f']}, def={sf['def']}; `{sf['id']}`; "
                                      + (f"P={sf['B']}" if kind == 'single' else f"NA={sf['NA']}, frozen={sf['frozen']}"))
            sm = ', '.join('%s: %d' % (esc(k), c) for k, c in sorted(e['small'].items(), key=lambda x: -x[1])[:10])
            L.append(f'| {nm} | {esc(sfs)} | {sm} |')
        L.append('')
    if byf:
        L.append(f'## Smallest repairs by f ({byf["name"]}: the dumps dataset again, with `--byf`; '
                 f'{byf["agg"]["states"]:,} states, {byf["agg"]["keys_pos"]:,} keys)')
        L.append('')
        for nm, per in sorted(byf['agg'].get('small_f', {}).items()):
            shapes = sorted({sh for sm in per.values() for sh in sm}, key=lambda sh: -sum(sm.get(sh, 0) for sm in per.values()))
            L.append(f'{nm}:'); L.append('')
            L.append('| f | ' + ' | '.join(esc(sh) for sh in shapes) + ' |'); L.append('|---|' + '---:|' * len(shapes))
            for fk in sorted(per, key=int):
                L.append(f'| {fk} | ' + ' | '.join(f'{per[fk].get(sh, 0):,}' for sh in shapes) + ' |')
            L.append('')
    # implications observed
    L.append('## Implications observed (all datasets)'); L.append('')
    for kind, names, vk in (('single', PR.SNAMES, 'svec'), ('keyg', PR.KNAMES, 'kvec')):
        vec = tot[vk]
        L.append(f'{"States" if kind == "single" else "Keys"}: {sum(vec.values()):,}; distinct verdict vectors {len(vec)}. '
                 'A row "A => B" is listed when B holds wherever A holds on the data although A\'s relation is not inside B\'s '
                 '(non-trivial implications), and "A =/=> B" with the number of states where A holds and B fails.')
        L.append('')
        allhold = [nm for j, nm in enumerate(names) if all(v[j] == '1' for v in vec)]
        L.append(f'- hold at every {"state" if kind == "single" else "key"} (so every implication into them is observed '
                 f'trivially): {", ".join(allhold) or "none"}')
        rows = []
        for i, a in enumerate(names):
            for j, b in enumerate(names):
                if i == j or b in allhold: continue
                ab = sum(c for v, c in vec.items() if v[i] == '1' and v[j] == '0')
                a1 = sum(c for v, c in vec.items() if v[i] == '1')
                if a1 and ab == 0 and not structural(kind, a, b): rows.append(f'- {a} => {b} (on {a1:,})')
                elif ab and structural(kind, a, b): rows.append(f'- INCONSISTENT: {a} holds and {b} fails at {ab}')
        L += rows or ['- none beyond the structural inclusions']
        L.append('')
        L.append('Verdict vectors (order ' + ', '.join(names) + '):')
        L.append('')
        for v, c in sorted(vec.items(), key=lambda x: -x[1]): L.append(f'- `{v}`: {c:,}')
        L.append('')
    open(os.path.join(OUT, 'TABLE.md'), 'w').write('\n'.join(L) + '\n')
    print('wrote results/k4_portfolio/TABLE.md')


STRUCT = {  # relation inclusions R_a inside R_b (so DL_{R_a} => DL_{R_b} trivially)
    'single': {'RC3_noT4': ['RC3'], 'RC3': ['RC_W1', 'NA3', 'D3'], 'NA3': ['NAall', 'D3'],
               'RT4': ['RC_W1', 'RC', 'RC_noneed', 'RC_Yfree', 'RC_Yany', 'RC_U0', 'NA1', 'NAbal', 'NAall'],
               'RC_W1': ['RC', 'RC_noneed', 'RC_Yfree', 'RC_Yany', 'RC_U0', 'NA1', 'NAbal', 'NAall'],
               'RC': ['RC_noneed', 'RC_Yfree', 'RC_Yany', 'RC_U0', 'NA1', 'NAbal', 'NAall'],
               'RC_noneed': ['NA1', 'NAbal', 'NAall'], 'RC_Yfree': ['NA1', 'NAbal', 'NAall'], 'RC_Yany': ['NA1', 'NAbal', 'NAall'],
               'RC_U0': ['NA1', 'NAbal', 'NAall'], 'NA1': ['NAbal', 'NAall', 'U1Z1'], 'NAbal': ['NAall'], 'NAall': ['NAbal'],
               'D2': ['D3', 'D4'], 'D3': ['D4']},
    'keyg': {'K3b_noT4': ['K3b'], 'K3b': ['K3'], 'K1': ['K3', 'K2', 'K2_noneed', 'K2_Yany', 'K4', 'K5', 'KU1'], 'K3': ['K2', 'K2_noneed', 'K2_Yany', 'K4', 'K5', 'KU1'],
             'K2': ['K2_noneed', 'K2_Yany', 'K4', 'K5', 'KU1'], 'K2_noneed': ['K4', 'K5', 'KU1'], 'K2_Yany': ['K4', 'K5', 'KU1'],
             'K4': ['K5', 'KU1']}}


def structural(kind, a, b):
    """is R_a inside R_b by definition (transitively)?"""
    seen, st = set(), [a]
    while st:
        x = st.pop()
        for y in STRUCT[kind].get(x, []):
            if y == b: return True
            if y not in seen: seen.add(y); st.append(y)
    return False


if __name__ == '__main__':
    sys.exit(main())
