"""Driver for k4/lemmam_portfolio.c: a portfolio of candidate strengthenings of Lemma M (k4/rulef.md §4, §6) evaluated
in one pass over the data, with exchange partners, (G2) and C40 counts (workstream compute/k4-m-portfolio; EVIDENCE).

k4/lemmam_portfolio.c #includes k4/rulef.c unchanged, so the classes K0 and K1 are rulef.c's (Lemma K deficit <= 0 at
the state after Phase 1(tau_a) and upgrades, before or after one rotation). See the C header for every candidate.

Usage:
  lemmam_portfolio.py FILE [FILE ...] [--jobs=J] [--n4=K] [--m=M] [--first=N] [--every=K] [--checkpoint=CK]
                      [--out=JSON] [--label=L] [C options: -Y1 -N1 -S50 -X7 -f3 -O0]
      every core of the certificate files (exhaustive by default, -SN random profiles per core); --every=K takes every
      K-th core only
  lemmam_portfolio.py --profiles=FILE [...]       single profiles (JSON lines {"sets", "vals"} or tagged sets=/vals=)
  lemmam_portfolio.py --H=1,2,3 --perms=K         the cores H_t of k4/c4.md §7 and K seeded relabelings each (k4/adaptive_H.py)
  lemmam_portfolio.py --suite                     the counterexample suite k4/suite/instances (k = 4 cores only)
--checkpoint: each core's (or profile's) result is appended to CK and skipped when rerun with the same key (input
label, options, source hash): every run is resumable. --out: the aggregated counters and failures as JSON (for
k4/lemmam_table.py). The log (stdout) starts with the command and the source hash."""
import gzip, hashlib, json, os, re, subprocess, sys, tempfile, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as AR

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'lemmam_portfolio.c')
RULEF = os.path.join(HERE, 'rulef.c')
SHA = hashlib.sha256(open(SRC, 'rb').read() + open(RULEF, 'rb').read()).hexdigest()[:16]
RULEF_SHA = hashlib.sha256(open(RULEF, 'rb').read()).hexdigest()
BIN = os.environ.get('LEMMAM_BIN') or os.path.join(tempfile.gettempdir(), 'k4_lemmam_' + SHA)
CANDS = ["M", "M_K0", "M_bt", "M_bt1", "M_nobt", "M_gap", "M_gapn", "M_kappa", "M_def1", "M_12", "M_K0KR", "M_K0KRo",
         "M_bt12", "M_nobt0", "M_btK0KR"]
VARS = [k + p for p in ('N', 'E', '0') for k in ('x1', 'x2', 'x3', 'x3b', 'x3c', 'x4')]
FAILTAGS = ('PFAIL', 'XFAIL', 'C40VIOL', 'M1VIOL', 'KRVIOL', 'KROVIOL', 'HFAIL', 'HTIGHT', 'HDONE')


def build():
    if not os.path.exists(BIN):
        tmp = BIN + f'.tmp{os.getpid()}'
        subprocess.run(['gcc', '-O2', '-o', tmp, SRC, '-lm'], check=True, cwd=HERE)
        os.replace(tmp, BIN)


def run(task):
    key, inp, opts = task
    t0 = time.time()
    p = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if p.returncode: raise RuntimeError(f'{key}: exit {p.returncode}: ' + p.stdout[-500:] + p.stderr[-1000:])
    lines = p.stdout.strip().split('\n')
    pm = [l for l in lines if l.startswith('PM ')]
    lv = [l for l in lines if l.startswith('PLEAVES')]
    fl = [l for l in lines if l.startswith(FAILTAGS)]
    return key, pm, lv, fl, time.time() - t0


def parse_pm(line):
    t = line.split()[1:]
    d = {}; key = None
    for x in t:
        if x.lstrip('-').isdigit(): d.setdefault(key, []).append(int(x))
        else: key = x
    return d


def add(a, b):
    for k, v in b.items():
        a[k] = [x + y for x, y in zip(a[k], v)] if k in a else list(v)
    return a


def prof_key(line):
    """size key of a failure line: (n, m, total goods, max value, sum of values)"""
    n = int(re.search(r' n=(\d+)', line).group(1)); m = int(re.search(r' m=(\d+)', line).group(1))
    sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
    vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
    return (n, m, sum(len(S) for S in sets), max(max(v) for v in vals), sum(sum(v) for v in vals))


def fail_name(line):
    if line.startswith('PFAIL'): return re.search(r'cand=(\S+)', line).group(1)
    if line.startswith('XFAIL'): return 'partner:' + re.search(r'var=(\S+)', line).group(1)
    if line.startswith('HFAIL'):
        v = re.search(r'var=(\S+)', line)
        return ('partner:' + v.group(1)) if v else re.search(r'cand=(\S+)', line).group(1)
    return line.split()[0]


def summarize(tot, fails, label, out=None, extra=None):
    """print the aggregated table; return the JSON-able summary"""
    S = {'label': label, 'sha': SHA, 'rulef_sha256': RULEF_SHA, 'counters': tot, 'smallest': {}, 'nfail_lines': {}}
    if extra: S.update(extra)
    for l in fails:
        if l.startswith(('HTIGHT', 'HDONE')): continue
        nm = fail_name(l)
        S['nfail_lines'][nm] = S['nfail_lines'].get(nm, 0) + 1
        k = prof_key(l)
        if nm not in S['smallest'] or tuple(S['smallest'][nm]['key']) > k:
            S['smallest'][nm] = {'key': list(k), 'line': l}
    T = tot.get('tot', [0])[0]
    print(f"== {label}: profiles {T}, exactly one first agent in K0 or K1: {tot.get('tightM', [0])[0]}, "
          f"no agent in K0 but some in K1: {tot.get('K1only', [0])[0]}")
    print(f"  {'candidate':10s} {'applicable':>16s} {'fails':>14s} {'tight':>14s} {'only':>14s}")
    for c in CANDS:
        if c in tot:
            a, f, t, o = tot[c]
            print(f"  {c:10s} {a:16d} {f:14d} {t:14d} {o:14d}")
    print(f"  {'partner':10s} {'pairs (a not W)':>16s} {'undefined':>14s} {'some works':>14s} {'all work':>14s} {'none works':>12s}")
    for v in VARS:
        if v in tot:
            p, u, an, al = tot[v]
            print(f"  {v:10s} {p:16d} {u:14d} {an:14d} {al:14d} {p - u - an:12d}")
    for k in ('g2', 'g2W', 'g2bad', 'c40', 'c40notW', 'profc40', 'profnoc40', 'm1notK0', 'krnotW', 'kronotW', 'wK0', 'wK1', 'wK1KR', 'wK1noKR'):
        if k in tot: print(f"  {k} {tot[k][0]}", end='')
    print()
    for nm in sorted(S['smallest']):
        print(f"  smallest {nm} ({S['nfail_lines'][nm]} lines): {S['smallest'][nm]['line'][:900]}")
    if out:
        json.dump(S, open(out, 'w'), indent=1)
        with open(os.path.splitext(out)[0] + '.fails.txt', 'w') as ff:
            for l in fails:
                if not l.startswith(('HTIGHT', 'HDONE')): ff.write(l + '\n')
    sys.stdout.flush()
    return S


def load_ck(ck, keyprefix):
    done = {}
    if ck and os.path.exists(ck):
        for line in open(ck):
            try: o = json.loads(line)
            except json.JSONDecodeError: continue
            if o['key'].startswith(keyprefix): done[o['key']] = o
    return done


def drive(tasks, jobs, ck, label, out, extra=None):
    """tasks: list of (key, input, opts); runs the missing ones, aggregates everything"""
    done = load_ck(ck, '')
    todo = [t for t in tasks if t[0] not in done]
    if len(todo) < len(tasks): print(f"# resuming: {len(tasks) - len(todo)} of {len(tasks)} tasks from {ck}", flush=True)
    fc = open(ck, 'a') if ck else None
    tot = {}; fails = []; leaves = 0; cpu = 0.0
    for t in tasks:
        if t[0] in done:
            o = done[t[0]]
            for l in o['pm']: add(tot, parse_pm(l))
            fails += o['fl']; cpu += o.get('time', 0)
    t0 = time.time(); nd = 0
    with Pool(jobs) as pool:
        for key, pm, lv, fl, dt in pool.imap_unordered(run, todo):
            nd += 1; cpu += dt
            for l in pm: add(tot, parse_pm(l))
            fails += fl
            for l in fl:
                if l.startswith(('HFAIL',)) or (l.startswith('PFAIL') and 'cand=M ' in l): print('!!', l[:1500], flush=True)
            if fc: fc.write(json.dumps({'key': key, 'pm': pm, 'lv': lv, 'fl': fl, 'time': dt}) + '\n'); fc.flush()
            if nd % max(1, len(todo) // 20) == 0:
                print(f"# {nd}/{len(todo)} tasks, {time.time() - t0:.0f}s", flush=True)
    if fc: fc.close()
    ex = dict(extra or {}); ex['tasks'] = len(tasks); ex['cpu_seconds'] = round(cpu, 1); ex['wall_seconds_this_run'] = round(time.time() - t0, 1)
    return summarize(tot, fails, label, out, ex)


def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    opt = lambda name, dflt=None: next((a.split('=', 1)[1] for a in args if a.startswith(f'--{name}=')), dflt)
    jobs = int(opt('jobs', os.cpu_count()))
    copts = [a for a in args if a.startswith('-') and not a.startswith('--')]
    ck = opt('checkpoint'); out = opt('out'); label = opt('label', ' '.join(files) or 'profiles')
    build()
    print('#', 'lemmam_portfolio.py', ' '.join(args), '# source sha', SHA, '# rulef.c sha256', RULEF_SHA, flush=True)
    okey = ' '.join(copts) + ' ' + SHA
    tasks = []
    if opt('profiles'):
        P = AR.load_profiles(opt('profiles'))
        for i, (s, v) in enumerate(P):
            tasks.append((f"prof {os.path.basename(opt('profiles'))} {i} {okey}", AR.encode_profile(s, v), copts + ['-T1']))
    elif opt('H'):
        import random
        import adaptive_H as AH
        perms = int(opt('perms', 0)); seed = int(opt('seed', 1))
        for t in [int(x) for x in opt('H').split(',')]:
            sets, vals, m = AH.build(t)
            rng = random.Random(seed * 1000 + t)
            for p in range(perms + 1):
                S, V, pa = (sets, vals, None) if p == 0 else AH.relabel(sets, vals, m, rng)
                tasks.append((f"H {t} {p} {seed} {okey}", AR.encode_profile(S, V), copts + ['-T1']))
    elif '--suite' in args:
        sys.path.insert(0, os.path.join(HERE, 'suite'))
        import model as SM
        import glob
        for f in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
            d = json.load(open(f))
            if 'kind' in d: continue
            I = SM.Inst(d['sets'], d['vals'], d.get('m'))
            if I.core_violations() or len(d['sets']) > 40: continue
            tasks.append((f"suite {d['id']} {okey}", AR.encode_profile(d['sets'], d['vals']), copts + ['-T1']))
    else:
        every = int(opt('every', 1)); n4 = opt('n4'); monly = opt('m'); first = opt('first')
        for f in files:
            data = json.load(gzip.open(f, 'rt'))
            idxs = [i for i, c in enumerate(data['cores']) if (monly is None or c['m'] == int(monly))
                    and (n4 is None or sum(len(S) == 4 for S in c['sets']) == int(n4))]
            if first: idxs = idxs[:int(first)]
            idxs = idxs[::every]
            for i in idxs:
                c = data['cores'][i]
                tasks.append((f"{os.path.basename(f)} {i} {okey}", AR.encode_core(c['sets'], c['m']), copts))
    print(f"# {len(tasks)} tasks, {jobs} workers", flush=True)
    t0 = time.time()
    drive(tasks, jobs, ck, label, out, {'options': copts, 'args': args})
    print(f"# done in {time.time() - t0:.0f}s", flush=True)


if __name__ == '__main__':
    main()
