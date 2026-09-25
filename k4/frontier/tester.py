"""Test a k = 4 construction against every certified core and every strict profile (tester.c does the work).

The construction is a C plugin (k4plugin.h; gcc -O2 -shared -fPIC -o my.so my.c), any program speaking the line
protocol below (--pipe), or the certificate itself (--oracle, a brute-force re-check of coverage). Cores come from the
certificate files results/k4_certs_<n>*.json.gz (ties files excluded), in order of n, then m, then index, so the
first failures reported are the smallest. Every output is checked with the raw EFX₀ definition and integer values;
--d2 also requires at most one bundle of more than 2 goods. A failure line (--fail-out, JSON) carries the core, the
values, the construction's allocation, the reason, and a certificate allocation that works for the same profile.

Usage: tester.py (--plugin=my.so [--plugin-arg=S] | --pipe='python3 mine.py' | --oracle) [--n=2,3] [--files=F,..]
                 [--d2] [--ties] [--sample=N --seed=S] [--max-fail=3] [--stop-after=K] [--jobs=J] [--fail-out=F]
  --n: which n to take from results/ (default 2,3: every profile of every core is feasible there; n = 4, 5 and 6 have
       up to 288^4, 288^5 and 288 * 6^5 profiles per core, use --sample); --files: explicit certificate files instead;
  --stop-after=K: stop each job after K failing cores.
Pipe protocol: the tester writes one line per instance, "n m" then for each agent "d g_1..g_d v_1..v_d" (goods
increasing; values positive integers, 0 on every other good); the program answers with one line of m owners.
Exit status 0 iff no failure. Speed: a simple C plugin runs all 51 n = 3 cores (≈ 3·10^8 profiles) in minutes."""
import glob, gzip, json, os, subprocess, sys, tempfile
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
BIN = os.path.join(HERE, 'tester')

def build():
    src = os.path.join(HERE, 'tester.c')
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < max(os.path.getmtime(src), os.path.getmtime(os.path.join(HERE, 'k4plugin.h'))):
        subprocess.run(['gcc', '-O2', '-o', BIN, src, '-ldl'], check=True)

def export(files, path):
    """Cores file for tester.c: 'C id n m src', one 'A d goods..' line per agent, 'K k', then k allocations."""
    recs = []
    for fn in files:
        data = json.load(gzip.open(fn, 'rt'))
        for r in data['cores']: recs.append((data['n'], r['m'], r.get('idx', 0), os.path.basename(fn), r))
    recs.sort(key=lambda x: x[:4])
    with open(path, 'w') as f:
        for n, m, idx, src, r in recs:
            f.write(f"C {src.replace('.json.gz', '')}:m{m}:{idx} {n} {m} {src}\n")
            for S in r['sets']: f.write(f"A {len(S)} {' '.join(map(str, sorted(S)))}\n")
            f.write(f"K {len(r['allocs'])}\n")
            for A in r['allocs']: f.write(' '.join(map(str, A)) + '\n')
    return len(recs)

def run(args):
    return subprocess.run([BIN] + args, capture_output=True, text=True)

def main():
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    if 'help' in opt or not any(k in opt for k in ('plugin', 'pipe', 'oracle')): print(__doc__); sys.exit(0 if 'help' in opt else 2)
    build()
    if 'files' in opt: files = opt['files'].split(',')
    else:
        files = []
        for n in opt.get('n', '2,3').split(','):
            files += sorted(f for f in glob.glob(os.path.join(ROOT, 'results', f'k4_certs_{n}*.json.gz')) if '_ties' not in f
                            and os.path.basename(f)[len(f'k4_certs_{n}')] in '._')
    tmp = tempfile.mkdtemp()
    cores = os.path.join(tmp, 'cores.txt')
    print(f"cores: {export(files, cores)} from {', '.join(os.path.basename(f) for f in files)}", flush=True)
    jobs = int(opt.get('jobs', os.cpu_count()))
    base = [f'--cores={cores}']
    for k in ('plugin', 'plugin-arg', 'pipe', 'sample', 'seed', 'max-fail', 'stop-after'):
        if k in opt: base.append(f'--{k}={opt[k]}')
    for k in ('oracle', 'd2', 'ties'):
        if k in opt: base.append(f'--{k}')
    argl = [base + [f'--part={p}/{jobs}', f'--fail-out={tmp}/fail{p}.jsonl'] for p in range(jobs)]
    with Pool(jobs) as pool: res = pool.map(run, argl)
    lines, bad = [], 0
    for r in res:
        if r.returncode not in (0, 1): print(r.stdout, r.stderr); sys.exit(2)
        lines += [l for l in r.stdout.splitlines() if l.startswith('core ') or l.startswith('  FAIL')]
    fails = []
    for p in range(jobs):
        fails += [json.loads(l) for l in open(f'{tmp}/fail{p}.jsonl')]
    fails.sort(key=lambda x: (x['n'], x['m'], x['core']))
    ncores = sum(l.startswith('core ') for l in lines)
    nprof = sum(int(l.split(': ')[1].split(' ')[0]) for l in lines if l.startswith('core '))
    failcores = sorted({(f['n'], f['m'], f['core']) for f in fails})
    print(res[0].stdout.splitlines()[0])
    print(f"SUMMARY: {ncores} cores, {nprof} profiles, {len(failcores)} cores with failures{' (EFX0 + D2)' if 'd2' in opt else ' (EFX0)'}")
    for f in fails[:int(opt.get('show', 10))]:
        print(f"  n={f['n']} m={f['m']} {f['core']}: sets {f['sets']} values {f['values']} alloc {f['alloc']}: {f['reason']}; "
              f"certificate allocation that works: {f['witness']}")
    if 'fail-out' in opt:
        with open(opt['fail-out'], 'w') as f:
            for x in fails: f.write(json.dumps(x) + '\n')
    sys.exit(1 if failcores else 0)

if __name__ == '__main__':
    main()
