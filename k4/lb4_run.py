"""Driver for k4/lb4.c: run LB4 on every strict (or, with --ties, every balanced weak) profile of every core in the
given certificate files (results/k4_certs_*.json.gz; only the core lists are used, loaded as in k4/check4.py), in
parallel over cores, and sum the per-core result lines.
Usage: lb4_run.py FILE [FILE ...] [--ties] [--jobs=J] [--show=N] [--m=M] [C options: -o0 -o1 -o2 -i1 -s -b -u0]"""
import gzip, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check4

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.environ.get('LB4_BIN', os.path.join(tempfile.gettempdir(), 'k4_lb4_bin'))

def build():
    src = os.path.join(HERE, 'lb4.c')
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-o', BIN, src], check=True, stderr=subprocess.DEVNULL)

def encode(sets, m, ties):
    doms = check4.core_domains(sets, m, ties)
    out = [f"{len(sets)} {m}"]
    for S, dom in zip(sets, doms):
        out.append(f"{len(S)} {' '.join(map(str, S))} {len(dom)}")
        out += [' '.join(str(v[g]) for g in S) for v in dom]
    return '\n'.join(out) + '\n'

def run(task):
    recs, ties, opts = task
    inp = ''.join(encode(r['sets'], r['m'], ties) for r in recs)
    p = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if p.returncode: raise RuntimeError(p.stderr[-2000:])
    return [(r, line) for r, line in zip(recs, p.stdout.strip().split('\n'))], p.stderr

def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    ties = '--ties' in args
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    show = int(next((a.split('=')[1] for a in args if a.startswith('--show=')), 20))
    monly = next((int(a.split('=')[1]) for a in args if a.startswith('--m=')), None)
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')]
    build()
    print('#', 'lb4_run.py', ' '.join(args), flush=True)
    for f in files:
        t0 = time.time()
        data = json.load(gzip.open(f, 'rt'))
        cores = [c for c in data['cores'] if monly is None or c['m'] == monly]
        chunk = max(1, min(8, len(cores) // (4 * jobs) or 1))
        tasks = [(cores[i:i + chunk], ties, opts) for i in range(0, len(cores), chunk)]
        tot = {}; bad = []; errs = []
        with Pool(jobs) as pool:
            for res, err in pool.imap_unordered(run, tasks):
                if err: errs.append(err)
                for r, line in res:
                    toks = line.split()
                    kv = dict(zip(toks[0:18:2], map(int, toks[1:18:2])))
                    for k, v in kv.items(): tot[k] = tot.get(k, 0) + v
                    for bs in toks[19:]:
                        s, c = bs.split(':'); tot['big' + s] = tot.get('big' + s, 0) + int(c)
                    if kv['fails'] or kv['rawfails']: bad.append((r['m'], r['sets'], kv['fails'], kv['rawfails']))
                    if '-i1' not in opts:        # every profile covered exactly once: leaf weights add up
                        expect = 1
                        for dom in check4.core_domains(r['sets'], r['m'], ties): expect *= len(dom)
                        if kv['total'] != expect: raise SystemExit(f"coverage mismatch {r['sets']}: {kv['total']} != {expect}")
        print(f"{f}: {len(cores)} cores{' (ties)' if ties else ''}, {time.time() - t0:.0f}s")
        print('  ' + ' '.join(f"{k}={v}" for k, v in tot.items()))
        print(f"  cores with a failure: {len(bad)}")
        for b in sorted(bad)[:show]: print('   ', b)
        lines = [l for e in errs for l in e.strip().split('\n') if l]
        lines.sort(key=lambda l: (int(l.split('m=')[1].split()[0]), len(l)))
        for l in lines[:show]: print('  ', l)
        sys.stdout.flush()

if __name__ == '__main__':
    main()
