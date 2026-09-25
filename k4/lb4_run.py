"""Driver for k4/lb4.c: run LB4 on every strict (or, with --ties, every balanced weak) profile of every core in the
given certificate files (results/k4_certs_*.json.gz; only the core lists are used, loaded as in k4/check4.py), in
parallel over cores, and sum the per-core result lines.
Usage: lb4_run.py FILE [FILE ...] [--ties] [--jobs=J] [--show=N] [--m=M] [C options: -o0 -o1 -o2 -i1 -s -b -u0]"""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check4

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'lb4.c')
# the binary is named by a hash of the source, so two checkouts or an edited source never reuse a stale binary
BIN = os.environ.get('LB4_BIN') or os.path.join(
    tempfile.gettempdir(), 'k4_lb4_bin_' + hashlib.sha256(open(SRC, 'rb').read()).hexdigest()[:16])

def build():
    if 'LB4_BIN' in os.environ or not os.path.exists(BIN):
        subprocess.run(['gcc', '-O2', '-o', BIN, SRC], check=True, stderr=subprocess.DEVNULL)

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
    out, allocs, cur = [], [], []
    for line in p.stdout.strip().split('\n'):
        if line.startswith('A '): cur.append(list(map(int, line.split()[1:])))
        else: out.append(line); allocs.append(cur); cur = []
    if len(out) != len(recs): raise RuntimeError(f"{len(out)} result lines for {len(recs)} cores")
    return [(r, line, A) for r, line, A in zip(recs, out, allocs)], p.stderr

def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    ties = '--ties' in args
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    show = int(next((a.split('=')[1] for a in args if a.startswith('--show=')), 20))
    monly = next((int(a.split('=')[1]) for a in args if a.startswith('--m=')), None)
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')]
    certp = next((a.split('=', 1)[1] for a in args if a.startswith('--cert=')), None)
    if certp: opts.append('-a')
    build()
    print('#', 'lb4_run.py', ' '.join(args), flush=True)
    for f in files:
        t0 = time.time()
        data = json.load(gzip.open(f, 'rt'))
        if data.get('ties', False) != ties:     # the type domain must match the file's (a strict run of a ties file
            raise SystemExit(f"{f}: file has ties={data.get('ties', False)}, run has --ties={ties}")  # would mislabel)
        cores = [c for c in data['cores'] if monly is None or c['m'] == monly]
        chunk = max(1, min(8, len(cores) // (4 * jobs) or 1))
        tasks = [(cores[i:i + chunk], ties, opts) for i in range(0, len(cores), chunk)]
        tot = {}; bad = []; errs = []
        cert = [] if certp else None
        with Pool(jobs) as pool:
            for res, err in pool.imap_unordered(run, tasks):
                if err: errs.append(err)
                for r, line, A in res:
                    if cert is not None: cert.append({'m': r['m'], 'sets': r['sets'], 'allocs': A})
                    toks = line.split()
                    kv = dict(zip(toks[0:22:2], map(int, toks[1:22:2])))
                    for k, v in kv.items(): tot[k] = tot.get(k, 0) + v
                    for bs in toks[23:]:
                        s, c = bs.split(':'); tot['big' + s] = tot.get('big' + s, 0) + int(c)
                    if kv['fails'] or kv['rawfails']: bad.append((r['m'], r['sets'], kv['fails'], kv['rawfails']))
                    if '-i1' not in opts and '-i9' not in opts:        # every profile covered exactly once: leaf weights add up
                        expect = 1
                        for dom in check4.core_domains(r['sets'], r['m'], ties): expect *= len(dom)
                        if kv['total'] != expect: raise SystemExit(f"coverage mismatch {r['sets']}: {kv['total']} != {expect}")
        if certp:
            hdr = {k: v for k, v in data.items() if k != 'cores'}
            path = certp if len(files) == 1 else certp.replace('.json.gz', '_' + os.path.basename(f))
            cert.sort(key=lambda c: (c['m'], c['sets']))
            with gzip.open(path, 'wt') as fh: json.dump(dict(hdr, construction='LB4 ' + ' '.join(opts), cores=cert), fh)
            print(f"  certificate: {path} ({sum(len(c['allocs']) for c in cert)} allocations)")
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
