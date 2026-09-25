"""Driver for gm4_explore.c (k4/gm4.md): level-sum maxima of k = 4 cores, from the cores of certificate files.

Cores come from results/k4_certs_*.json.gz (complete lists by the orbit count of k4/check4.py); strict type
representatives from k4/check4.py's core_domains (an agent with two private goods keeps only p + q < s + t).
Usage: gm4_run.py CERTFILE [...] [--sample=K] [--jobs=J] [--cores=A:B] [--only=IDX] [--maxm=M] [--minm=M]
                  [--defs='-DOUT=100'] [--prog=gm4_explore]
Prints the per-core RESULT lines' totals; with -DOUT the M lines too (for k4/gm4_analyze.py).
"""
import gzip, json, os, subprocess, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains

def build(defs, prog):
    d = os.path.expanduser('~/.cache/gm4'); os.makedirs(d, exist_ok=True)
    exe, src = os.path.join(d, prog + defs.replace(' ', '').replace('-D', '_').replace('=', '')), os.path.join(HERE, prog + '.c')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-march=native'] + defs.split() + ['-o', exe, src], check=True)
    return exe

def task_text(n, m, sets, sample, seed):
    doms = core_domains(sets, m, False)
    lines = [f"{n} {m}"] + [" ".join(map(str, [len(S)] + list(S))) for S in sets]
    for S, dom in zip(sets, doms):
        lines.append(str(len(dom)))
        lines += [" ".join(str(vals[g]) for g in S) for vals in dom]
    lines.append(f"{1 if sample else 0} {sample or 0} {seed}")
    return "\n".join(lines) + "\n"

def work(args):
    exe, n, m, sets, sample, seed = args
    out = subprocess.run([exe], input=task_text(n, m, sets, sample, seed), capture_output=True, text=True)
    return sets, m, out.returncode, out.stdout

def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], '1') for a in sys.argv[1:] if a.startswith('--'))
    sample, jobs = int(opt.get('sample', 0)), int(opt.get('jobs', os.cpu_count()))
    exe = build(opt.get('defs', ''), opt.get('prog', 'gm4_explore'))
    print('# ' + ' '.join(sys.argv), flush=True)
    tasks = []
    for f in files:
        data = json.load(gzip.open(f, 'rt'))
        recs = data['cores']
        lo, hi = map(int, opt['cores'].split(':')) if 'cores' in opt else (0, len(recs))
        for k, rec in enumerate(recs[lo:hi], lo):
            if 'only' in opt and k != int(opt['only']): continue
            if 'maxm' in opt and rec['m'] > int(opt['maxm']): continue
            if 'minm' in opt and rec['m'] < int(opt['minm']): continue
            tasks.append((exe, data['n'], rec['m'], rec['sets'], sample, k + 1))
    tot, ncores, bad, t0 = {}, 0, 0, time.time()
    with Pool(jobs) as pool:
        for sets, m, rc, out in pool.imap_unordered(work, tasks):
            ncores += 1
            for line in out.splitlines():
                if line.startswith('RESULT'):
                    for kv in line.split()[1:]:
                        k, v = kv.split('='); tot[k] = tot.get(k, 0) + int(v)
                elif line.split(' ')[0] in ('M', 'GMFAIL', 'H1FAIL', 'H0FAIL') or line.startswith('SKIP'):
                    print(f"{line} # m={m} sets={json.dumps(sets, separators=(',', ':'))}", flush=True)
            if rc not in (0, 1) or 'RESULT' not in out: bad += 1; print('BAD', sets, rc, out[-300:], flush=True)
    print(f"TOTAL cores={ncores} badcores={bad} " + ' '.join(f"{k}={v}" for k, v in tot.items()) + f" wall={time.time() - t0:.0f}s", flush=True)
    sys.exit(1 if bad or tot.get('noplace', 0) else 0)

if __name__ == '__main__':
    main()
