"""Driver for ls4.c: runs the k = 4 two-phase local search on the cores of certificate files.

Cores are read with the loader of k4/check4.py (the core lists of results/k4_certs_*.json.gz, complete by orbit
counting there) and profiles are enumerated from check4.core_domains (one integer representative per strict balanced
type, or per balanced weak type with --ties; an agent with two private goods p, q keeps only types with p + q < s + t).
Usage: ls4_run.py CERTFILE [...] [--sample=K] [--ties] [--x] [--v] [--jobs=J] [--r=POLICY] [--only=IDX]
"""
import gzip, json, os, subprocess, sys
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check4 import core_domains

HERE = os.path.dirname(os.path.abspath(__file__))

def build(src='ls4.c', exe='ls4'):
    os.makedirs(os.path.expanduser('~/.cache/ls4'), exist_ok=True)
    exe = os.path.join(os.path.expanduser('~/.cache/ls4'), exe)
    srcp = os.path.join(HERE, src)
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(srcp):
        subprocess.run(['gcc', '-O2', '-march=native', '-o', exe, srcp], check=True)
    return exe

def task_text(n, m, sets, ties, sample, seed):
    doms = core_domains(sets, m, ties)
    lines = [f"{n} {m}"] + [" ".join(map(str, [len(S)] + list(S))) for S in sets]
    for S, D in zip(sets, doms):
        lines.append(str(len(D)))
        lines += [" ".join(str(vals[g]) for g in S) for vals in D]
    lines.append(f"{1 if sample else 0} {sample or 0} {seed}")
    return "\n".join(lines) + "\n"

def work(args):
    exe, flags, n, m, sets, ties, sample, seed = args
    out = subprocess.run([exe] + flags, input=task_text(n, m, sets, ties, sample, seed), capture_output=True, text=True)
    if out.returncode != 0: return (sets, 'ERROR ' + out.stdout[-2000:] + out.stderr[-2000:])
    return (sets, out.stdout)

def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], '1') for a in sys.argv[1:] if a.startswith('--'))
    sample = int(opt.get('sample', 0)); ties = 'ties' in opt; jobs = int(opt.get('jobs', os.cpu_count()))
    src = opt.get('src', 'ls4.c'); exe = build(src, src[:-2])
    flags = (['-x'] if 'x' in opt else []) + (['-v'] if 'v' in opt else []) + (['-r', opt['r']] if 'r' in opt else [])
    flags += opt.get('flags', '').split()
    tasks = []
    for f in files:
        data = json.load(gzip.open(f, 'rt'))
        for k, rec in enumerate(data['cores']):
            if 'only' in opt and k != int(opt['only']): continue
            tasks.append((exe, flags, data['n'], rec['m'], rec['sets'], ties, sample, k + 1))
    tot = {}
    with Pool(jobs) as pool:
        for sets, out in pool.imap_unordered(work, tasks):
            if out.startswith('ERROR'): print('ERROR', sets, out); tot['error'] = tot.get('error', 0) + 1; continue
            for line in out.splitlines():
                if line.startswith('RESULT'):
                    kv = dict(x.split('=') for x in line.split()[1:])
                    for key, val in kv.items():
                        tot[key] = max(tot.get(key, 0), int(val)) if key == 'maxsteps' else tot.get(key, 0) + int(val)
                    if int(kv['fail']) or 'v' in opt: print(sets, line)
                elif 'v' in opt or 'FAIL' in line or 'NEEDS' in line or 'sets/values' in line: print(line)
    print('TOTAL', ' '.join(f"{k}={v}" for k, v in tot.items()), flush=True)

if __name__ == '__main__':
    main()
