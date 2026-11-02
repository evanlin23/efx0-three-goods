"""Exhaustive check of conjecture DE4 over every strict profile of every core in a certificate file, with de4.c
(the C implementation). Usage: python3 k4/de4/run_exhaustive.py FILE [CHUNKS] > log
Each core is split into CHUNKS jobs (default 8), run on all CPUs; prints one line per core and a total."""
import os, subprocess, sys, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from de4lib import load_cores
from check import write_input, ROOT
HERE = os.path.dirname(os.path.abspath(__file__))
EXE = os.path.join(HERE, 'de4')

def job(args):
    ci, sets, ch, nch = args
    out = subprocess.run([EXE, str(ch), str(nch)], input=write_input(sets), capture_output=True, text=True).stdout
    return ci, out

if __name__ == '__main__':
    path = sys.argv[1]; nch = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    subprocess.run(['gcc', '-O2', '-w', '-o', EXE, os.path.join(HERE, 'de4.c')], check=True)
    cores = load_cores(path if os.path.exists(path) else os.path.join(ROOT, 'results', path))
    jobs = [(ci, s, ch, nch) for ci, s in enumerate(cores) for ch in range(nch)]
    per = {}; fails = []
    with mp.Pool(os.cpu_count()) as p:
        for ci, out in p.imap_unordered(job, jobs):
            for line in out.splitlines():
                if line.startswith('FAIL'): fails.append((ci, line))
                if line.startswith('profiles'):
                    w = line.split(); d = dict(zip(w[0::2], map(int, w[1::2])))
                    acc = per.setdefault(ci, {}); [acc.__setitem__(k, acc.get(k, 0) + v) for k, v in d.items()]
    tot = {}
    for ci in sorted(per):
        print('core', ci, cores[ci], ' '.join(f'{k} {v}' for k, v in per[ci].items()))
        for k, v in per[ci].items(): tot[k] = tot.get(k, 0) + v
    for f in fails[:20]: print('core', f[0], f[1])
    print('TOTAL', path, len(cores), 'cores;', ' '.join(f'{k} {v}' for k, v in tot.items()))
