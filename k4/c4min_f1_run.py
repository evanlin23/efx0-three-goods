#!/usr/bin/env python3
"""Driver for k4/c4min_f1.c: run it on every core of k = 4 certificate files (every strict profile, or a sample), in
parallel, and add up the counters of its RESULT line.

usage: python3 k4/c4min_f1_run.py FILE [FILE ...] [--jobs=4] [--split=K] [--rand=N] [--seed=S] [--only=I,J] [-L] [-x N]
  FILE: results/k4_certs_*.json.gz;  --split=K: split each core into K jobs by agent 0's type (default 4 for cores
  with >= 10^5 profiles);  --rand=N: N random profiles per core;  -L: lemma checks;  -x N: examples per job."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from c4min_run import core_input


def binary():
    src = open(os.path.join(HERE, 'c4min_f1.c'), 'rb').read()
    path = os.environ.get('C4MIN_F1_BIN') or os.path.join(tempfile.gettempdir(), 'c4min_f1_' + hashlib.sha1(src).hexdigest()[:12])
    if not os.path.exists(path):
        subprocess.run(['gcc', '-O2', '-march=native', '-Wall', '-o', path, os.path.join(HERE, 'c4min_f1.c')], check=True)
    return path


def run(args):
    b, inp, lo, hi, opts = args
    r = subprocess.run([b] + opts, input=f'{inp}\n{lo} {hi}\n', capture_output=True, text=True)
    if r.returncode not in (0,):
        return r.stdout + f'\nFAILED exit {r.returncode} {r.stderr}'
    return r.stdout


def main():
    files, opts, jobs, split, rand, seed, only = [], [], 4, None, 0, 1, None
    argv = sys.argv[1:]; i = 0
    while i < len(argv):
        a = argv[i]
        if a.startswith('--jobs='): jobs = int(a[7:])
        elif a.startswith('--split='): split = int(a[8:])
        elif a.startswith('--rand='): rand = int(a[7:])
        elif a.startswith('--seed='): seed = int(a[7:])
        elif a.startswith('--only='): only = set(int(x) for x in a[7:].split(','))
        elif a == '-x': opts += [a, argv[i + 1]]; i += 1
        elif a.startswith('-'): opts.append(a)
        else: files.append(a)
        i += 1
    b = binary()
    for f in files:
        t0 = time.time()
        data = json.load(gzip.open(f, 'rt'))
        cores = data['cores'] if isinstance(data, dict) else data
        tasks = []
        for ci, c in enumerate(cores):
            if only is not None and ci not in only: continue
            inp, sizes = core_input(c['n'], c['m'], c['sets'])
            prof = 1
            for s in sizes: prof *= s
            if rand:
                tasks.append((ci, (b, inp, 0, sizes[0], opts + ['-r', str(rand), '-S', str(seed * 1000003 + ci)])))
                continue
            k = min(split if split else (4 if prof >= 10**5 else 1), sizes[0])
            for p in range(k):
                tasks.append((ci, (b, inp, sizes[0] * p // k, sizes[0] * (p + 1) // k, opts)))
        tot, bad = {}, 0
        with ThreadPoolExecutor(jobs) as ex:
            for (ci, _), out in zip(tasks, ex.map(run, [t for _, t in tasks])):
                for line in out.splitlines():
                    if line.startswith(('EX', 'ASSERT', 'FAILED')):
                        print(f'core {ci}: {line}')
                        if not line.startswith('EX'): bad += 1
                    elif line.startswith('RESULT'):
                        w = line.split()
                        for k, v in zip(w[1::2], w[2::2]): tot[k] = tot.get(k, 0) + int(v)
        print(f'FILE {f} ({len(cores)} cores, {"rand=%d seed=%d" % (rand, seed) if rand else "every profile"}, {time.time() - t0:.0f} s)' + (f' {bad} JOBS FAILED' if bad else ''))
        print('  ' + ' '.join(f'{k} {v}' for k, v in tot.items()))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
