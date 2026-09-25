#!/usr/bin/env python3
"""Driver for k4/c4min.c: run it on every core of k = 4 certificate files (every strict profile, or a sample).

usage: python3 k4/c4min_run.py FILE [FILE ...] [--jobs=4] [--split=K] [--rand=N] [--seed=S] [--only=I,J] [c4min options]
  FILE: results/k4_certs_*.json.gz (the core lists of K4.R3-R5)
  --split=K  split each core into K jobs by agent 0's type (default: 4 for cores with >= 10^5 profiles)
  --rand=N   N random profiles per core instead of all (seeded by --seed and the core index)
  --only=I,J only the cores with these indices in the file
  other options are passed to c4min (-p, -x, -X, -D)
Prints the totals of c4min's counters per file, and the examples."""
import gzip, hashlib, json, os, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains   # the strict balanced types, as every k = 4 tool uses


def binary():
    src = open(os.path.join(HERE, 'c4min.c'), 'rb').read()
    path = os.environ.get('C4MIN_BIN') or os.path.join(tempfile.gettempdir(), 'c4min_' + hashlib.sha1(src).hexdigest()[:12])
    if not os.path.exists(path):
        subprocess.run(['gcc', '-O2', '-march=native', '-o', path, os.path.join(HERE, 'c4min.c')], check=True)
    return path


def core_input(n, m, sets):
    doms = core_domains(sets, m, False)
    lines = [f'{n} {m}']
    for S, D in zip(sets, doms):
        lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + f' {len(D)}')
        for vals in D: lines.append(' '.join(str(vals[g]) for g in S))
    return '\n'.join(lines), [len(D) for D in doms]


def run(args):
    b, inp, lo, hi, opts = args
    r = subprocess.run([b] + opts, input=f'{inp}\n{lo} {hi}\n', capture_output=True, text=True, check=True)
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
        elif a in ('-x', '-p', '-f'): opts += [a, argv[i + 1]]; i += 1
        elif a.startswith('-'): opts.append(a)
        else: files.append(a)
        i += 1
    b = binary()
    for f in files:
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
        tot, phis, order = {}, {}, []
        with ThreadPoolExecutor(jobs) as ex:
            for (ci, _), out in zip(tasks, ex.map(run, [t for _, t in tasks])):
                for line in out.splitlines():
                    if line.startswith(('EX', 'NONE', 'XCHECK', 'R0PROF')): print(f'core {ci}: {line}')
                    elif line.startswith('RESULT'):
                        w = line.split()
                        for k, v in zip(w[1::2], w[2::2]): tot[k] = tot.get(k, 0) + int(v)
                    elif line.startswith('PHI'):
                        w = line.split(); name = w[1]
                        if name not in phis: phis[name] = [0, 0, [0] * 7]; order.append(name)
                        phis[name][0] += int(w[3]); phis[name][1] += int(w[5])
                        if 'dist' in w:
                            k = w.index('dist')
                            for q in range(7): phis[name][2][q] += int(w[k + 1 + q])
        print(f'FILE {f} cores {len(set(ci for ci, _ in tasks))} ' + ' '.join(f'{k} {v}' for k, v in tot.items()))
        for name in order:
            e, s, dd = phis[name]
            print(f'  {name:40s} every-max fails {e:>10d}   some-max fails {s:>10d}' + (f'   dist {dd}' if any(dd) else ''))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
