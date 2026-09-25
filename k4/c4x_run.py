#!/usr/bin/env python3
"""Driver for k4/c4x.c: run it on every core of certificate files (every strict profile, or a sample).

usage: python3 k4/c4x_run.py FILE [FILE ...] [--jobs=4] [--split=K] [--rand=N] [--seed=S] [--only=I,J] [c4x options]
  FILE: results/k4_certs_*.json.gz (the core lists of K4.R3-R5) or results/certs_*.json.gz (k = 3 cores)
  --split=K  split each core into K jobs by agent 0's type (default: 4 for cores with >= 10^6 profiles)
  --rand=N   N random profiles per core instead of all (with --seed)
  --only=I,J only the cores with these indices in the file
  other options are passed to c4x (-w0, -x N, -a, -3)
Prints, per file, the totals of c4x's counters and the examples (-x)."""
import gzip, json, os, sys, subprocess, hashlib, tempfile, itertools
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains   # the strict balanced types (integer representatives), as every k = 4 tool uses

def binary():
    src = open(os.path.join(HERE, 'c4x.c'), 'rb').read()
    path = os.environ.get('C4X_BIN') or os.path.join(tempfile.gettempdir(), 'c4x_' + hashlib.sha1(src).hexdigest()[:12])
    if not os.path.exists(path):
        subprocess.run(['gcc', '-O2', '-march=native', '-o', path, os.path.join(HERE, 'c4x.c')], check=True)
    return path

def k3_domains(sets):
    """k = 3 cores: one strict balanced type per ranking of 3 goods (values 3 > 2 > ... with a < b + c)."""
    doms = []
    for S in sets:
        D = []
        for perm in itertools.permutations(range(3)):
            vals = {S[k]: (4, 3, 2)[perm[k]] for k in range(3)}
            D.append(vals)
        doms.append(D)
    return doms

def core_input(core, k3=False):
    n, m, sets = core['n'], core['m'], core['sets']
    doms = k3_domains(sets) if k3 else core_domains(sets, m, False)
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
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        a = argv[i]
        if a.startswith('--jobs='): jobs = int(a[7:])
        elif a.startswith('--split='): split = int(a[8:])
        elif a.startswith('--rand='): rand = int(a[7:])
        elif a.startswith('--seed='): seed = int(a[7:])
        elif a.startswith('--only='): only = set(int(x) for x in a[7:].split(','))
        elif a in ('-x', '-s', '-p'): opts += [a, argv[i + 1]] + ([argv[i + 2]] if a == '-s' else []); i += 1 + (a == '-s')
        elif a.startswith('-'): opts.append(a)
        else: files.append(a)
        i += 1
    b = binary()
    for f in files:
        data = json.load(gzip.open(f, 'rt'))
        cores = data['cores'] if isinstance(data, dict) else data
        k3 = os.path.basename(f).startswith('certs_')
        tasks = []
        for ci, core in enumerate(cores):
            if only is not None and ci not in only: continue
            if k3: core = {'n': core['n'], 'm': core['m'], 'sets': core['sets'] if 'sets' in core else core['edges']}
            inp, sizes = core_input(core, k3)
            prof = 1
            for s in sizes: prof *= s
            if rand:
                tasks.append((ci, (b, inp, 0, sizes[0], opts + ['-r', str(rand), '-S', str(seed * 1000003 + ci)])))
                continue
            k = split if split else (4 if prof >= 10**6 else 1)
            k = min(k, sizes[0])
            for p in range(k):
                lo, hi = sizes[0] * p // k, sizes[0] * (p + 1) // k
                tasks.append((ci, (b, inp, lo, hi, opts)))
        tot = {}
        phis = {}
        order = []
        with ThreadPoolExecutor(jobs) as ex:
            for (ci, _), out in zip(tasks, ex.map(run, [t for _, t in tasks])):
                for line in out.splitlines():
                    if line.startswith('EX') or line.startswith('OWN'): print(f'core {ci}: {line}')
                    elif line.startswith('RULESTATS'):
                        w = [int(x) for x in line.split()[1:]]
                        rs = tot.setdefault('_rs', [0] * len(w))
                        for q in range(len(w)): rs[q] += w[q]
                    elif line.startswith('TERMSTATS'):
                        w = [int(x) for x in line.split()[1:]]
                        ts = tot.setdefault('_ts', [0] * len(w))
                        for q in range(len(w)): ts[q] += w[q]
                    elif line.startswith('MOVES'):
                        w = line.split()
                        mv = tot.setdefault('_moves', [0] * 17)
                        nums = [int(x) for x in w[2:3] + w[4:12] + w[13:21]]
                        for q in range(17): mv[q] += nums[q]
                    elif line.startswith('RESULT'):
                        w = line.split()
                        for key, val in zip(w[1::2], w[2::2]):
                            if key == 'asg': continue
                            tot[key] = tot.get(key, 0) + int(val)
                    elif line.startswith('PHI'):
                        w = line.split()
                        name = w[1]
                        if name not in phis: phis[name] = [0, 0]; order.append(name)
                        phis[name][0] += int(w[3]); phis[name][1] += int(w[5])
        mv = tot.pop('_moves', None)
        ts = tot.pop('_ts', None)
        rs = tot.pop('_rs', None)
        if rs:
            names = ['maxima with omega>=1', 'w terminal', '... w invalid', 'w not terminal, 3-good terminal exists',
                     '... no 3-good terminal valid', 'no terminal', '... w invalid', '... frozen agents exist', 'w frozen',
                     'w frozen and some 3-good terminal invalid', 'Lemma Rw violated', 'Lemma Ew violated', 'P1', 'P2', 'w free and exposed by a 3-good terminal',
                     'w free, E_w nonempty', '.. frozen x, one good of B_w + one junk', '.. low(x) in B_w', '.. other',
                     '.. w terminal', '.. w valid', 'P1 at any maximum', 'C1 with E_w nonempty', 'case B2', 'case B2 with E_w nonempty', 'case B2, no 3-good terminal valid', 'case B2, no 3-good terminal']
            print('  RULESTATS (argmax of the first potential): ' + ', '.join(f'{a} {b}' for a, b in zip(names, rs)))
        print(f'FILE {f} cores {len(set(ci for ci, _ in tasks))} ' + ' '.join(f'{k} {v}' for k, v in tot.items()))
        if ts:
            names = ['terminals', '|E_t|=0', '|E_t|=1', '|E_t|>=2', '|E_t|>slots', 't invalid', 'E_t has free agent',
                     't reachable from E_t', 'two in E_t, same single end', 'P without terminal', 'x in E_t without end', 'P with omega>=1', 'P: no terminal with E_t empty', 'P: no valid terminal', 'P: exposure graph has a cycle',
                     'Lemma U violated', 'Lemma C violated', 'frozen agent without chain end', 'Lemma E violated',
                     '|Z_t| fits but t invalid', '|Z_t| too big but t valid']
            print('  TERMSTATS (Pareto-maxima): ' + ', '.join(f'{a} {b}' for a, b in zip(names, ts)))
        if mv: print(f'  MOVES: {mv[0]} min-frozen pre-allocations with positive deficit; nearest lower deficit at distance 1..7: {mv[2:9]} (none: {mv[1]}); nearest deficit <= 0: {mv[10:17]} (none: {mv[9]})')
        for name in order:
            print(f'  {name:32s} every-max fails {phis[name][0]:>12d}   some-max fails {phis[name][1]:>12d}')
        sys.stdout.flush()

if __name__ == '__main__':
    main()
