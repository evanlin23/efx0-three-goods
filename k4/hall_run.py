#!/usr/bin/env python3
"""Driver for k4/hall.c (k4/hall.md): run it on every core of certificate files, every strict profile or a sample.

usage: python3 k4/hall_run.py FILE [FILE ...] [--jobs=4] [--rand=N] [--seed=S] [--only=I,J] [--split=K]
                              [--xcheck=C4X_BINARY] [hall options: -x N, -d, ...]
  FILE      results/k4_certs_*.json.gz (the core lists of K4.R3-R5; strict types from k4/check4.py)
  --rand=N  N random profiles per core (seeded by --seed and the core index)
  --xcheck  also run a c4x binary built from k4/c4x.c (branch proof/k4-c4x) with the per-profile summary line
            "X <types> valid V minfrozen F count C le0 Z least D" added after its deficit block (the patch is
            k4/hall_c4x_xcheck.py), and compare the summaries profile by profile.
Prints the summed counters of hall.c per file."""
import gzip, json, os, sys, subprocess, hashlib, tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains

def binary(name='hall.c', extra=()):
    src = open(os.path.join(HERE, name), 'rb').read()
    path = os.path.join(tempfile.gettempdir(), name.replace('.c', '') + '_' + hashlib.sha1(src + repr(extra).encode()).hexdigest()[:12])
    if not os.path.exists(path):
        subprocess.run(['gcc', '-O2', '-march=native', *extra, '-o', path, os.path.join(HERE, name)], check=True)
    return path

def core_input(core):
    n, m, sets = core['n'], core['m'], core['sets']
    doms = core_domains(sets, m, False)
    lines = [f'{n} {m}']
    for S, D in zip(sets, doms):
        lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + f' {len(D)}')
        for vals in D: lines.append(' '.join(str(vals[g]) for g in S))
    return '\n'.join(lines), [len(D) for D in doms]

def run(args):
    cmd, inp, lo, hi = args
    r = subprocess.run(cmd, input=f'{inp}\n{lo} {hi}\n', capture_output=True, text=True, check=True)
    return r.stdout

def main():
    files, opts, jobs, rand, seed, only, split, xc = [], [], 4, 0, 1, None, None, None
    argv = sys.argv[1:]; i = 0
    while i < len(argv):
        a = argv[i]
        if a.startswith('--jobs='): jobs = int(a[7:])
        elif a.startswith('--rand='): rand = int(a[7:])
        elif a.startswith('--seed='): seed = int(a[7:])
        elif a.startswith('--only='): only = set(int(x) for x in a[7:].split(','))
        elif a.startswith('--split='): split = int(a[8:])
        elif a.startswith('--xcheck='): xc = a[9:]
        elif a in ('-x', '-r', '-S', '-Px', '-Gx', '-Bx'): opts += [a, argv[i + 1]]; i += 1
        elif a.startswith('-'): opts.append(a)
        else: files.append(a)
        i += 1
    b = binary()
    for f in files:
        data = json.load(gzip.open(f, 'rt'))
        cores = data['cores'] if isinstance(data, dict) else data
        tasks = []
        for ci, core in enumerate(cores):
            if only is not None and ci not in only: continue
            inp, sizes = core_input(core)
            prof = 1
            for s in sizes: prof *= s
            ro = ['-r', str(rand), '-S', str(seed * 1000003 + ci)] if rand else []
            k = 1 if rand else (split if split else (4 if prof >= 10**6 else 1))
            k = min(k, sizes[0])
            for p in range(k):
                lo, hi = sizes[0] * p // k, sizes[0] * (p + 1) // k
                tasks.append((ci, ([b] + opts + ro + (['-X'] if xc else []), inp, lo, hi)))
                if xc: tasks.append((ci, ([xc, '-R', '-p', '6'] + (['-r', str(rand), '-S', str(seed * 1000003 + ci)] if rand else []), inp, lo, hi)))
        tot, kinds, fo = {}, {}, None
        mism = nx = 0
        with ThreadPoolExecutor(jobs) as ex:
            outs = list(ex.map(run, [t for _, t in tasks]))
        if xc:
            for q in range(0, len(outs), 2):
                a = [l for l in outs[q].splitlines() if l.startswith('X ')]
                c = [l for l in outs[q + 1].splitlines() if l.startswith('X ')]
                nx += len(a)
                if a != c:
                    mism += 1 + (len(a) != len(c))
                    for la, lc in zip(a, c):
                        if la != lc: print(f'core {tasks[q][0]}: MISMATCH hall: {la} | c4x: {lc}'); break
            outs = outs[0::2]
            tasks = tasks[0::2]
        for (ci, _), out in zip(tasks, outs):
            for line in out.splitlines():
                w = line.split()
                if line.startswith('RESULT'):
                    for key, v in zip(w[1::2], w[2::2]): tot[key] = tot.get(key, 0) + int(v)
                elif line.startswith('FAILOWNERS'):
                    nums = [int(x) for x in w[1:2] + w[3:4] + w[5:13] + w[14:22]]
                    fo = [a + b for a, b in zip(fo, nums)] if fo else nums
                elif line.startswith('BTX'):
                    cur = tot.setdefault('_btx', [0] * 6)
                    for q, v in enumerate(w[1:7]): cur[q] += int(v)
                elif line.startswith('BTC'):
                    cur = tot.setdefault('_btc', [0] * 3)
                    for q, v in enumerate(w[1:4]): cur[q] += int(v)
                elif line.startswith('FZ'):
                    cur = tot.setdefault('_fz', [0] * 15)
                    for q, v in enumerate(w[1:16]): cur[q] += int(v)
                elif line.startswith('G0'):
                    cur = tot.setdefault('_g0', [0] * 8)
                    for q, v in enumerate(w[1:9]): cur[q] += int(v)
                elif line.startswith('F0'):
                    cur = tot.setdefault('_f0', [0] * 15)
                    for q, v in enumerate(w[1:16]): cur[q] += int(v)
                elif line.startswith('PARETO'):
                    key = 'pareto F=' + w[2]
                    cur = tot.setdefault(key, [0, 0, 0, 0])
                    for q, v in enumerate((w[4], w[6], w[8], w[10])): cur[q] += int(v)
                elif line.startswith('KIND'):
                    k = int(w[1]); name = ' '.join(w[10:])
                    cur = kinds.get(k, [name, 0, 0, 0, 0])
                    kinds[k] = [name, cur[1] + int(w[3]), cur[2] + int(w[5].strip('()')), cur[3] + int(w[7]), cur[4] + int(w[9].strip('()'))]
                elif line.startswith('EX') or line.startswith('P ') or line.startswith('V'):
                    print(f'core {ci}: {line}')
        par = {k: tot.pop(k) for k in list(tot) if k.startswith('pareto')}
        f0 = tot.pop('_f0', None)
        g0 = tot.pop('_g0', None)
        fz = tot.pop('_fz', None)
        btc = tot.pop('_btc', None)
        btx = tot.pop('_btx', None)
        print(f'FILE {f} cores {len(set(ci for ci, _ in tasks))} ' + ' '.join(f'{k} {v}' for k, v in tot.items()))
        for k, v in par.items():
            if v[0]: print(f'  Pareto-maxima inside the min-frozen set, {k}: profiles {v[0]}, every maximum deficit <= 0: {v[1]}, some: {v[2]} ({v[3]} maxima)')
        if f0:
            names = ['F=0 Pareto-maxima with omega>=1', 'Lemma U violated', 'Lemma U2 violated', 'no single-good holder', 'exposure of another kind',
                     'label criterion != exact test', 'a single-good holder valid', 'a pair-holder valid', 'no valid owner', 'every single-good holder valid',
                     'single-good holder invalid by an unhittable exposure', 'e2 exposures', 'e1 exposures', 'e3 exposures', 'e2 exposures at single-good owners']
            print('  F0: ' + ', '.join(f'{a} {b}' for a, b in zip(names, f0)))
        if btx:
            print(f'  BTX: non-completable Pareto-maxima with frozen agents {btx[0]}, with a frozen big-top agent {btx[1]}, with an exposed frozen big-top agent {btx[2]}, with an exchange cycle through a frozen big-top agent x after which x is a valid owner {btx[3]}, after which some owner is valid {btx[4]}; some cycle through any exposed frozen agent completes {btx[5]}')
        if btc and btc[0]:
            print(f'  BTC: profiles with a non-completable Pareto-maximum with frozen agents {btc[0]}, with a completable min-frozen pre-allocation whose owner is of big-top type {btc[1]}, with any completable min-frozen pre-allocation {btc[2]}')
        if fz:
            names = ['maxima with F>=1 and omega>=1', 'with a globally exposed frozen agent', 'global exposure of another shape', 'no global exposure and no valid owner',
                     'global exposure and no valid owner', 'Lemma H6 violations', 'frozen agents exposed w.r.t. >= 2 owners', 'some owner valid', 'no valid owner and no G1 configuration', 'no valid owner and no frozen big-top agent',
                     'frozen exposures (agent, owner): global', '... owner a chain end of x (G1-type)', '... local, one label', '... local, two labels', '... local, unhittable']
            print('  FZ: ' + ', '.join(f'{a} {b}' for a, b in zip(names, fz)))
        if g0:
            names = ['F=0 P with U, U2, omega>=1 and no valid owner', 'agent exposed w.r.t. two owners', 'owner exposing nobody', 'T>=2',
                     'exposure map not a bijection', 'rotation rule: valid Pareto improvement', 'rotation rule fails', '... for want of labels']
            print('  G0: ' + ', '.join(f'{a} {b}' for a, b in zip(names, g0)))
        if xc: print(f'  XCHECK profiles {nx} mismatching task pairs {mism}')
        if fo:
            print(f'  failing (P, owner) pairs {fo[0]}, with an unhittable exposed agent {fo[1]}; tau for the others: {fo[2:10]}; minimal violator size (0 = none of size < 8): {fo[10:18]}')
        for k in sorted(kinds):
            name, a, b2, c, dd = kinds[k]
            if a or c: print(f'  exposed at failing owners, {name}: free {a} (unhittable {b2}), frozen {c} (unhittable {dd})')
        sys.stdout.flush()

if __name__ == '__main__':
    main()
