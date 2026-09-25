#!/usr/bin/env python3
"""Driver for the exhaustive mode of k4/c4min_hunt.c (k4/c4min_hunt.md §2): every strict profile of every core of
certificate files (the core lists of K4.R3-R6a), in parallel.

For each core the agents are reordered so that one with the most types is last (the vectorized agent of c4min_hunt.c)
and the others by increasing number of types (--order=big: one with the most types first, the pure n = 4 run of the
first version); the work is split by the first agent's type. c4min_hunt.c runs with -B 8 (--best=K to change). Prints, per file, the totals of c4min_hunt.c's counters and every
FAIL line (a profile where no min-frozen pre-allocation has deficit <= 0; the line lists types and values, goods by
their global index in the core), and appends per-core lines to a checkpoint (--ckpt) so an interrupted run resumes.

usage: c4min_hunt_run.py FILE [--jobs=4] [--split=K] [--only=I,J] [--from=I] [--to=I] [--ckpt=PATH] [--order=small|big]
       [--best=K] [-w0] [-V]"""
import json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
import c4min_common as cc


def run(args):
    b, inp, lo, hi, opts = args
    t = time.time()
    r = subprocess.run([b, '-E', *opts], input=f'{inp}{lo} {hi}\n', capture_output=True, text=True)
    if r.returncode != 0: raise RuntimeError(f'c4min_hunt exit {r.returncode}: {r.stdout[-2000:]} {r.stderr[-2000:]}')
    return r.stdout, time.time() - t


def main():
    files, jobs, split, only, lo_c, hi_c, ckpt, opts, order_mode = [], 4, None, None, 0, None, None, ['-B', '8'], 'small'
    for a in sys.argv[1:]:
        if a.startswith('--jobs='): jobs = int(a[7:])
        elif a.startswith('--split='): split = int(a[8:])
        elif a.startswith('--only='): only = set(int(x) for x in a[7:].split(','))
        elif a.startswith('--from='): lo_c = int(a[7:])
        elif a.startswith('--to='): hi_c = int(a[5:])
        elif a.startswith('--ckpt='): ckpt = a[7:]
        elif a in ('-w0', '-V'): opts.append(a)
        elif a.startswith('--order='): order_mode = a[8:]
        elif a.startswith('--best='): opts[opts.index('-B') + 1] = a[7:]
        else: files.append(a)
    b = cc.hunt_binary()
    done = {}
    if ckpt and os.path.exists(ckpt):
        for line in open(ckpt):
            rec = json.loads(line); done[(rec['file'], rec['core'])] = rec
    for f in files:
        cores = cc.load_cores(f)
        tasks = []
        for ci, c in enumerate(cores):
            if only is not None and ci not in only: continue
            if ci < lo_c or (hi_c is not None and ci >= hi_c): continue
            if (f, ci) in done: continue
            doms = cc.domains(c['sets'], c['m'])
            sizes = [len(D) for D in doms]
            n = len(c['sets'])
            last = max(range(n), key=lambda i: (sizes[i], i))
            rest = [i for i in range(n) if i != last]
            if order_mode == 'big':
                first = max(rest, key=lambda i: (sizes[i], -i))
                order = [first] + [i for i in rest if i != first] + [last]
            else:                                  # agents with the fewest types outermost (faster for n = 5)
                order = sorted(rest, key=lambda i: (sizes[i], i)) + [last]
            inp = cc.input_all(c['sets'], c['m'], doms, order)
            prof = 1
            for s in sizes: prof *= s
            k = split if split else max(1, min(sizes[order[0]], prof // (5 * 10 ** 9) + 1))
            k = min(k, sizes[order[0]])
            for p in range(k):
                lo, hi = sizes[order[0]] * p // k, sizes[order[0]] * (p + 1) // k
                tasks.append((ci, order, (b, inp, lo, hi, opts)))
        per = {}
        tot = {}
        fails = 0
        with ThreadPoolExecutor(jobs) as ex:
            futs = [(ci, order, ex.submit(run, t)) for ci, order, t in tasks]
            ncore_tasks = {}
            for ci, _, _ in futs: ncore_tasks[ci] = ncore_tasks.get(ci, 0) + 1
            for ci, order, fu in futs:
                out, dt = fu.result()
                rec = per.setdefault(ci, {'file': f, 'core': ci, 'order': order, 'secs': 0.0, 'faillines': []})
                rec['secs'] += dt
                for line in out.splitlines():
                    if line.startswith('FAIL') or line.startswith('MISMATCH'):
                        print(f'core {ci} (agent order {order}): {line}', flush=True)
                        rec['faillines'].append(line); fails += 1
                    elif line.startswith('RESULT'):
                        w = line.split()
                        for key, val in zip(w[1:13:2], w[2:13:2]):
                            rec[key] = rec.get(key, 0) + int(val); tot[key] = tot.get(key, 0) + int(val)
                        fs = [int(x) for x in w[w.index('fstar_solved') + 1:]]
                        rec['fstar_solved'] = [a + b2 for a, b2 in zip(rec.get('fstar_solved', [0] * len(fs)), fs)]
                ncore_tasks[ci] -= 1
                if ncore_tasks[ci] == 0:
                    if ckpt:
                        with open(ckpt, 'a') as fh: fh.write(json.dumps(per[ci]) + '\n')
                    print(f'core {ci} m {cores[ci]["m"]} profiles {per[ci].get("profiles", 0)} fails {len(per[ci]["faillines"])} '
                          f'solved {per[ci].get("solved", 0)} secs {per[ci]["secs"]:.1f}', flush=True)
        for (ff, ci), rec in done.items():
            if ff != f: continue
            if only is not None and ci not in only: continue
            for key in ('profiles', 'solved', 'templates', 'cachehits', 'fails', 'verified'):
                tot[key] = tot.get(key, 0) + rec.get(key, 0)
            fails += len(rec['faillines'])
        print(f'FILE {f} cores {len(set(ci for ci, _, _ in tasks)) + sum(1 for (ff, _) in done if ff == f)} '
              + ' '.join(f'{k} {v}' for k, v in tot.items()) + f' faillines {fails}', flush=True)


if __name__ == '__main__':
    main()
